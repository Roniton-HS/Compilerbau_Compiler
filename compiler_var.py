from ast import *
from utils import *
from x86_ast import *

Binding = tuple[Name, expr]
Temporaries = list[Binding]

get_fresh_tmp = lambda: generate_name('tmp')


class Compiler:
    def __init__(self):
        self.stack_size = 0
        self.stack_offset = 0

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, needs_to_be_atomic: bool) -> tuple[expr, Temporaries]:
        
        match e:
            case Constant(int):
                return (e, [])
            case Name(var):
                return (e, [])
        
        if needs_to_be_atomic:
            match e:
                case UnaryOp(USub(), exp):
                    tmp = Name(get_fresh_tmp())
                    new_exp, tmps = self.rco_exp(exp, True)
                    return (tmp, tmps + [(tmp, UnaryOp(USub(), new_exp))])
                case BinOp(l, op, r):
                    tmp = Name(get_fresh_tmp())
                    new_l, l_tmps = self.rco_exp(l, True)
                    new_r, r_tmps = self.rco_exp(r, True)
                    return (tmp, l_tmps + r_tmps + [(tmp, BinOp(new_l, op, new_r))])
                case Call(Name("input_int"), []):
                    tmp = Name(get_fresh_tmp())
                    return (tmp, [(tmp, e)])
        else:
            match e:
                case UnaryOp(USub(), exp):
                    new_exp, tmps = self.rco_exp(exp, True)
                    return (UnaryOp(USub(), new_exp), tmps)
                case BinOp(l, op, r):
                    new_l, l_tmps = self.rco_exp(l, True)
                    new_r, r_tmps = self.rco_exp(r, True)
                    return (BinOp(new_l, op, new_r), l_tmps + r_tmps)
                case Call(Name("input_int"), []):
                    return (e, [])


    def rco_stmt(self, s: stmt) -> list[stmt]:
        temporaries: Temporaries = []

        match s:
            case Assign([Name(var)], exp):
                exp, temporaries = self.rco_exp(exp, False)
                s = Assign([Name(var)], exp)
            case Expr(Call(Name("print"), [exp])):
                exp, temporaries = self.rco_exp(exp, True)
                s = Expr(Call(Name("print"), [exp]))
            case Expr(exp):
                exp, temporaries = self.rco_exp(exp, False)
                s = Expr(exp)
        
        return [Assign([tmp[0]], tmp[1]) for tmp in temporaries] + [s]

    def remove_complex_operands(self, p: Module) -> Module:
        new_mod = Module([])

        for stmt in p.body:
            new_mod.body += self.rco_stmt(stmt)        

        return new_mod

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(int):
                return Immediate(int)
            case Name(var):
                return Variable(var)
            case _:
                pass

    def select_stmt(self, s: stmt) -> list[instr]:
        match s:
            case Assign([Name(var)], BinOp(atm1, op, atm2)):
                name: str
                match op:
                    case Add():
                        name = "addq"
                    case Sub():
                        name = "subq"

                if isinstance(atm1, Name) and atm1.id == var:
                    return [Instr(name, [self.select_arg(atm2), Variable(var)])]
                elif isinstance(atm2, Name) and atm2.id == var:
                    return [Instr(name, [self.select_arg(atm1), Variable(var)])]
                else:
                    return [Instr("movq", [self.select_arg(atm1), Variable(var)]),
                            Instr(name, [self.select_arg(atm2), Variable(var)])]

            case Assign([Name(var)], Call(Name("input_int"), [])):
                return [Callq("read_int", 0),
                        Instr("movq", [Reg("rax"), Variable(var)])]

            case Assign([Name(var)], UnaryOp(USub(), atm)):  # TODO improve uneccessary movq
                if isinstance(atm, Name) and atm.id == var:
                    return [Instr("negq", [Variable(var)])]
                else:
                    return [Instr("movq", [self.select_arg(atm), Variable(var)]),
                            Instr("negq", [Variable(var)])]

            case Assign([Name(var)], atm):
                return [Instr("movq", [self.select_arg(atm), Variable(var)])]

            case Expr(Call(Name("print"), [atm])):
                return [Instr("movq", [self.select_arg(atm), Reg("rdi")]),
                        Callq("print_int", 1)]

    def select_instructions(self, p: Module) -> X86Program:
        instructions: list[Instr] = []

        for stmt in p.body:
            instructions += self.select_stmt(stmt)

        return X86Program(instructions)

    ############################################################################
    # Assign Homes
    ############################################################################

    def alloc(self) -> arg:
        # alloc on stack
        self.stack_offset -= 8
        return Deref('rbp', self.stack_offset)

    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        if a in home:
            # arg already in home
            return home[a]
        if isinstance(a, Immediate) or isinstance(a, Reg):
            # do nothing because arg is immediate value or register
            return a
        else:
            # arg is variable
            h = self.alloc()
            home[a] = h
            return h

    def assign_homes_instr(self, i: instr, home: dict[Variable, arg]) -> instr:
        # replace arguments of given instruction
        match i:
            case Instr(name, args):
                new_args = []
                for a in args:
                    new_args.append(self.assign_homes_arg(a, home))
                return Instr(name, new_args)
            case _:
                return i

    def assign_homes_instrs(self, ss: list[instr], home: dict[Variable, arg]) -> list[instr]:
        # replace arguments for all instructions
        new_instr = []
        for i in ss:
            new_instr.append(self.assign_homes_instr(i, home))
        return new_instr

    def assign_homes(self, p: X86Program) -> X86Program:
        new_body = self.assign_homes_instrs(p.body, {})
        # stack dividable by 16?
        if self.stack_offset % 16 != 0:
            self.alloc()
        return X86Program(new_body)

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        # YOUR CODE HERE
        match i:
            case Instr('movq', [Deref(reg1, offset1), Deref(reg2, offset2)]):
                tmp = Reg('rax')
                return [
                    Instr('movq', [Deref(reg1, offset1), tmp]),
                    Instr('movq', [tmp, Deref(reg2, offset2)])
                ]
            case _:
                return [i]

    def patch_instrs(self, instrs: list[instr]) -> list[instr]:
        # YOUR CODE HERE
        patched_instrs = []
        for i in instrs:
            patched_instrs.extend(self.patch_instr(i))
        return patched_instrs

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        instructions = []
        for instr in p.body:
            instructions.append(instr)
        return X86Program(self.patch_instrs(instructions))

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        prelude = [
            Instr('pushq', [Reg('rbp')]),
            Instr('movq', [Reg('rsp'), Reg('rbp')]),
            Instr('subq', [Immediate(self.stack_offset), Reg('rsp')])
        ]
        conclusion = [
            Instr('addq', [Immediate(self.stack_offset), Reg('rsp')]),
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ]
        instructions: list[Instr] = []
        for instr in p.body:
            instructions.append(instr)
        return X86Program(prelude + instructions + conclusion)

    ##################################################
    # Compiler
    ##################################################

    def compile(self, s: str, logging=False) -> X86Program:
        compiler_passes = {
            'remove complex operands': self.remove_complex_operands,
            'select instructions': self.select_instructions,
            'assign homes': self.assign_homes,
            'patch instructions': self.patch_instructions,
            'prelude & conclusion': self.prelude_and_conclusion,
        }

        current_program = parse(s)

        if logging == True:
            print()
            print('==================================================')
            print(' Input program')
            print('==================================================')
            print()
            print(s)

        for pass_name, pass_fn in compiler_passes.items():
            current_program = pass_fn(current_program)

            if logging == True:
                print()
                print('==================================================')
                print(f' Output of pass: {pass_name}')
                print('==================================================')
                print()
                print(current_program)

        return current_program


##################################################
# Execute
##################################################

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                compiler = Compiler()
                x86_program = compiler.compile(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(str(x86_program))

            except:
                print(
                    'Error during compilation! **************************************************'
                )
                import traceback

                traceback.print_exception(*sys.exc_info())
