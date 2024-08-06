from ast import *
from x86_ast import *
import x86_ast
from graph import *
from utils import *
from dataflow_analysis import analyze_dataflow
import copy
import type_check_Ltup
import type_check_Ctup
import compiler_conditionals

Binding = tuple[Name, expr]
Temporaries = list[Binding]

get_fresh_tmp = lambda: generate_name('tmp')
label = lambda v: v.id if isinstance(v, Reg) else str(v)


def create_block(stmts, basic_blocks):
    match stmts:
        case [Goto(l)]:
            return stmts
        case _:
            label = label_name(generate_name('block'))
            basic_blocks[label] = stmts
            return [Goto(label)]


def create_tag(types: list[Type]) -> int:
    tag = len(types) << 1
    tag |= 1

    l = 7
    for t in types:
        if isinstance(t, TupleType):
            tag |= 1 << l
        l += 1

    return tag
    

class Compiler(compiler_conditionals.Compiler):
    def __init__(self):
        super().__init__()
        self.rootstack_size: int = 0
        self.rootstack_offset: int = 0
        self.var_types: dict[Variable, Type] = {}

    ###########################################################################
    # Shrink
    ###########################################################################

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case Tuple(els, Load()):
                nels = [self.shrink_exp(e) for e in els]
                return Tuple(self.shrink_exp(nels), Load())
            case Subscript(lhs, Constant(idx), Load()):
                return Subscript(self.shrink_exp(lhs), Constant(idx), Load())
            case Call(Name('len'), [exp]):
                return Call(Name('len'), [self.shrink_exp(exp)])
            case _:
                return super().shrink_exp(e)

    ###########################################################################
    # Expose Allocation
    ###########################################################################

    def expose_exp(self, e: expr) -> expr:
        # YOUR CODE HERE
        match e:
            case Tuple(els, _):
                nels = [self.expose_exp(e) for e in els]
                init_list = []
                alloc_list = []
                # Speicherplatz eines Tupels
                n = 8 + len(els) * 8

                alloc_var = Name(generate_name('alloc'))
                alloc_list.append(Assign([alloc_var], Allocate(len(els), e.has_type)))

                for index, el in enumerate(nels):
                    new_init = Name(generate_name('init'))
                    init_list.append(Assign([new_init], el))
                    alloc_list.append(Assign([Subscript(alloc_var, Constant(index), Store())], new_init))

                stmts = (
                        init_list +
                        [If(Compare(BinOp(GlobalValue('free_ptr'), Add(), Constant(n)), [Lt()],
                                    [GlobalValue('fromspace_end')]),
                            [Expr(Constant(0))],
                            [Collect(n)]
                            )]
                        + alloc_list
                )

                return Begin(stmts, alloc_var)
            case _:
                return e

    def expose_stmt(self, s: stmt) -> stmt:
        # YOUR CODE HERE
        match s:
            case While(test, body, orelse):
                return While(
                    self.expose_exp(test), 
                    [self.expose_stmt(s) for s in body], 
                    [self.expose_stmt(s) for s in orelse]
                )
            case If(test, thn, els):
                return If(
                    self.expose_exp(test),
                    [self.expose_stmt(s) for s in thn],
                    [self.expose_stmt(s) for s in els]
                )
            case Assign([lhs], rhs):
                return Assign([lhs], self.expose_exp(rhs))
            case Expr(e):
                return Expr(self.expose_exp(e))
            case _:
                return s

    def expose_allocation(self, p: Module) -> Module:
        # YOUR CODE HERE
        type_check_Ltup.TypeCheckLtup().type_check(p)
        return Module([self.expose_stmt(s) for s in p.body])

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case Tuple(els, Load()):
                nels = [self.rco_exp(e, True) for e in els]
                return Tuple([exp for exp, _ in nels], Load()), [item for temps in nels for item in temps]

        if need_atomic:
            match e:
                case Subscript(lhs, idx, Load()):
                    tmp = Name(get_fresh_tmp())
                    lhs, lhs_tmp = self.rco_exp(lhs, True)
                    idx, idx_tmp = self.rco_exp(idx, True)
                    return tmp, idx_tmp + lhs_tmp + [(tmp, Subscript(lhs, idx, Load()))]
                case Call(Name("len"), [atm]):
                    tmp = Name(get_fresh_tmp())
                    atm, atm_tmp = self.rco_exp(atm, True)
                    return tmp, atm_tmp + [(tmp, Call(Name("len"), [atm]))]
                case Allocate(size, typ):
                    tmp = Name(get_fresh_tmp())
                    return tmp, [(tmp, Allocate(size, typ))]
                case GlobalValue(var):
                    tmp = Name(get_fresh_tmp())
                    return tmp, [(tmp, GlobalValue(var))]
                case Begin(stmts, exp):
                    tmp = Name(get_fresh_tmp())
                    exp, exp_tmp = self.rco_exp(exp, False)
                    stmts = [item for stmt in stmts for item in self.rco_stmt(stmt)] + [Assign([var], val) for var, val
                                                                                        in exp_tmp]
                    return tmp, [(tmp, Begin(stmts, exp))]
                case _:
                    return super().rco_exp(e, need_atomic)
        else:
            match e:
                case Subscript(lhs, idx, Load()):
                    lhs, lhs_tmp = self.rco_exp(lhs, True)
                    idx, idx_tmp = self.rco_exp(idx, True)
                    return Subscript(lhs, idx, Load()), idx_tmp + lhs_tmp
                case Call(Name("len"), [atm]):
                    atm, atm_tmp = self.rco_exp(atm, True)
                    return Call(Name("len"), [atm]), atm_tmp
                case Allocate(size, typ):
                    return Allocate(size, typ), []
                case GlobalValue(var):
                    return GlobalValue(var), []
                case Begin(stmts, exp):
                    exp, exp_tmp = self.rco_exp(exp, False)
                    stmts = [item for stmt in stmts for item in self.rco_stmt(stmt)] + [Assign([var], val) for var, val
                                                                                        in exp_tmp]
                    return Begin(stmts, exp), []
                case _:
                    return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> list[stmt]:
        match s:
            case Assign([Subscript(lhs, idx, Store())], rhs):
                lhs, lhs_tmp = self.rco_exp(lhs, True)
                idx, idx_tmp = self.rco_exp(idx, True)
                rhs, rhs_tmp = self.rco_exp(rhs, True)
                temps = lhs_tmp + idx_tmp + rhs_tmp
                return [Assign([var], val) for var, val in temps] + [Assign([Subscript(lhs, idx, Store())], rhs)]
            case _:
                return super().rco_stmt(s)

    ############################################################################
    # Explicate Control
    ############################################################################

    def explicate_effect(self, e, cont, basic_blocks) -> list[stmt]:
        match e:
            case Allocate(_, _) | GlobalValue(_) | Call(Name('len'), _):
                return [Expr(e)] + cont
            case _:
                return super().explicate_effect(e, cont, basic_blocks)

    def explicate_assign(self, rhs, lhs, cont, basic_blocks) -> list[stmt]:
        match rhs:
            case Subscript(_, _, _) | Allocate(_, _) | GlobalValue(_) | Call(Name('len'), _):
                return [Assign([lhs], rhs)] + cont
            case _:
                return super().explicate_assign(rhs, lhs, cont, basic_blocks)

    def explicate_stmt(self, s: stmt, cont, basic_blocks) -> list[stmt]:
        match s:
            case Collect(val):
                return [Collect(val)] + cont
            case _:
                return super().explicate_stmt(s, cont, basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            case GlobalValue(var):
                return x86_ast.Global(var)
            case _:
                return super().select_arg(e)

    def select_assign(self, s: stmt) -> list[instr]:
        # YOUR CODE HERE
        match s:
            case Assign([lhs], Allocate(len, TupleType(types))):
                tmp_reg = Reg("r11")
                len_size = 8 * (len + 1)
                tag = create_tag(types)
                return [
                    Instr("movq", [x86_ast.Global("free_ptr"), tmp_reg]),
                    Instr("addq", [Immediate(len_size), x86_ast.Global("free_ptr")]),
                    Instr("movq", [Immediate(tag), Deref(tmp_reg.id, 0)]),
                    Instr("movq", [tmp_reg, self.select_arg(lhs)])
                ]
            case Assign([lhs], Subscript(tup, idx, Load())):
                tmp_reg = Reg("r11")
                idx_val = (idx.value + 1) * 8
                return [
                    Instr("movq", [self.select_arg(tup), tmp_reg]),
                    Instr("movq", [Deref(tmp_reg.id, idx_val), self.select_arg(lhs)])
                ]
            case Assign([Subscript(tup, idx, Store())], rhs):
                tmp_reg = Reg("r11")
                idx_val = (idx.value + 1) * 8
                return [
                    Instr("movq", [self.select_arg(tup), tmp_reg]),
                    Instr("movq", [self.select_arg(rhs), Deref(tmp_reg.id, idx_val)])
                ]
            case Assign([lhs], Call(Name("len"), [tup])): # print(len(tup))
                tmp_reg = Reg("r11")
                return [
                    Instr("movq", [self.select_arg(tup), tmp_reg]),
                    Instr("movq", [Deref(tmp_reg.id, 0), tmp_reg]),
                    Instr("andq", [Immediate(0x7E), tmp_reg]),                  # 0x7E = 0111 1110
                    Instr("sarq", [Immediate(1), tmp_reg]),
                    Instr("movq", [tmp_reg, self.select_arg(lhs)])
                ]
            case _:
                return super().select_stmt(s)

    def select_stmt(self, s: stmt) -> list[instr]:
        match s:
            case Collect(bytes):
                return [Instr("movq", [Reg("r15"), Reg("rdi")]),
                        Instr("movq", [Immediate(bytes), Reg("rsi")]),
                        Callq("collect", 0)]
            case Assign([lhs], rhs):
                return self.select_assign(s)
            case _:
                return super().select_stmt(s)

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        type_check_Ctup.TypeCheckCtup().type_check(p)
        self.var_types = p.var_types

        new_body = super().select_instructions(p).body

        ### dummy prelude
        ### this is needed to make interp_x86 work for using run-tests!
        prelude = []
        prelude.append(Instr('movq', [Immediate(16384), Reg('rdi')]))
        prelude.append(Instr('movq', [Immediate(16384), Reg('rsi')]))
        prelude.append(Callq('initialize', 2))
        prelude.append(Instr('movq', [x86_ast.Global('rootstack_begin'), Reg('r15')]))
        prelude.append(Instr('movq', [Immediate(0), Deref('r15', 0)]))
        prelude.append(Jump('start'))
        new_body['main'] = prelude
        ###

        return X86Program(new_body)

    ############################################################################
    # Assign Homes
    ############################################################################
    
    # allocate space on the rootstack
    def alloc_tuple(self) -> arg:
        # alloc on stack
        self.rootstack_size += 1
        self.rootstack_offset -= 8
        return Deref('r15', self.rootstack_offset)

    # assign every tuple to the rootstack
    # precoloured tuples should be reassigned to the rootstack since it checks for tuples first 
    # and looks into the dictionary if it isn't a tuple
    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        if isinstance(a, Variable) and isinstance(self.var_types[a.id], TupleType):
            h = self.alloc_tuple()
            home[a] = h
            return h
        else:
            return super().assign_homes_arg(a, home)

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        dummy_prelude = p.body['main']
        conclusion = []
        prelude = [
            Instr("pushq", [Reg("rbp")]),
            Instr("movq", [Reg("rsp"), Reg("rbp")]),
        ]

        # push and pop registers used for colouring non spilled variables 
        for i in self.used_callees:
            prelude.append(Instr('pushq', [i]))
            conclusion.insert(0, Instr('popq', [i]))
            self.alloc()

        # stack dividable by 16?
        if self.stack_offset % 16 != 0:
            self.alloc()

        prelude.append(Instr('subq', [Immediate(abs(self.stack_offset)), Reg('rsp')]))
        # the dummy prelude is used instead
        # prepare initialize
        #prelude.append(Instr('movq', [Immediate(16384), Reg('rdi')]))
        #prelude.append(Instr('movq', [Immediate(16384), Reg('rsi')]))
        # call initialize
        #prelude.append(Callq('Initialize', 2))
        # move rootstack_being to register r15
        #prelude.append(Instr('movq', [x86_ast.Global('rootstack_begin'), Reg('r15')]))
        # initialize space for tuple on the rootstack
        dummy_prelude = dummy_prelude[:-1]
        prelude += dummy_prelude
        for i in range(self.rootstack_size):
            prelude.append(Instr('movq', [Immediate(0), Deref('r15', 8 * i)]))
        conclusion.insert(0, Instr('addq', [Immediate(abs(self.stack_offset)), Reg('rsp')]))

        if self.rootstack_offset != 0:
            prelude.append(Instr('addq', [Immediate(abs(self.rootstack_offset)), Reg('r15')]))
            conclusion.insert(0, Instr('subq', [Immediate(abs(self.rootstack_offset)), Reg('r15')]))
        
        prelude.append(Jump("start"))

        conclusion.extend([
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ])

        #combine in one dictonary
        p.body['main'] = prelude
        p.body = {
            **p.body,
            "conclusion": conclusion
        }

        return p

    ##################################################
    # Compiler
    ##################################################

    def compile(self, s: str, logging=False) -> X86Program:
        compiler_passes = {
            'shrink': self.shrink,
            'expose allocation': self.expose_allocation,
            'remove complex operands': self.remove_complex_operands,
            'explicate control': self.explicate_control,
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
