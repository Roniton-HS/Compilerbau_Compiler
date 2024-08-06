import ast
from _ast import If, stmt
from ast import *
from typing import List, Any

from x86_ast import *
from utils import *
from graph import *
from dataflow_analysis import analyze_dataflow
import compiler_register_allocator
from compiler_register_allocator import get_loc_from_arg, caller_saved_registers, registers_for_coloring
import copy

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


def get_op_str(op: cmpop) -> str:
    name: str

    match op:
        case Lt():
            name = "l"
        case LtE():
            name = "le"
        case Gt():
            name = "g"
        case GtE():
            name = "ge"
        case Eq():
            name = "e"
        case NotEq():
            name = "ne"

    return name


class Compiler(compiler_register_allocator.Compiler):
    def __init__(self):
        super().__init__()
        self.stack_size = 0

    ###########################################################################
    # Shrink
    ###########################################################################

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case BoolOp(And(), values):
                e1 = self.shrink_exp(values[0])
                e2 = self.shrink_exp(values[1])
                return IfExp(e1, e2, Constant(False))
            case BoolOp(Or(), values):
                e1 = self.shrink_exp(values[0])
                e2 = self.shrink_exp(values[1])
                return IfExp(e1, Constant(True), e2)
            case UnaryOp(Not(), operand):
                return UnaryOp(Not(), self.shrink_exp(operand))
            case Compare(left, [op], [right]):
                left = self.shrink_exp(left)
                right = self.shrink_exp(right)
                return Compare(left, [op], [right])
            case IfExp(test, body, orelse):
                test = self.shrink_exp(test)
                body = self.shrink_exp(body)
                orelse = self.shrink_exp(orelse)
                return IfExp(test, body, orelse)
            case BinOp(left, op, right):
                left = self.shrink_exp(left)
                right = self.shrink_exp(right)
                return BinOp(left, op, right)
            case UnaryOp(op, operand):
                operand = self.shrink_exp(operand)
                return UnaryOp(op, operand)
            case _:
                return e

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign([Name(var)], value):
                return Assign([Name(var)], self.shrink_exp(value))
            case Expr(Call(Name("print"), [arg])):
                return Expr(Call(Name("print"), [self.shrink_exp(arg)]))
            case Expr(value):
                return Expr(self.shrink_exp(value))
            case If(test, body, orelse):
                return If(self.shrink_exp(test), [self.shrink_stmt(s) for s in body],
                          [self.shrink_stmt(s) for s in orelse])
            case While(test, body, orelse):
                return While(self.shrink_exp(test), [self.shrink_stmt(s) for s in body],
                             [self.shrink_stmt(s) for s in orelse])
            case _:
                return s

    def shrink(self, p: Module) -> Module:
        for i, stmt in enumerate(p.body):
            p.body[i] = self.shrink_stmt(stmt)
        return p

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        if need_atomic:
            match e:
                case Compare(left, [op], [right]):
                    tmp = Name(get_fresh_tmp())
                    left, left_tmps = self.rco_exp(left, True)
                    right, right_tmps = self.rco_exp(right, True)
                    return tmp, [(tmp, Compare(left, [op], [right]))] + left_tmps + right_tmps
                case IfExp(test, body, orelse):
                    tmp = Name(get_fresh_tmp())

                    test, test_tmps = self.rco_exp(test, False)
                    if len(test_tmps) > 0:
                        test = Begin([Assign([tmp[0]], tmp[1]) for tmp in test_tmps], test)

                    body, body_tmps = self.rco_exp(body, need_atomic)
                    if len(body_tmps) > 0:
                        body = Begin([Assign([tmp[0]], tmp[1]) for tmp in body_tmps], body)

                    orelse, orelse_tmps = self.rco_exp(orelse, need_atomic)
                    if len(orelse_tmps) > 0:
                        orelse = Begin([Assign([tmp[0]], tmp[1]) for tmp in orelse_tmps], orelse)

                    return tmp, [(tmp, IfExp(test, body, orelse))]
                case Begin(body, result):
                    tmp = Name(get_fresh_tmp())
                    body = [self.rco_stmt(s) for s in body]
                    result, result_tmps = self.rco_exp(result, need_atomic)
                    return tmp, [(tmp, Begin(body, result))] + result_tmps
                case Call(Name("input"), []):
                    tmp = Name(get_fresh_tmp())
                    return (tmp, [(tmp, e)])
                case _:
                    return super().rco_exp(e, need_atomic)
        else:
            match e:
                case Compare(left, [op], [right]):
                    left, left_tmps = self.rco_exp(left, True)
                    right, right_tmps = self.rco_exp(right, True)
                    return Compare(left, [op], [right]), left_tmps + right_tmps
                case IfExp(test, body, orelse):
                    test, test_tmps = self.rco_exp(test, False)
                    if len(test_tmps) > 0:
                        test = Begin([Assign([tmp[0]], tmp[1]) for tmp in test_tmps], test)

                    body, body_tmps = self.rco_exp(body, need_atomic)
                    if len(body_tmps) > 0:
                        body = Begin([Assign([tmp[0]], tmp[1]) for tmp in body_tmps], body)

                    orelse, orelse_tmps = self.rco_exp(orelse, need_atomic)
                    if len(orelse_tmps) > 0:
                        orelse = Begin([Assign([tmp[0]], tmp[1]) for tmp in orelse_tmps], orelse)

                    return IfExp(test, body, orelse), []
                case Begin(body, result):
                    body = [self.rco_stmt(s) for s in body]
                    result, result_tmps = self.rco_exp(result, need_atomic)
                    return Begin(body, result), result_tmps
                case Call(Name("input"), []):
                    tmp = Name(get_fresh_tmp())
                    return (tmp, [(tmp, e)])
                case _:
                    return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> list[stmt]:
        temporaries: Temporaries = []

        match s:
            case If(test, body, orelse):
                test, temporaries = self.rco_exp(test, False)
                body = [item for s in body for item in self.rco_stmt(s)]
                orelse = [item for s in orelse for item in self.rco_stmt(s)]
                s = If(test, body, orelse)
                return [Assign([tmp[0]], tmp[1]) for tmp in temporaries] + [s]
            case While(test, body, orelse):
                test, temporaries = self.rco_exp(test, False)
                body = [item for s in body for item in self.rco_stmt(s)]
                orelse = [item for s in orelse for item in self.rco_stmt(s)]
                s = While(test, body, orelse)
                return [Assign([tmp[0]], tmp[1]) for tmp in temporaries] + [s]
            case _:
                return super().rco_stmt(s)

    ############################################################################
    # Explicate Control
    ############################################################################

    def explicate_effect(self, e, cont, basic_blocks) -> list[stmt]:
        match e:
            case IfExp(test, body, orelse):
                then_block = self.explicate_stmt(body, cont, basic_blocks)
                else_block = self.explicate_stmt(orelse, cont, basic_blocks)
                return self.explicate_pred(test, then_block, else_block, basic_blocks)
            case Call(func, args):
                # keep if side effects
                return [Expr(e)] + cont
            case Begin(body, result):
                new_cont = self.explicate_effect(result, cont, basic_blocks)
                for s in reversed(body):
                    new_cont = self.explicate_stmt(s, new_cont, basic_blocks)
                return new_cont
            case _:
                return cont

    def explicate_assign(self, rhs, lhs, cont, basic_blocks) -> list[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                # YOUR CODE HERE
                then_block = self.explicate_assign(body, lhs, cont, basic_blocks)
                else_block = self.explicate_assign(orelse, lhs, cont, basic_blocks)
                return self.explicate_pred(test, then_block, else_block, basic_blocks)
            case Begin(body, result):
                # YOUR CODE HERE
                new_cont = self.explicate_assign(result, lhs, cont, basic_blocks)
                for s in reversed(body):
                    new_cont = self.explicate_stmt(s, new_cont, basic_blocks)
                return new_cont
            case _:
                return [Assign([lhs], rhs)] + cont

    def explicate_pred(self, cnd, thn, els, basic_blocks) -> list[If] | list[stmt]:
        match cnd:
            case Compare(left, [op], [right]):
                return [If(
                    Compare(left, [op], [right]),
                    create_block(thn, basic_blocks),
                    create_block(els, basic_blocks))]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                # switch then and else
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case IfExp(test, body, orelse):
                then_block = self.explicate_pred(body, thn, els, basic_blocks)
                else_block = self.explicate_pred(orelse, thn, els, basic_blocks)
                return self.explicate_pred(test, then_block, else_block, basic_blocks)
            case Begin(body, result):
                new_cont = self.explicate_pred(result, thn, els, basic_blocks)
                for s in reversed(body):
                    new_cont = self.explicate_stmt(s, new_cont, basic_blocks)
                return new_cont
            case _:
                return [
                    If(
                        Compare(cnd, [Eq()], [Constant(False)]),
                        create_block(els, basic_blocks),
                        create_block(thn, basic_blocks),
                    )
                ]

    def explicate_stmt(self, s: stmt, cont, basic_blocks) -> list[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                # create block for after if statements
                after_if = create_block(cont, basic_blocks)

                then_block = self.process_body(body, after_if, basic_blocks)
                else_block = self.process_body(orelse, after_if, basic_blocks)
                return self.explicate_pred(test, then_block, else_block, basic_blocks)
            case While(test, body, []):
                goto_cont = create_block(cont, basic_blocks)

                label = label_name(generate_name('loop'))
                goto_loop = [Goto(label)]

                explicate_body = goto_loop
                for s in reversed(body):
                    explicate_body = self.explicate_stmt(
                        s, explicate_body, basic_blocks
                    )

                basic_blocks[label] = self.explicate_pred(
                    test, explicate_body, goto_cont, basic_blocks
                )

                return goto_loop

    def process_body(self, body: list[stmt], cont, basic_blocks) -> list[stmt]:
        new_cont = cont
        for s in reversed(body):
            new_cont = self.explicate_stmt(s, new_cont, basic_blocks)
        return new_cont

    def explicate_control(self, p: Module):
        basic_blocks = {}
        cont = []

        # iterate through statements in reversed order
        for s in reversed(p.body):
            cont = self.explicate_stmt(s, cont, basic_blocks)

        # create start block
        basic_blocks['start'] = cont

        # add return to last blocks
        for label, block in basic_blocks.items():
            if not block or not (isinstance(block[-1], (Goto, If, Return))):
                block.append(Return(Constant(0)))

        return CProgram(basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            # bool and int are the same type of constant
            case Constant(var):
                if var == True:
                    return Immediate(1)
                elif var == False:
                    return Immediate(0)
                else:
                    return Immediate(var)
            case [exp]:
                return self.select_arg(e[0])
            case _:
                return super().select_arg(e)

    def select_stmt(self, s: stmt) -> list[instr]:
        match s:
            case Assign([Name(var)], UnaryOp(Not(), atm)):
                if isinstance(atm, Name) and atm.id == var:
                    return [Instr("xorq", [Immediate(1), Variable(var)])]
                else:
                    return [Instr("movq", [self.select_arg(atm), Variable(var)]),
                            Instr("xorq", [Immediate(1), Variable(var)])]

            case Assign([Name(var)], Compare(atm1, op, atm2)):
                return [Instr("cmpq", [self.select_arg(atm2), self.select_arg(atm1)]),
                        Instr(get_op_str(op[0]), [ByteReg("al")]),
                        Instr("movzbg", [ByteReg("al"), Variable(var)])]

            case Goto(label):
                return [Jump(label)]

            case If(Compare(atm1, op, atm2), [Goto(label1)], [Goto(label2)]):
                return [
                    Instr("cmpq", [self.select_arg(atm2), self.select_arg(atm1)]),
                    JumpIf(get_op_str(op[0]), label1),
                    Jump(label2)
                ]

            case Return(exp):
                return [Instr("movq", [self.select_arg(exp), Reg("rax")]),
                        Jump("conclusion")]

            case _:
                return super().select_stmt(s)

    def select_instructions(self, p: Module) -> X86Program:
        blocks: dict[str, list[Instr]] = {}

        for block_key, block_instructions in p.body.items():
            instructions = []
            for instr in block_instructions:
                instructions += self.select_stmt(instr)
            blocks[block_key] = instructions

        blocks["conclusion"] = []
        return X86Program(blocks)

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes(self, p: X86Program) -> X86Program:
        live_after = self.uncover_live_blocks(p.body)
        graph = self.build_interference(p, live_after)

        home = self.color_graph(graph, registers_for_coloring)

        for block_key, block_instructions in p.body.items():
            p.body[block_key] = self.assign_homes_instrs(block_instructions, home)

        return p

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> set[location]:
        match i:
            case Instr('movq', [s, d]) | Instr('movzbq', [s, d]):
                return get_loc_from_arg(s)
            case Instr('addq', [s, d]) | Instr('subq', [s, d]) | Instr('xorq', [s, d]):
                return get_loc_from_arg(s) | get_loc_from_arg(d)
            case Instr('cmpq', [s, d]):
                return get_loc_from_arg(s) | get_loc_from_arg(d)
            case Instr('negq', [d]):
                return get_loc_from_arg(d)
            case Instr('pushq', [d]):
                return get_loc_from_arg(d)
            case Callq(_, n):
                return set([Reg('rdi')]) if n == 1 else set()
            case _:
                return set()

    def write_vars(self, i: instr) -> set[location]:
        match i:
            case Instr('movq', [s, d]) | Instr('movzbq', [s, d]):
                return get_loc_from_arg(d)
            case Instr('addq', [s, d]) | Instr('subq', [s, d]) | Instr('xorq', [s, d]):
                return get_loc_from_arg(d)
            case Instr(op, [d]) if 'set' in op:
                return get_loc_from_arg(d)
            case Instr('negq', [d]) | Instr('pushq', [d]):
                return get_loc_from_arg(d)
            case Callq(_, n):
                return set([Reg('rax')])
            case _:
                return set()

    def control_flow_graph(
            self, basic_blocks: dict[str, list[instr]]
    ) -> DirectedAdjList:
        cfg = DirectedAdjList()

        for block_id, block_items in basic_blocks.items():
            for i in block_items:
                match i:
                    case Jump(label):
                        cfg.add_edge(block_id, label)
                    case JumpIf(_, label):
                        cfg.add_edge(block_id, label)

        return cfg

    def transfer(self, basic_blocks, block_id, l_after: set[location]):
        if block_id == 'conclusion':
            l_before = set([Reg('rax'), Reg('rsp')])
        else:
            l_before = set()

        for instr in reversed(basic_blocks[block_id]):
            self.instr_to_lafter[instr] = l_after
            l_before = (l_after - self.write_vars(instr)) | self.read_vars(instr)
            l_after = l_before

        self.block_to_lafter[block_id] = l_after
        return l_before

    def uncover_live_blocks(self, basic_blocks) -> dict[instr, set[location]]:
        cfg = self.control_flow_graph(basic_blocks)

        self.block_to_lafter = {}
        self.instr_to_lafter = {}

        analyze_dataflow(
            transpose(cfg),
            lambda label, l_after: self.transfer(basic_blocks, label, l_after),
            set(),
            lambda a, b: a.union(b),
        )

        return self.instr_to_lafter

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(
            self, p: X86Program, live_blocks
    ) -> UndirectedAdjList:
        graph = UndirectedAdjList(vertex_label=label)

        for (_, vs) in live_blocks.items():
            for v in vs:
                graph.add_vertex(v)

        for _, instrs in p.body.items():
            for instr in instrs:
                l_after = live_blocks[instr]

                match instr:
                    case Instr('movq', [s, d]) | Instr('movzbq', [s, d]):
                        for v in l_after:
                            if v != s and v != d and not graph.has_edge(v, d):
                                graph.add_edge(v, d)
                    case Callq(_, n):
                        for v in l_after:
                            for v2 in caller_saved_registers:
                                if v != v2 and not graph.has_edge(v, v2):
                                    graph.add_edge(v, v2)
                    case _:
                        for v in l_after:
                            for d in self.write_vars(instr):
                                if v != d and not graph.has_edge(v, d):
                                    graph.add_edge(v, d)
        return graph

    ###########################################################################
    # Patch Instructions
    ###########################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        # YOUR CODE HERE
        match i:
            case Instr("movzbq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                tmp = Reg("rax")
                return [
                    Instr("movzbq", [Deref(reg1, offset1), tmp]),
                    Instr("movq", [tmp, Deref(reg2, offset2)])
                ]
            case Instr("cmpq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                tmp = Reg("rax")
                return [
                    Instr("movq", [Deref(reg1, offset1), tmp]),
                    Instr("cmpq", [tmp, Deref(reg2, offset2)])
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
        for label, instrs in p.body.items():
            p.body[label] = self.patch_instrs(instrs)
        return p

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        conclusion = []
        prelude = [
            Instr("pushq", [Reg("rbp")]),
            Instr("movq", [Reg("rsp"), Reg("rbp")]),
        ]

        # stack dividable by 16?
        if self.stack_offset % 16 != 0:
            self.alloc()

        prelude.append((Instr('subq', [Immediate(self.stack_offset), Reg('rsp')])))
        prelude.append(Jump("start"))
        conclusion.insert(0, Instr('addq', [Immediate(self.stack_offset), Reg('rsp')]))

        conclusion.extend([
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ])

        # combine in one dictonary
        p.body = {
            "main": prelude,
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
