from _ast import stmt
from ast import *
from typing import Dict, List, Any

import compiler_tup
from x86_ast import *
import x86_ast
from graph import *
from utils import *
from dataflow_analysis import analyze_dataflow
import copy
import type_check_Lfun
import type_check_Cfun

Binding = tuple[Name, expr]
Temporaries = list[Binding]

get_fresh_tmp = lambda: generate_name('tmp')
label = lambda v: v.id if isinstance(v, Reg) else str(v)


class Compiler(compiler_tup.Compiler):

    ###########################################################################
    # Shrink
    ###########################################################################

    def shrink(self, p: Module) -> Module:
        # Sammle alle top-level statements und Funktionsdefinitionen
        stmts = []
        defs = []

        for node in p.body:
            if isinstance(node, FunctionDef):
                defs.append(node)
            else:
                stmts.append(node)

        # Erstelle die main-Funktion mit den top-level statements
        main_func = FunctionDef(
            name="main",
            args=arguments(
                args=[],
                vararg=None,
                kwonlyargs=[],
                kw_defaults=[],
                kwarg=None,
                defaults=[],
            ),
            body=stmts + [Return(Constant(0))],
            decorator_list=[],
            returns=Name(id="int", ctx=Load()),
            type_comment=None,
        )

        # Füge die main-Funktion zu den Funktionsdefinitionen hinzu
        new_body = defs + [main_func]

        for function in new_body:
            super().shrink(function)

        # Erzeuge ein neues Module-Objekt mit dem aktualisierten Body
        new_module = Module(body=new_body, type_ignores=p.type_ignores)

        return new_module

    ###########################################################################
    # Reveal Functions
    ###########################################################################

    def reveal_functions(self, p: Module) -> Module:
        type_check_Lfun.TypeCheckLfun().type_check(p)
        function_types = p.var_types

        def transform_node(node):
            match node:
                case Return(value):
                    return Return(transform_node(value))
                case Assign(target, value):
                    return Assign(target, transform_node(value))
                case Call(func, args):
                    return Call(transform_node(func), [transform_node(arg) for arg in args])
                case Name(name):
                    if name in function_types:
                        func_type = function_types[name]
                        if isinstance(func_type, type_check_Lfun.FunctionType):
                            arity = len(func_type.param_types)
                            return FunRef(name, arity)
                    return Name(name)
                case _:
                    return node

        def transform_body(body):
            new_body = []
            for fun in body:
                if isinstance(fun, FunctionDef):
                    fun.body = transform_body(fun.body)
                    new_body.append(fun)
                else:
                    new_body.append(transform_node(fun))
            return new_body

        p.body = transform_body(p.body)
        return p

    ###########################################################################
    # Limit Functions
    ###########################################################################

    # optional
    # def limit_functions(self, p: Module) -> Module:
    # YOUR CODE HERE
    # pass

    ###########################################################################
    # Expose Allocation
    ###########################################################################

    def expose_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, arguments_args, stmts, args, kwargs):
                return FunctionDef(name, arguments_args, self.expose_stmt(stmts), args, kwargs)
            case _:
                return super().expose_stmt(s)

    def expose_allocation(self, p: Module) -> Module:
        type_check_Lfun.TypeCheckLfun().type_check(p)
        return Module([self.expose_stmt(s) for s in p.body])

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool):
        temporaries: Temporaries = []

        match e:
            case FunRef(label, arity):
                pass
            case Call(func, args):
                func, func_tmp = self.rco_exp(func, True)
                args = [self.rco_exp(arg, True) for arg in args]
                temporaries = func_tmp + [item for _, temps in args for item in temps]
                e = Call(func, [arg for arg, _ in args])
            case _:
                return super().rco_exp(e, need_atomic)
        if need_atomic:
            tmp = Name(get_fresh_tmp())
            temporaries.append((tmp, e))
            e = tmp

        return e, temporaries

    def rco_stmt(self, s: stmt) -> list[stmt]:
        temporaries: Temporaries = []

        match s:
            case Return(e):
                e, temporaries = self.rco_exp(e, False)
                s = Return(e)
            case FunctionDef(name, params, body, dec, ret_type, comment):
                body = [item for s in body for item in self.rco_stmt(s)]
                s = FunctionDef(name, params, body, dec, ret_type, comment)
            case _:
                return super().rco_stmt(s)
        return [Assign([tmp[0]], tmp[1]) for tmp in temporaries] + [s]

    ############################################################################
    # Explicate Control
    ############################################################################

    def explicate_control(self, p: Module):
        for fun in p.body:
            if isinstance(fun, FunctionDef):
                fun.body = self.explicate_def(fun.body, fun.name)
        return p

    def explicate_def(self, body: list[stmt], name) -> dict[str, list[Any]]:
        basic_blocks = {}
        cont = []

        # iterate through statements in reversed order
        for s in reversed(body):
            cont = self.explicate_stmt(s, cont, basic_blocks)

        # create start block
        basic_blocks[name + 'start'] = cont

        # add return to last blocks
        for label, block in basic_blocks.items():
            if not block or not (isinstance(block[-1], (Goto, If, Return))):
                block.append(Return(Constant(0)))
        return basic_blocks

    def explicate_stmt(self, s: stmt, cont, basic_blocks) -> list[stmt]:
        match s:
            case Return(val):
                return [Return(val)] + cont
            case _:
                return super().explicate_stmt(s, cont, basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        pass

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> set[location]:
        # YOUR CODE HERE
        pass

    def write_vars(self, i: instr) -> set[location]:
        # YOUR CODE HERE
        pass

    def control_flow_graph(
            self, basic_blocks: dict[str, list[instr]]
    ) -> DirectedAdjList:
        # YOUR CODE HERE
        pass

    def uncover_live(self, block_items, l_after) -> dict[instr, set[location]]:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program, live_blocks) -> UndirectedAdjList:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Allocate Registers
    ############################################################################

    def color_graph(
            self, graph: UndirectedAdjList, colors: set[location]
    ) -> dict[Variable, arg]:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes(self, p: X86ProgramDefs) -> X86ProgramDefs:
        # YOUR CODE HERE
        pass

    ###########################################################################
    # Patch Instructions
    ###########################################################################

    def patch_instructions(self, p: X86ProgramDefs) -> X86ProgramDefs:
        # YOUR CODE HERE
        pass

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86ProgramDefs) -> X86Program:
        # YOUR CODE HERE
        pass

    ##################################################
    # Compiler
    ##################################################

    def compile(self, s: str, logging=False) -> X86Program:
        compiler_passes = {
            'shrink': self.shrink,
            'reveal_functions': self.reveal_functions,
            'limit_functions': self.limit_functions,
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
