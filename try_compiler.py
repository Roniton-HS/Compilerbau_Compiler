from ast import *
from utils import *
from compiler_fun import Compiler
from x86_ast import Reg

compiler = Compiler()

prog = """
def maps(f : Callable[[int], int,], v : int) -> int:
    return f(v)
    
def inc(x : int) -> int:
    return (x + 1)

x = maps
"""

print("#Parse")
ast = parse(prog)
print(ast)

print("#Shrink")
ast = compiler.shrink(ast)
print(ast)

print("#Reveal Functions")
ast = compiler.reveal_functions(ast)
print(ast)

print("#Expose Allocation")
ast = compiler.expose_allocation(ast)
print(ast)

print("#Remove Complex Operants")
ast = compiler.remove_complex_operands(ast)
print(ast)

print("#Explicate Control")
ast = compiler.explicate_control(ast)
print(ast)

print("#Select Instructions")
ast = compiler.select_instructions(ast)
print(ast)
