import os
from compiler_fun import Compiler
import interp_Lfun
import interp_Cfun
import type_check_Cfun
import type_check_Lfun
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

#enable_tracing()

fun_compiler = Compiler()

typecheck_Lfun = type_check_Lfun.TypeCheckLfun().type_check
typecheck_Cfun = type_check_Cfun.TypeCheckCfun().type_check

typecheck_dict = {
    'source': typecheck_Lfun,
    'shrink': typecheck_Lfun,
    'expose_allocation': typecheck_Lfun,
    'remove_complex_operands': typecheck_Lfun,
    'explicate_control': typecheck_Cfun,
}

interpLfun = interp_Lfun.InterpLfun().interp
interpCfun = interp_Cfun.InterpCfun().interp

# interp_x86 cannot run assign_homes and patch_instructions because of the missing
# prelude and conclusion
interp_dict = {
    'shrink': interpLfun,
    'reveal_functcions': interpLfun,
    'expose_allocation': interpLfun,
    'remove_complex_operands': interpLfun,
    'explicate_control': interpCfun,
    'select_instructions': interp_x86,
    #'assign_homes': interp_x86,
    #'patch_instructions': interp_x86,
    'prelude_and_conclusion': interp_x86,
}

run_tests('var', fun_compiler, 'fun', typecheck_dict, interp_dict)
run_tests('regalloc', fun_compiler, 'fun', typecheck_dict, interp_dict)
run_tests('lif', fun_compiler, 'fun', typecheck_dict, interp_dict)
run_tests('while', fun_compiler, 'fun', typecheck_dict, interp_dict)
run_tests('tup', fun_compiler, 'fun', typecheck_dict, interp_dict)
run_tests('fun', fun_compiler, 'fun', typecheck_dict, interp_dict)
