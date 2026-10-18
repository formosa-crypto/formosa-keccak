import build
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the 1-way Keccak-f[1600] permutations (ref, basic, opt, avx2)
   and of the permutation dispatcher _keccakf1600.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety.
from Jasmin require import JModel_x86 Jcheck JSafety.
"""
items = [('raw', HDR), ('raw', "(* ref *)")]
items += [('gen', n) for n in ["__andn_u64_ref","__rol_u64_ref","__theta_sum_ref","__theta_rol_ref","__rol_sum_ref",
                               "__set_row_ref","_pround_ref","__keccakf1600_ref","_keccakf1600_ref","_keccakf1600_ref_"]]
items += [('raw', "(* basic *)")]
items += [('gen', n) for n in ["__pround_basic_inlined","__not_lane_basic","__complement_lanes_basic",
                               "__keccakf1600_basic","_keccakf1600_basic","_keccakf1600_basic_"]]
items += [('raw', "(* opt *)")]
items += [('gen', n) for n in ["keccakf1600_opt_loop_body","read_regs_opt","store_regs_opt","__keccakf1600_opt","_keccakf1600_opt"]]
items += [('raw', "(* avx2 *)")]
items += [('gen', n) for n in ["__keccakf1600_pround_avx2","__keccakf1600_avx2","_keccakf1600_avx2",
                               "__stavx2_pack","__stavx2_unpack","_keccakf1600_st25_avx2"]]
items += [('raw', "(* dispatcher *)")]
items += [('gen', n) for n in ["_keccakf1600","_keccakf1600_"]]
V = "valid trace_"
ANN = {
 "__theta_sum_ref": {
   "INV1": "valid trace___theta_sum_ref /\\ 0 <= x <= 5 /\\ BArray40.is_init b_c 0 (8 * x)",
   "INV2": "valid trace___theta_sum_ref /\\ 1 <= y <= 5 /\\ BArray40.is_init b_c 0 40",
   "INV3": "valid trace___theta_sum_ref /\\ 0 <= x <= 5 /\\ 1 <= y < 5 /\\ BArray40.is_init b_c 0 40"},
 "__theta_rol_ref": {"INV1": "valid trace___theta_rol_ref /\\ 0 <= x <= 5 /\\ BArray40.is_init b_d 0 (8 * x)"},
 "__rol_sum_ref": {"INV1": "valid trace___rol_sum_ref /\\ 0 <= x <= 5 /\\ BArray40.is_init b_b 0 (8 * x)"},
 "__set_row_ref": {"INV1": "valid trace___set_row_ref /\\ 0 <= x <= 5 /\\ 0 <= y < 5 /\\ BArray40.is_init b_b 0 40 /\\ BArray200.is_init b_e 0 (y * 5 * 8 + 8 * x)"},
 "_pround_ref": {"INV1": "valid trace__pround_ref /\\ 0 <= y <= 5 /\\ BArray200.is_init b_e 0 (y * 5 * 8)"},
 # drivers: their closers are cheap atom by atom, and the shallow attempt only adds a timeout
 "__keccakf1600_ref": {"SPLIT": ('all',), "INV1": "valid trace___keccakf1600_ref /\\ 0 <= c /\\ BArray200.is_init b_a 0 200"},
 "__keccakf1600_basic": {"SPLIT": ('all',), "INV1": "valid trace___keccakf1600_basic /\\ 0 <= c /\\ BArray200.is_init b_a 0 200"},
 "__pround_basic_inlined": {"SPLIT": ('all',)},
 # two rounds in registers: stepwise wp (see gen.STEPWP); the round-constant reads need
 # to_uint of the counter and of its successor
 "keccakf1600_opt_loop_body": {"STEPWP": 10,
   "SMT": "W64.uleE W64.to_uintD_small W64.to_uint_cmp W64.of_uintK W64.to_uint1 pow2_64"},
 "__keccakf1600_opt": {"SPLIT": ('all',), "SMT": "W64.uleE W64.ultE W64.to_uintD_small W64.to_uint_cmp W64.of_uintK pow2_64",
   "INV1": "valid trace___keccakf1600_opt /\\ W64.to_uint rax %% 2 = 0 /\\ W64.to_uint rax <= 24"},
 "__keccakf1600_pround_avx2": {"STEPWP": 10},
 "__keccakf1600_avx2": {"INV1": "valid trace___keccakf1600_avx2 /\\ 1 <= r <= 24"},
}
MANUAL = {}
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, build.ROOT + "/ref/Keccakf1600_safety.ec")
    print("built")
