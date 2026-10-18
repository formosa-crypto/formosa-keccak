import build
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the 4-way Keccak-f[1600] permutations (ref, alt, nat), of the
   permutation dispatcher _keccakf1600_avx2x4, and of the 4-way state
   init and rate bit.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety.
from Jasmin require import JModel_x86 Jcheck JSafety.
"""
# the driver never writes the state bitmaps back (later calls get constant full bitmaps)
ALT = "valid trace___keccakf1600_avx2x4_alt /\\ BArray800.is_init b_A_4x 0 800"
def ROUND(tr, k): return f"valid {tr} /\\ BArray800.is_init b_A_4x 0 800 /\\ BArray800.is_init b_E_4x 0 {160 * (k - 2)}"
ANN = {
 "__keccakf1600_avx2x4_ref": {"INV1": "valid trace___keccakf1600_avx2x4_ref /\\ 0 <= c /\\ c %% 2 = 0"},
 # round-constant read at 8 * to_uint (of_int i)
 "__f1600_loopbody_native": {"SMT": "W64.of_uintK pow2_64"},
 "__keccakf1600_avx2x4_nat": {"INV1": "valid trace___keccakf1600_avx2x4_nat /\\ 1 <= i <= 24"},
 "__state_init_avx2x4": {"INV1": "valid trace___state_init_avx2x4 /\\ 0 <= i <= 800 /\\ i %% 32 = 0 /\\ BArray800.is_init b_st 0 i"},
 "__keccakf1600_avx2x4_alt": dict((f"BEFORE{k}", ALT) for k in range(3, 26)),
 "__theta_rho_pi_chi_iota": dict((f"BEFORE{k}", ROUND("trace___theta_rho_pi_chi_iota", k)) for k in range(3, 7)),
 "_theta_rho_pi_chi_iota_prepare_theta_even": dict((f"BEFORE{k}", ROUND("trace__theta_rho_pi_chi_iota_prepare_theta_even", k)) for k in range(3, 7)),
 "_theta_rho_pi_chi_iota_prepare_theta_odd": dict((f"BEFORE{k}", ROUND("trace__theta_rho_pi_chi_iota_prepare_theta_odd", k)) for k in range(3, 7)),
}
KER = [f"__{r}_{p}" for p in ["even","odd","last"] for r in ["second","third","fourth","fifth","sixth"]]
items = [('raw', HDR), ('raw', "(* ref *)")]
items += [('gen', n) for n in ["_keccakf1600_4x_pround_ref","__keccakf1600_avx2x4_ref","_keccakf1600_avx2x4_ref"]]
items += [('raw', "(* alt *)")]
items += [('gen', n) for n in ["__rol_4u64_rho56","__rol_4u64_rho8","__rol_4u64","__prepare_theta","__first"] + KER]
items += [('gen', n) for n in ["_theta_rho_pi_chi_iota_prepare_theta_even","_theta_rho_pi_chi_iota_prepare_theta_odd",
                               "__theta_rho_pi_chi_iota","__keccakf1600_avx2x4_alt","_keccakf1600_avx2x4_alt"]]
items += [('raw', "(* nat *)")]
items += [('gen', n) for n in ["__f1600_loopbody_native","__regs_fetch","__regs_unfetch","__keccakf1600_avx2x4_nat","_keccakf1600_avx2x4_nat"]]
items += [('raw', "(* dispatcher, state init, rate bit *)")]
items += [('gen', n) for n in ["_keccakf1600_avx2x4","_keccakf1600_avx2x4_","__state_init_avx2x4","__addratebit_avx2x4"]]
MANUAL = {}
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, build.ROOT + "/avx2x4/Keccakf1600x4_safety.ec")
    print("built")
