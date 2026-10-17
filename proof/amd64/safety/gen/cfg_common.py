import re
import json, build
M = json.load(open(build.HERE + "/common_manual.json"))
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the common helpers: feature query, shifts, rho offsets,
   memory/array sub-reads/writes, 4-way pack/unpack, status-word decoder.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.
"""
BIT = """(* -------------------------------------------------------------------- *)
(* TEST_64 on small lengths (variable-length sub-reads/writes)             *)
"""
WORD = """(* -------------------------------------------------------------------- *)
(* word facts used by the streaming (updstate) code                        *)
lemma and7_to_uint (a : int) :
  0 <= a < 18446744073709551616 =>
  to_uint (W64.of_int a `&` W64.of_int 7) = a %% 8.
proof.
move=> ha; rewrite (: 7 = 2^3 - 1) // to_uint_and_mod // of_uintK.
by rewrite (modz_small a) //; smt().
qed.

lemma and7_nz (a : int) :
  0 <= a < 18446744073709551616 =>
  (W64.of_int a `&` W64.of_int 7 <> W64.of_int 0) = (a %% 8 <> 0).
proof. by move=> ha; rewrite W64.to_uint_eq /= (and7_to_uint a ha). qed.

lemma int_shr3 (a : int) : a `|>>` 3 = a %/ 8.
proof. by rewrite /(`|>>`) /(`<<`) /=. qed.

lemma int_shl3 (a : int) : a `<<` 3 = a * 8.
proof. by rewrite /(`<<`) /=. qed.

lemma chunks8 (l : int) :
  0 <= l => 32 * (l %/ 32) + (if 16 <= l %% 32 then 16 else 0) + (if 8 <= l %% 16 then 8 else 0) = 8 * (l %/ 8).
proof. smt(). qed.
"""

def _inith():
    sizes = sorted(set(int(x) for x in re.findall(r"\bBArray(\d+)\b", open(build.MODEL).read())))
    t = """(* -------------------------------------------------------------------- *)
(* bitmaps of fully (un)initialised arrays, sub-array updates             *)
require import SBArray208_200 SBArray808_800.
hint simplify SBArray208_200.is_init_cell_set, SBArray808_800.is_init_cell_set.
"""
    for n in sizes:
        t += (f"lemma BArray{n}_init_cell_ones k : BArray{n}.is_init_cell (BArray{n}.init_arr (W8.of_int 255)) k = true.\n"
              f"proof. by rewrite eqT; apply (BArray{n}.init_arrP witness). qed.\n"
              f"lemma BArray{n}_init_cell_zeros k : BArray{n}.is_init_cell (BArray{n}.init_arr (W8.of_int 0)) k = !(0 <= k < {n}).\n"
              f"proof. by rewrite /BArray{n}.is_init_cell; case: (0 <= k < {n}) => //= h; rewrite BArray{n}.initE h /= W8.to_uint_eq. qed.\n"
              f"hint simplify BArray{n}_init_cell_ones, BArray{n}_init_cell_zeros.\n")
    return t
INITH = _inith()
items = [('raw', HDR), ('raw', INITH)]
items += [('gen', n) for n in ["__HAS_FEATURE","__SHLQ","__SHLDQ","__SHLQ_256","__KECCAK_F","__KECCAK_Fx4",
                               "keccakf1600_index","keccakf1600_rho_offsets","keccakf1600_rhotates"]]
items += [('raw', "(* memory sub-reads/writes *)")]
items += [('gen', n) for n in ["__m_ilen_read_upto8_at","__m_ilen_read_upto16_at","__m_ilen_read_upto32_at",
                               "__m_ilen_read_bcast_upto8_at","__m_ilen_write_upto8","__m_ilen_write_upto16","__m_ilen_write_upto32"]]
items += [('raw', BIT)] + [('raw', M["helpers"][k]) for k in ["and_shlwE","test_64_zf","test_zf_small","zf4","zf2","zf1"]]
items += [('gen', n) for n in ["__m_rlen_read_upto8","__m_rlen_write_upto8"]]
items += [('raw', "(* status-word decoder *)"), ('raw', M["helpers"]["to_uint_and255"]), ('gen', "_ststatus_data")]
items += [('raw', "(* 4-way pack/unpack *)")]
items += [('gen', n) for n in ["__u256x4_4u64x4","__st4x_pack","__4u64x4_u256x4","__st4x_unpack"]]
items += [('raw', WORD)]
items += [('theory', dict(name="ReadWriteArraySafety", presets=["subreadwrite"], rw=False,
                          check="Keccak1600_subreadwrite_checkXtr.ec"))]
ANN = {
 "keccakf1600_rho_offsets": {"INV1": "valid trace_keccakf1600_rho_offsets"},
 "__st4x_pack": {"INV1": "valid trace___st4x_pack /\\ 0 <= i <= 6 /\\ BArray800.is_init b_st4x 0 (128 * i)"},
 "__st4x_unpack": {"INV1": "valid trace___st4x_unpack /\\ 0 <= i <= 6 /\\ BArray200.is_init b_st0 0 (32 * i) /\\ BArray200.is_init b_st1 0 (32 * i) /\\ BArray200.is_init b_st2 0 (32 * i) /\\ BArray200.is_init b_st3 0 (32 * i)"},
}
MANUAL = M["manual"]
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, build.ROOT + "/common/Keccak1600_common_safety.ec")
    print("built")
