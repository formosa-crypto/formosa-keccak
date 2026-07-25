(******************************************************************************
   Keccakf1600_avx2x4_alt.ec:

   Correctness proof for the 4-way AVX2 "alt" implementation
   [__keccakf1600_avx2x4_alt] (src/amd64/avx2/keccakf1600x4_alt.jinc).

   Unlike the "ref" variant, [alt] is FULLY UNROLLED (no round loop) and uses a
   SOFTWARE-PIPELINED ("lazy") theta: the theta column-sums (ca..cu) of round
   k+1 are computed inside the chi/iota kernel of round k and returned alongside
   the state.  A logical round is therefore split across two textual kernels and
   cannot be isolated the way the "ref" pround is.

******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.
require import Keccakf1600_avx2x4_ref.

require import Keccak_bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array1 Array100 WArray200 WArray800.

require import Avx2_extra.

from JazzEC require import Array5 Array24 Array25.


(* -------------------------------------------------------------------------- *)
(*  Packed column parity (the fused theta sum carried across rounds)          *)
(* -------------------------------------------------------------------------- *)

(* column [x] parity of the packed state: way k in the 64-bit sub-word k *)
op st4x_Ci (st: state4x) (x:int) : W256.t =
 u256_pack4 (keccak_C (st4x_get st 0)).[x] (keccak_C (st4x_get st 1)).[x]
            (keccak_C (st4x_get st 2)).[x] (keccak_C (st4x_get st 3)).[x].

(* the 5-tuple returned by [__prepare_theta] / carried by the kernels *)
op st4x_C (st: state4x) : W256.t * W256.t * W256.t * W256.t * W256.t =
 (st4x_Ci st 0, st4x_Ci st 1, st4x_Ci st 2, st4x_Ci st 3, st4x_Ci st 4).



(* -------------------------------------------------------------------------- *)
(*  Kernel contracts (each closed by [proc; inline*; circuit] -- admitted)     *)
(* -------------------------------------------------------------------------- *)

(* [__prepare_theta] computes the packed column sums of its argument. *)
hoare prepare_theta_alt_h _a:
 M.__prepare_theta :
 a_4x = _a
 ==> res = st4x_C _a.
proof. by proc; inline*; circuit. qed.

(*pragma +Circuit:timing.*)

(* full round kernel (even buffer orientation):
   given the carried sums = st4x_C _a and the broadcast round constant [rc],
   the destination buffer (res.`2) holds one full round applied lane-wise,
   and the new carried sums (res.`3..`7) are st4x_C of that round output. *)
hoare kernel_even_alt_h rc _a:
 M._theta_rho_pi_chi_iota_prepare_theta_even :
 a_4x = _a
 /\ (ca, ce, ci, co, cu) = st4x_C _a
 /\ rc_index = VPBROADCAST_4u64 rc
 ==> res.`2 = st4x_map (keccak_round_op rc) _a
  /\ (res.`3, res.`4, res.`5, res.`6, res.`7)
     = st4x_C (st4x_map (keccak_round_op rc) _a).
proof.
proc; inline*.
do 2! cfold 6.
do 2! cfold 11.
do 2! cfold 17.
do 2! cfold 21.
do 2! cfold 24.
do 10! cfold 33.
do 2! cfold 40.
cfold 49. cfold 62. cfold 74.
do 10! cfold 92.
cfold 96. cfold 104. cfold 112. cfold 124. cfold 136.
do 10! cfold 155.
cfold 159. cfold 167. cfold 175. cfold 197.
do 10! cfold 216.
cfold 220. cfold 228. cfold 236. cfold 248.
do 10! cfold 277.
cfold 281. cfold 289. cfold 297. cfold 309. cfold 321.
do 5! cfold 338.
cfold 339.
wp 339.
by circuit.
qed.

(* full round kernel (odd buffer orientation): byte-identical to the even one. *)
hoare kernel_odd_alt_h rc _a:
 M._theta_rho_pi_chi_iota_prepare_theta_odd :
 a_4x = _a
 /\ (ca, ce, ci, co, cu) = st4x_C _a
 /\ rc_index = VPBROADCAST_4u64 rc
 ==> res.`2 = st4x_map (keccak_round_op rc) _a
  /\ (res.`3, res.`4, res.`5, res.`6, res.`7)
     = st4x_C (st4x_map (keccak_round_op rc) _a).
proof.
proc; simplify; inline*.
do 7! cfold 1.
do 2! cfold 6.
do 2! cfold 11.
do 2! cfold 16.
do 2! cfold 21.
do 14! cfold 26.
cfold 34. cfold 42. cfold 45. cfold 54. cfold 66.
do 31! cfold 80.
cfold 90.
do 16! cfold 80.
do 6! cfold 81.
cfold 82. cfold 90. cfold 98. cfold 110. cfold 122.
do 10! cfold 140.
cfold 144. cfold 152. cfold 160. cfold 182.
do 11! cfold 198.
cfold 202. cfold 210. cfold 218. cfold 230.
do 6! cfold 255.
do 8! cfold 256.
cfold  264. cfold 272. cfold 284. cfold 296.
do 7! cfold 312.
do 7! cfold 313.
do 2! cfold 314.
cfold 325.
do 5! cfold 330.
do 4! cfold 336.
do 4! cfold 342.
do 12! cfold 348.
wp 352.
by circuit.
qed.

(* last round kernel: one full round, but no next-round theta-sum. *)
hoare kernel_last_alt_h rc _a:
 M.__theta_rho_pi_chi_iota :
 a_4x = _a
 /\ (ca, ce, ci, co, cu) = st4x_C _a
 /\ rc_index = VPBROADCAST_4u64 rc
 ==> res.`2 = st4x_map (keccak_round_op rc) _a.
proof.
proc; simplify; inline*.
cfold 7. cfold 13. cfold 19. cfold 25. cfold 31. cfold 53. cfold 61. cfold 73. cfold 84.
cfold 109. cfold 117. cfold 125. cfold 136. cfold 147. cfold 172. cfold 180. cfold 188.
cfold 208. cfold 233. cfold 241. cfold 249. cfold 260. cfold 282. cfold 293. cfold 301.
cfold 309. cfold 320. cfold 331.
wp 343.
by circuit.
qed.


(* -------------------------------------------------------------------------- *)
(*  Top-level correctness of the unrolled permutation                          *)
(* -------------------------------------------------------------------------- *)

hoare __keccakf1600_avx2x4_alt_h _a:
 M.__keccakf1600_avx2x4_alt :
 a_4x = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
ecall (kernel_last_alt_h rC.[23] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[22] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[21] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[20] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[19] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[18] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[17] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[16] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[15] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[14] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[13] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[12] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[11] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[10] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[9] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[8] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[7] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[6] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[5] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[4] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[3] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[2] a_4x); simplify.
wp; ecall (kernel_odd_alt_h rC.[1] e_4x); simplify.
wp; ecall (kernel_even_alt_h rC.[0] a_4x); simplify.
wp; ecall (prepare_theta_alt_h a_4x); simplify.
auto => |> /=.
move => _ [a1 e1 c1a c1e c1i c1o c1u] /= -> ?; split; first smt().
move=> C1 [e2 a2 c2a c2e c2i c2o c2u] /= -> ?; split; first smt().
move=> C2; rewrite st4x_map_comp.
move=> [a3 e3 c3a c3e c3i c3o c3u] /= -> ?; split; first smt().
move=> C3; rewrite st4x_map_comp.
move=> [e4 a4 c4a c4e c4i c4o c4u] /= -> ?; split; first smt().
move=> C4; rewrite st4x_map_comp.
move=> [a5 e5 c5a c5e c5i c5o c5u] /= -> ?; split; first smt().
move=> C5; rewrite st4x_map_comp.
move=> [e6 a6 c6a c6e c6i c6o c6u] /= -> ?; split; first smt().
move=> C6; rewrite st4x_map_comp.
move=> [a7 e7 c7a c7e c7i c7o c7u] /= -> ?; split; first smt().
move=> C7; rewrite st4x_map_comp.
move=> [e8 a8 c8a c8e c8i c8o c8u] /= -> ?; split; first smt().
move=> C8; rewrite st4x_map_comp.
move=> [a9 e9 c9a c9e c9i c9o c9u] /= -> ?; split; first smt().
move=> C9; rewrite st4x_map_comp.
move=> [e10 a10 c10a c10e c10i c10o c10u] /= -> ?; split; first smt().
move=> C10; rewrite st4x_map_comp.
move=> [a11 e11 c11a c11e c11i c11o c11u] /= -> ?; split; first smt().
move=> C11; rewrite st4x_map_comp.
move=> [e12 a12 c12a c12e c12i c12o c12u] /= -> ?; split; first smt().
move=> C12; rewrite st4x_map_comp.
move=> [a13 e13 c13a c13e c13i c13o c13u] /= -> ?; split; first smt().
move=> C13; rewrite st4x_map_comp.
move=> [e14 a14 c14a c14e c14i c14o c14u] /= -> ?; split; first smt().
move=> C14; rewrite st4x_map_comp.
move=> [a15 e15 c15a c15e c15i c15o c15u] /= -> ?; split; first smt().
move=> C15; rewrite st4x_map_comp.
move=> [e16 a16 c16a c16e c16i c16o c16u] /= -> ?; split; first smt().
move=> C16; rewrite st4x_map_comp.
move=> [a17 e17 c17a c17e c17i c17o c17u] /= -> ?; split; first smt().
move=> C17; rewrite st4x_map_comp.
move=> [e18 a18 c18a c18e c18i c18o c18u] /= -> ?; split; first smt().
move=> C18; rewrite st4x_map_comp.
move=> [a19 e19 c19a c19e c19i c19o c19u] /= -> ?; split; first smt().
move=> C19; rewrite st4x_map_comp.
move=> [e20 a20 c20a c20e c20i c20o c20u] /= -> ?; split; first smt().
move=> C20; rewrite st4x_map_comp.
move=> [a21 e21 c21a c21e c21i c21o c21u] /= -> ?; split; first smt().
move=> C21; rewrite st4x_map_comp.
move=> [e22 a22 c22a c22e c22i c22o c22u] /= -> ?; split; first smt().
move=> C22; rewrite st4x_map_comp.
move=> [a23 e23 c23a c23e c23i c23o c23u] /= -> ?; split; first smt().
move=> C23; rewrite st4x_map_comp.
move=> [e24 a24] /= ->; clear.
rewrite st4x_map_comp /=; congr.
rewrite fun_ext => st.
rewrite /keccak_f1600_op -iotaredE /=.
congr; by rewrite initiE.
qed.

lemma __keccakf1600_avx2x4_alt_ll: islossless M.__keccakf1600_avx2x4_alt.
proof. by islossless. qed.

phoare __keccakf1600_avx2x4_alt_ph _a:
 [ M.__keccakf1600_avx2x4_alt
 : a_4x = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. by conseq __keccakf1600_avx2x4_alt_ll (__keccakf1600_avx2x4_alt_h _a). qed.

hoare keccakf1600_avx2x4_alt_h _a:
 M._keccakf1600_avx2x4_alt :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof. by proc; ecall (__keccakf1600_avx2x4_alt_h a). qed.

lemma keccakf1600_avx2x4_alt_ll: islossless M._keccakf1600_avx2x4_alt.
proof. by proc; call __keccakf1600_avx2x4_alt_ll. qed.

