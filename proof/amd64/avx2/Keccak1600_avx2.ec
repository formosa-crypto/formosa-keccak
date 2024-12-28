(******************************************************************************
   Keccak1600_avx2.ec:

   Correctness proof for the Keccak AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

require import WArray768.
from JazzEC require import Jazz_avx2.

require import Array4 Array5 Array7 Array24 Array25.

from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

(* circuit-friendly state mappings *)

abbrev u256_bits64 (w: W256.t) k : W64.t =
 W64.init (fun i => w.[i+64*k]).

lemma u256_bits64E w k:
 0 <= k < 4 =>
 u256_bits64 w k = w \bits64 k.
proof.
move=> Hk; rewrite /u256_bits64.
apply W64.ext_eq => i Hi.
by rewrite bits64E initiE 1://= initiE 1://= /#.
qed.

op u256_pack4 (w0 w1 w2 w3: W64.t): W256.t =
 W256.init (fun i => if i < 64 then w0.[i]
                     else if i < 128 then w1.[i-64]
                     else if i < 192 then w2.[i-128]
                     else w3.[i-192]).


lemma u256_pack4E w0 w1 w2 w3:
 u256_pack4 w0 w1 w2 w3 = pack4 [w0; w1; w2; w3].
proof.
rewrite /u256_pack4; apply W256.ext_eq => k Hk.
rewrite initiE 1:// pack4E initiE 1:// /=.
rewrite get_of_list 1:/# /=.
case: (k < 64) => C1.
 by rewrite ifT 1:/# modz_small /= /#.
case: (k < 128) => C2.
 by rewrite ifF 1:/# ifT 1:/#; congr; smt().
case: (k < 192) => C3.
 by rewrite ifF 1:/# ifF 1:/# ifT 1:/#; congr; smt().
by rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#; congr => /#.
qed.

op stavx2_from_st25 (st: W64.t Array25.t): W256.t Array7.t =
 Array7.of_list W256.zero
  [ u256_pack4 st.[ 0] st.[ 0] st.[ 0] st.[ 0]
  ; u256_pack4 st.[ 1] st.[ 2] st.[ 3] st.[ 4]
  ; u256_pack4 st.[10] st.[20] st.[ 5] st.[15]
  ; u256_pack4 st.[16] st.[ 7] st.[23] st.[14]
  ; u256_pack4 st.[11] st.[22] st.[ 8] st.[19]
  ; u256_pack4 st.[21] st.[17] st.[13] st.[ 9]
  ; u256_pack4 st.[ 6] st.[12] st.[18] st.[24]
  ].

op stavx2_to_st25 (st: W256.t Array7.t): W64.t Array25.t =
 Array25.of_list W64.zero
  [ u256_bits64 st.[0] 0; u256_bits64 st.[1] 0; u256_bits64 st.[1] 1; u256_bits64 st.[1] 2; u256_bits64 st.[1] 3
  ; u256_bits64 st.[2] 2; u256_bits64 st.[6] 0; u256_bits64 st.[3] 1; u256_bits64 st.[4] 2; u256_bits64 st.[5] 3
  ; u256_bits64 st.[2] 0; u256_bits64 st.[4] 0; u256_bits64 st.[6] 1; u256_bits64 st.[5] 2; u256_bits64 st.[3] 3
  ; u256_bits64 st.[2] 3; u256_bits64 st.[3] 0; u256_bits64 st.[5] 1; u256_bits64 st.[6] 2; u256_bits64 st.[4] 3
  ; u256_bits64 st.[2] 1; u256_bits64 st.[5] 0; u256_bits64 st.[4] 1; u256_bits64 st.[3] 2; u256_bits64 st.[6] 3
  ].

lemma stavx2_from_st25K st:
 stavx2_to_st25 (stavx2_from_st25 st) = st.
proof.
rewrite /stavx2_to_st25 /stavx2_from_st25 !u256_bits64E 1..25:// /=.
rewrite !u256_pack4E /=.
by apply Array25.all_eq_eq; rewrite /all_eq.
qed.

op u256_broadcastP w =
 u256_bits64 w 1 = u256_bits64 w 0
 /\ u256_bits64 w 2 = u256_bits64 w 0
 /\ u256_bits64 w 3 = u256_bits64 w 0.

lemma u256_broadcastP_VPBROADCAST w:
 u256_broadcastP (VPBROADCAST_4u64 w).
proof.
rewrite /VPBROADCAST_4u64 /u256_broadcastP.
by rewrite !u256_bits64E 1..4:// !pack4bE 1..4:// /= -iotaredE /=.
qed.

lemma u256_broadcastP_xor w1 w2:
 u256_broadcastP w1 =>
 u256_broadcastP w2 =>
 u256_broadcastP (w1 `^` w2).
proof.
by rewrite /u256_broadcastP !u256_bits64E 1..12:// !xorb64E /#.
qed.


abbrev stF_avx2 f = fun st => stavx2_from_st25 (f (stavx2_to_st25 st)).

op stavx2_keccakf1600 = stF_avx2 keccak_f1600_op.



