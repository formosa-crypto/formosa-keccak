(******************************************************************************
   Keccak1600_avx2.ec:

   Correctness proof for the Keccak AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.
require BitEncoding.
import BitEncoding.BitChunking.


from Jasmin require import JModel.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import Keccakf1600_Spec FIPS202_SHA3_Spec.
from CryptoSpecs require export Keccak1600_Spec.

from JazzEC require import Jazz_avx2.

from JazzEC require import WArray200.
from JazzEC require import Array25 Array7.

(*
from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec Keccak1600_Spec FIPS202_SHA3_Spec.
*)

require import Avx2_extra.

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

lemma stavx2_from_st25_inj st1 st2:
 stavx2_from_st25 st1 = stavx2_from_st25 st2 =>
 st1 = st2.
proof.
move=> E.
by rewrite -(stavx2_from_st25K st1) -(stavx2_from_st25K st2) E.
qed.

op stavx2_st0 = stavx2_from_st25 st0.

lemma stavx2_st0P i:
 0 <= i < 7 =>
 stavx2_st0.[i] = W256.zero.
proof.
move=> Hi.
have: i \in iotared 0 7 by smt(mem_iota).
move: {Hi} i; apply/List.allP => /=.
by rewrite /stavx2_st0 /stavx2_from_st25 get_of_list 1:// /= /st0 !createiE 1..25:// u256_pack4_zero.
qed.

op stavx2INV (st: W256.t Array7.t): bool =
 u256_broadcastP st.[0].

lemma stavx2INV_from_st25 st:
 stavx2INV (stavx2_from_st25 st).
proof.
by rewrite /stavx2INV /u256_broadcastP !initiE 1:// !u256_bits64E 1..4://= /= !u256_pack4E pack4bE //.
qed.

lemma stavx2_to_st25K st:
 stavx2INV st =>
 stavx2_from_st25 (stavx2_to_st25 st) = st.
proof.
rewrite /stavx2INV /stavx2_to_st25 /stavx2_from_st25 !u256_bits64E 1..25:// /=.
rewrite !u256_pack4E /u256_broadcastP !u256_bits64E 1..4:// => /> ???.
apply Array7.all_eq_eq; rewrite /all_eq /=.
do split;
 rewrite -{5}(unpack64K st.[_]) unpack64E; congr;
 apply W4u64.Pack.all_eq_eq; rewrite /all_eq /= /#.
qed.

lemma stavx2_to_st25_inj st1 st2:
 stavx2INV st1 =>
 stavx2INV st2 =>
 stavx2_to_st25 st1 = stavx2_to_st25 st2 =>
 st1 = st2.
proof.
move=> H1 H2 E.
by rewrite -(stavx2_to_st25K st1 _) 1:// -(stavx2_to_st25K st2 _) 1:// E.
qed.

abbrev stF_avx2 f = fun st => stavx2_from_st25 (f (stavx2_to_st25 st)).

op stavx2_keccakf1600 = stF_avx2 keccak_f1600_op.

(******************************************************************************
   
******************************************************************************)


op absorb_spec_avx2 (r8: int) (tb: int) (l: W8.t list) st =
 st = stavx2_from_st25 (ABSORB1600 (W8.of_int tb) r8 l).

op pabsorb_spec_avx2 r8 l (pst: W64.t Array25.t) (st: W256.t Array7.t): bool =
 0 < r8 <= 200 /\
 st=stavx2_from_st25 (stateabsorb_iblocks (chunk r8 l) st0) /\
 sub (stbytes pst) 0 (size l %% r8) = chunkremains r8 l
 /\
 sub (stbytes pst) r8 (200-r8) = nseq (200-r8) W8.zero.

lemma pabsorb_spec_avx2_nil r8:
 0 < r8 <= 200 =>
 pabsorb_spec_avx2 r8 [] st0 stavx2_st0.
proof.
move=> Hr; rewrite /stavx2_st0 /pabsorb_spec_avx2 => />.
rewrite chunk0 /= 1:/#.
rewrite /stateabsorb_iblocks /= /chunkremains /= /sub mkseq0 -mkseq_nseq /=.
apply eq_in_mkseq => i Hi /=.
by rewrite initiE 1:/# /= /st0 createiE 1:/# W8u8.get_zero.
qed.

(*
lemma pabsorb_spec_avx2_cat r8 l1 l2 pst1 st1 pst2 st2:
 pabsorb_spec_avx2 r8 l1 pst1 st1 =>
 pabsorb_spec_avx2 r8 st1 l22 st2 (l12++l2)=>
 pabsorb_spec_avx2 r8 st0 l22 st2 (l1++l2).
proof.
rewrite /pabsorb_spec_avx2 => /> Hr0 Hr1; split.
 admit.
admit.
qed.
*)

op fillpst_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill 
   (fun i => nth W8.zero l (i-at)) at (size l) (stbytes st)).

(*
op squeeze_spec_avx2 r8 st l =
 l = SQUEEZE1600 r8 (size l) (stavx2_to_st25 st).

op squeezeblocks_spec_avx2 n r8 st l st1 =
 st1 = stavx2_from_st25 (st_i (stavx2_to_st25 st) n)
 /\ l = SQUEEZE1600 r8 (size l) (stavx2_to_st25 st).
*)

(******************************************************************************
   
******************************************************************************)

(*
u64_to_u256
*)


lemma state_init_avx2_ll:
 islossless M.__state_init_avx2.
proof.
proc.
while true (7-i).
 by move=> z; auto => /> /#.
auto => /#.
qed.

hoare state_init_avx2_h:
 M.__state_init_avx2
 : true
 ==> res = stavx2_st0.
proof.
proc.
unroll for ^while; auto => />.
by apply Array7.all_eq_eq; rewrite /all_eq /= !stavx2_st0P.
qed.

phoare state_init_avx2_ph:
 [ M.__state_init_avx2
 : true
 ==> res = stavx2_st0
 ] = 1%r.
proof. by conseq state_init_avx2_ll state_init_avx2_h. qed.

lemma pstate_init_avx2_ll:
 islossless M.__pstate_init_avx2.
proof.
proc.
call state_init_avx2_ll.
wp; while true (aux-i).
 by move=> z; auto => /> /#.
by auto => /#.
qed.

hoare pstate_init_avx2_h _r8:
 M.__pstate_init_avx2
 : 0 < _r8 <= 200
 ==> pabsorb_spec_avx2 _r8 [] res.`1 res.`2.
proof.
proc.
seq 7: (#pre /\ pst=st0).
 admit.
call state_init_avx2_h; auto => |> *.
by apply pabsorb_spec_avx2_nil.
qed.

phoare pstate_init_avx2_ph _r8:
 [ M.__pstate_init_avx2
 : 0 < _r8 <= 200
 ==> pabsorb_spec_avx2 _r8 [] res.`1 res.`2
 ] = 1%r.
proof. by conseq pstate_init_avx2_ll (pstate_init_avx2_h _r8). qed.

(*
perm_reg3456_avx2
*)

(*
unperm_reg3456_avx2
*)

(*
state_from_pstate_avx2
*)
lemma state_from_pstate_avx2_ll: islossless M.__state_from_pstate_avx2
by islossless.

hoare state_from_pstate_avx2_h _pst:
 M.__state_from_pstate_avx2
 : pst=_pst
 ==> res = stavx2_from_st25 _pst.
proof.
admit. (* BDEP *)
qed.

phoare state_from_pstate_avx2_ph _pst:
 [ M.__state_from_pstate_avx2
 : pst=_pst
 ==> res = stavx2_from_st25 _pst
 ] = 1%r.
proof. by conseq state_from_pstate_avx2_ll (state_from_pstate_avx2_h _pst). qed.

(*
addstate_r3456_avx2
*)

(*
addpst01_avx2
*)
lemma addpst01_avx2_ll: islossless M.__addpst01_avx2
 by islossless.

hoare addpst01_avx2_h _pst _stavx2:
 M.__addpst01_avx2
 : pst=_pst /\ st=_stavx2
 ==> res.[0] = _stavx2.[0] `^` u256_pack4 _pst.[0] _pst.[0] _pst.[0] _pst.[0]
  /\ res.[1] = _stavx2.[1] `^` u256_pack4 _pst.[1] _pst.[2] _pst.[3] _pst.[4]
  /\ res.[2] = _stavx2.[2]
  /\ res.[3] = _stavx2.[3]
  /\ res.[4] = _stavx2.[4]
  /\ res.[5] = _stavx2.[5]
  /\ res.[6] = _stavx2.[6].
proof.
admit (* bdep *).
qed.

phoare addpst01_avx2_ph _pst _stavx2:
 [ M.__addpst01_avx2
 : pst=_pst /\ st=_stavx2
 ==> res.[0] = _stavx2.[0] `^` u256_pack4 _pst.[0] _pst.[0] _pst.[0] _pst.[0]
  /\ res.[1] = _stavx2.[1] `^` u256_pack4 _pst.[1] _pst.[2] _pst.[3] _pst.[4]
  /\ res.[2] = _stavx2.[2]
  /\ res.[3] = _stavx2.[3]
  /\ res.[4] = _stavx2.[4]
  /\ res.[5] = _stavx2.[5]
  /\ res.[6] = _stavx2.[6]
 ] = 1%r.
proof. by conseq addpst01_avx2_ll (addpst01_avx2_h _pst _stavx2). qed.

(*
addpst23456_avx2
*)
lemma addpst23456_avx2_ll: islossless M.__addpst23456_avx2
 by islossless.

hoare addpst23456_avx2_h _pst _stavx2:
 M.__addpst23456_avx2
 : pst=_pst /\ st=_stavx2
 ==> res.[0] = _stavx2.[0]
  /\ res.[1] = _stavx2.[1]
  /\ res.[2] = _stavx2.[2] `^` u256_pack4 _pst.[10] _pst.[20] _pst.[5]  _pst.[15]
  /\ res.[3] = _stavx2.[3] `^` u256_pack4 _pst.[16] _pst.[7]  _pst.[23] _pst.[14]
  /\ res.[4] = _stavx2.[4] `^` u256_pack4 _pst.[11] _pst.[22] _pst.[8]  _pst.[19]
  /\ res.[5] = _stavx2.[5] `^` u256_pack4 _pst.[21] _pst.[17] _pst.[13] _pst.[9]
  /\ res.[6] = _stavx2.[6] `^` u256_pack4 _pst.[6]  _pst.[12] _pst.[18] _pst.[24].
proof.
admit (* bdep *).
qed.

phoare addpst23456_avx2_ph _pst _stavx2:
 [ M.__addpst23456_avx2
 : pst=_pst /\ st=_stavx2
 ==> res.[0] = _stavx2.[0]
  /\ res.[1] = _stavx2.[1]
  /\ res.[2] = _stavx2.[2] `^` u256_pack4 _pst.[10] _pst.[20] _pst.[5]  _pst.[15]
  /\ res.[3] = _stavx2.[3] `^` u256_pack4 _pst.[16] _pst.[7]  _pst.[23] _pst.[14]
  /\ res.[4] = _stavx2.[4] `^` u256_pack4 _pst.[11] _pst.[22] _pst.[8]  _pst.[19]
  /\ res.[5] = _stavx2.[5] `^` u256_pack4 _pst.[21] _pst.[17] _pst.[13] _pst.[9]
  /\ res.[6] = _stavx2.[6] `^` u256_pack4 _pst.[6]  _pst.[12] _pst.[18] _pst.[24]
 ] = 1%r.
proof. by conseq addpst23456_avx2_ll (addpst23456_avx2_h _pst _stavx2). qed.

(*
addpstate_avx2
*)
lemma addpstate_avx2_ll: islossless M._addpstate_avx2
by islossless.

hoare addpstate_avx2_h _pst _stavx2:
 M._addpstate_avx2
 : pst=_pst /\ st=_stavx2
 ==> res = stavx2_from_st25 (addstate _pst (stavx2_to_st25 _stavx2)).
proof.
admit (* BDEP *).
qed.

phoare addpstate_avx2_ph _pst _stavx2:
 [ M._addpstate_avx2
 : pst=_pst /\ st=_stavx2
 ==> res = stavx2_from_st25 (addstate _pst (stavx2_to_st25 _stavx2))
 ] = 1%r.
proof. by conseq addpstate_avx2_ll (addpstate_avx2_h _pst _stavx2). qed.

(*
stavx2_pos_avx2
*)

(*
addratebit_avx2
*)
lemma addratebit_avx2_ll: islossless M.__addratebit_avx2
 by islossless.

hoare addratebit_avx2_h _r8 _stavx2:
 M.__addratebit_avx2
 : st = _stavx2 /\ rATE8=_r8
 ==> res = stavx2_from_st25 (addratebit _r8 (stavx2_to_st25 _stavx2)).
proof.
admit (*BDEP*).
qed.

phoare addratebit_avx2_ph _r8 _stavx2:
 [ M.__addratebit_avx2
 : st = _stavx2 /\ rATE8=_r8
 ==> res = stavx2_from_st25 (addratebit _r8 (stavx2_to_st25 _stavx2))
 ] = 1%r.
proof. by conseq addratebit_avx2_ll (addratebit_avx2_h _r8 _stavx2). qed.
