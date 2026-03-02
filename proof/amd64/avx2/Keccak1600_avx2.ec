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

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200.
from JazzEC require import Array25 Array7.

require export Keccak_bindings.
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
by rewrite /stavx2_st0 /stavx2_from_st25 get_of_list 1:// /= /st0 !initiE 1..25:// !u256_pack4_zero.
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

op PABSORB1600 r8 m =
 stateabsorb (stateabsorb_iblocks (chunk r8 m) st0) (chunkremains r8 m).

op pabsorb_spec_avx2 r8 l (st: W256.t Array7.t): bool =
 0 < r8 <= 200 /\
 st=stavx2_from_st25 (PABSORB1600 r8 l).

lemma pabsorb_spec_avx2_nil r8:
 0 < r8 <= 200 =>
 pabsorb_spec_avx2 r8 [] stavx2_st0.
proof.
move=> Hr; rewrite /stavx2_st0 /pabsorb_spec_avx2 => />.
rewrite /PABSORB1600 chunk0 /= 1:/#.
by rewrite /stateabsorb_iblocks /= /chunkremains /= /stateabsorb bytes2state0 addstate_st0.
qed.

(*
lemma pabsorb_spec_avx2_cat r8 l1 l2 pst1 st1 pst2 st2:
 pabsorb_spec_avx2 r8 l1 st1 =>
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


lemma state_init_avx2_ll: islossless M.__state_init_avx2.
proof.
proc.
while true (7-i).
 by move=> z; auto => /> /#.
by auto => /#.
qed.

hoare state_init_avx2_h':
 M.__state_init_avx2
 : true
 ==> res = stavx2_st0.
proof.
proc.
unroll for ^while; auto => />.
by apply Array7.all_eq_eq; rewrite /all_eq /= !stavx2_st0P.
qed.

phoare state_init_avx2_ph':
 [ M.__state_init_avx2
 : true
 ==> res = stavx2_st0
 ] = 1%r.
proof. by conseq state_init_avx2_ll state_init_avx2_h'. qed.

hoare state_init_avx2_h _r8:
 M.__state_init_avx2
 :  0 < _r8 <= 200
 ==> pabsorb_spec_avx2 _r8 [] res.
proof.
conseq state_init_avx2_h'.
move=> _ Hr8 st ->.
by apply pabsorb_spec_avx2_nil.
qed.

phoare state_init_avx2_ph _r8:
 [ M.__state_init_avx2
 :  0 < _r8 <= 200
 ==> pabsorb_spec_avx2 _r8 [] res
 ] = 1%r.
proof. by conseq state_init_avx2_ll (state_init_avx2_h _r8). qed.


(*
perm_reg3456_avx2
*)

(*
unperm_reg3456_avx2
*)

(*
addstate_r3456_avx2
*)

(*
stavx2_pos_avx2
*)

(*
addratebit_avx2
*)
lemma addratebit_avx2_ll: islossless M.__addratebit_avx2
 by islossless.

op u256_set_u64 (w:W256.t) k (x:W64.t) =
 W256.init (fun i => if 64*k <= i < 64*(k+1) then x.[i-64*k] else w.[i]).

lemma w256_set_u64E w k x:
 u256_set_u64 w k x = pack4_t (W4u64.Pack.init (fun i => if i=k then x else w \bits64 i)).
proof.
apply W256.ext_eq => i Hi.
rewrite initiE //= pack4E initiE //= initiE 1:/# /=.
case: (i %/ 64 = k) => C.
 by rewrite ifT /#.
by rewrite ifF 1:/# bits64iE /#.
qed.

hoare u64_to_u256_h _k _w:
 M.__u64_to_u256
 : x = _w /\ l=_k /\ 0 <= _k < 4 ==> res = u256_set_u64 W256.zero _k _w.
proof.
proc; simplify.
case: (l=0).
 rcondt 1; first by auto => />.
 rcondt 3; first by auto => />.
 by auto => />; circuit.
case: (l=1).
 rcondf 1; first by auto => />.
 rcondt 4; first by auto => />.
 by auto => />; circuit.
case: (l=2).
 rcondt 1; first by auto => />.
 rcondf 3; first by auto => />.
 by auto => />; circuit.
case: (l=3).
 rcondf 1; first by auto => />.
 rcondf 4; first by auto => />.
 by auto => />; circuit.
conseq (: false ==> _).
 by move=> /> /#.
by auto.
qed.

op stavx2_pos n =
 nth (0,0) [(0,0);(1,0);(1,1);(1,2);(1,3);(2,2);(6,0);(3,1);(4,2);(5,3)
           ;(2,0);(4,0);(6,1);(5,2);(3,3);(2,3);(3,0);(5,1);(6,2);(4,3)
           ;(2,1);(5,0);(4,1);(3,2);(6,3) ] n.

hoare stavx2_pos_avx2_h _n:
 M.__stavx2_pos_avx2
 : pOS=_n ==> res = stavx2_pos _n.
proof.
proc. by auto => /> /#. qed.


lemma stavx2_posP st n r l x:
 stavx2INV st =>
 0 < n < 25 =>
 (r,l) = stavx2_pos n =>
 st.[r <- st.[r] `^` u256_set_u64 W256.zero l x]
 = stavx2_from_st25 (stavx2_to_st25 st).[n <- (stavx2_to_st25 st).[n] `^` x].
proof.
move=> Hinv H; have: n \in iota_ 1 24 by smt(mem_iota).
move: {H} n; rewrite -List.allP -iotaredE /stavx2_pos /= => />.
move: Hinv; circuit.
qed.

lemma stavx2_posP' (st: W64.t Array25.t) i x:
 0 < i < 25 =>
 stavx2_from_st25 (st.[i <- x])
 = (stavx2_from_st25 st).[(stavx2_pos i).`1 <- u256_set_u64 (stavx2_from_st25 st).[(stavx2_pos i).`1] (stavx2_pos i).`2 x].
proof.
rewrite tP => Hi k Hk.
have: i \in iota_ 1 24 by smt(mem_iota).
move: {Hi} i; rewrite -allP -iotaredE /=.
have: k \in iota_ 0 7 by smt(mem_iota).
move: {Hk} k; rewrite -allP -iotaredE /stavx2_pos /=.
by circuit.
qed.


lemma stavx2_pos0 n:
 0 <= n < 25 =>
 (stavx2_pos n).`1 = 0 =>
 n = 0
by smt().


lemma stavx2_pos0' stavx2 (st: W64.t Array25.t) x:
 stavx2 = stavx2_from_st25 st =>
 stavx2.[0 <- stavx2.[0] `^` VPBROADCAST_4u64 x]
 = stavx2_from_st25 (st.[0 <- st.[0] `^` x]).
proof. by circuit. qed.

abbrev u64_bitswap i (w:W64.t) = w `^` (W64.one `<<` (W8.of_int i)).


lemma u64_xorbitE i w:
 0 <= i < 64 =>
 u64_xorbit i w = u64_bitswap i w.
move=> Hi; apply W64.ext_eq => k Hk.
rewrite !initiE // xorwE shlwE of_uintK modz_small 1:/# Hk /=.
by rewrite nth_one /#.
qed.



hoare addratebit_avx2_h _r8 _stavx2:
 M.__addratebit_avx2
 : st = _stavx2 /\ rATE_8=_r8 /\ 0 < _r8 <= 200 /\ stavx2INV st
 ==> res = stavx2_from_st25 (addratebit _r8 (stavx2_to_st25 _stavx2)).
proof.
proc; simplify.
sp.
seq 1: (#pre /\ (r,l) = stavx2_pos ((rATE_8 - 1) %/ 8)).
 by ecall (stavx2_pos_avx2_h ((rATE_8 - 1) %/ 8)); auto => /> /#.
case: (r=0).
 rcondt 1; first by auto.
 auto => |> &m  ??Hinv H.
 have := stavx2_pos0 ((_r8 - 1) %/ 8) _; first smt().
 rewrite -H /= => {H} H.
 rewrite (stavx2_pos0' _ (stavx2_to_st25 _stavx2)).
  admit.
 pose x:= (W64.one `<<` W8.of_int ((8 * _r8 - 1) %% 64)).
 congr.
 move: (Top.stavx2_to_st25 _stavx2) => _s.
 rewrite /addratebit /addratebit8 -stbytesK.
 apply stbytes_inj; rewrite !stwordsK tP => i Hi.
 rewrite initiE 1:/# /= initiE 1:/# get_setE // get_setE 1:/# /=.
 case: (i%/8=0) => C1.
  case: (i=_r8-1) => C2.
   rewrite -C2 C1 xorb8E; congr.
   admit.
  rewrite xorb8E initiE //= C1. 
   have ->: (x \bits8 i %% 8) = W8.zero. admit.
   smt().
 case: (i=_r8-1) => ?; first smt().
 by rewrite initiE //=. 
rcondf 1; first by auto.
wp; ecall (u64_to_u256_h l t64); auto => |> &m ??Hinv H ?.
split.
 admit.
move=> ??.
rewrite (stavx2_posP _stavx2 ((_r8 - 1) %/ 8) r{m} l{m} _ Hinv _ H). admit.
rewrite /addratebit -addratebitE 1:/#.
congr.
move: H; rewrite u64_xorbitE /#.
qed.

phoare addratebit_avx2_ph _r8 _stavx2:
 [ M.__addratebit_avx2
 : st = _stavx2 /\ rATE_8=_r8 /\ 0 < _r8 <= 200 /\ stavx2INV st
 ==> res = stavx2_from_st25 (addratebit _r8 (stavx2_to_st25 _stavx2))
 ] = 1%r.
proof. by conseq addratebit_avx2_ll (addratebit_avx2_h _r8 _stavx2). qed.
