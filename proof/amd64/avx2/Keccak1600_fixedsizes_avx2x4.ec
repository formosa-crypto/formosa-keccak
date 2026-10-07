(******************************************************************************
   Keccak1600_fixedsizes_avx2x4.ec:

   Correctness proof for the Keccak (fixed-sized) absorb/squeeze
  4-way AVX2 implementation



******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.

from JazzEC require import WArray200 WArray800.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccak1600_Spec.


require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Avx2_extra.
require import Keccak1600_subreadwrite.
require import Keccak1600_statebytes.

(* ------------------------------------------------------------------------ *)
(* Lane view.  The 4-way code is the ref code acting on the four 64-bit      *)
(* lanes of a W256.t Array25.t: the proofs below are the ref proofs read on  *)
(* each lane (st4x_get st k), with the four inputs as the lanes' inputs.     *)
(* ------------------------------------------------------------------------ *)

lemma forall4 (P: int -> bool):
 (forall k, 0 <= k < 4 => P k) <=> (P 0 /\ P 1 /\ P 2 /\ P 3).
proof.
split; first by move=> H; smt().
move=> [H0 [H1 [H2 H3]]] k Hk.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

lemma pabsorb_spec_avx2x4E r8 (l0 l1 l2 l3: W8.t list) (st4: state4x):
 pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 st4
 <=> size l1 = size l0 /\ size l2 = size l0 /\ size l3 = size l0
     /\ forall k, 0 <= k < 4 => pabsorb_spec r8 (nth [] [l0; l1; l2; l3] k) (st4x_get st4 k).
proof.
rewrite forall4 /= /pabsorb_spec_avx2x4 /pabsorb_spec /st4x_match.
split.
 move=> [Hr [H1 [H2 [H3 ->]]]].
 by rewrite st4x_get_pack0 st4x_get_pack1 st4x_get_pack2 st4x_get_pack3 /= Hr H1 H2 H3.
move=> [H1 [H2 [H3 [[Hr E0] [[_ E1] [[_ E2] [_ E3]]]]]]].
rewrite Hr H1 H2 H3 /= -E0 -E1 -E2 -E3.
by have := st4x_unpackK st4; rewrite /st4x_unpack => ->.
qed.

lemma absorb_spec_avx2x4E r8 tb (l0 l1 l2 l3: W8.t list) (st4: state4x):
 absorb_spec_avx2x4 r8 tb l0 l1 l2 l3 st4
 <=> forall k, 0 <= k < 4 => st4x_get st4 k = ABSORB1600 (W8.of_int tb) r8 (nth [] [l0; l1; l2; l3] k).
proof.
rewrite forall4 /= /absorb_spec_avx2x4 /st4x_match; split.
 by move=> ->; rewrite st4x_get_pack0 st4x_get_pack1 st4x_get_pack2 st4x_get_pack3.
move=> [E0 [E1 [E2 E3]]]; rewrite -E0 -E1 -E2 -E3.
by have := st4x_unpackK st4; rewrite /st4x_unpack => ->.
qed.

(* one __addstate call on every lane, lane k reading the input list nth [] ls k *)
op addstate_spec4 (st4: state4x) at (ls: W8.t list list) tb sz cur0 cur' (st4': state4x) at' len' tb' =
 forall k, 0 <= k < 4 =>
  addstate_spec (st4x_get st4 k) at (nth [] ls k) tb sz cur0 cur' (st4x_get st4' k) at' len' tb'.

lemma addstate_spec4_init (st4: state4x) at ls tb sz cur0 n:
 0 <= sz <= at => (forall k, 0 <= k < 4 => size (nth [] ls k) = n) =>
 addstate_spec4 st4 at ls tb sz cur0 cur0 st4 at n tb.
proof. by move=> Hsz Hn k Hk; apply addstate_spec_init => //; rewrite Hn. qed.

(* the stores of the 4-way code, lane by lane: 64-bit word q is lane q%%4 of
   256-bit word q%/4 *)
lemma st4x_get_xor64 (st: state4x) q t k:
 0 <= q < 100 => 0 <= k < 4 =>
 st4x_get (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q) `^` t)))) k
 = if q %% 4 = k then addstate_at (st4x_get st k) (8*(q %/ 4)) (u64bytes t) else st4x_get st k.
proof.
move=> Hq Hk; rewrite st4x_get_set64 // get64_init256 //.
case: (q %% 4 = k) => C //.
by rewrite -setw_addstate_at 1:/# st4x_getiE 1,2:/# C.
qed.

lemma st4x_get_xor64x4 (st: state4x) j q0 q1 q2 q3 (t0 t1 t2 t3: W64.t) k:
 0 <= j < 25 => q0 = 4*j => q1 = 4*j+1 => q2 = 4*j+2 => q3 = 4*j+3 => 0 <= k < 4 =>
 st4x_get (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) `^` t1)))))) (8*q2) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) `^` t1)))))) (8*q2) `^` t2)))))) (8*q3) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) `^` t1)))))) (8*q2) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) (get64_direct (WArray800.init256 ("_.[_]" st)) (8*q0) `^` t0)))))) (8*q1) `^` t1)))))) (8*q2) `^` t2)))))) (8*q3) `^` t3)))) k
 = addstate_at (st4x_get st k) (8*j) (u64bytes (nth W64.zero [t0; t1; t2; t3] k)).
proof.
move=> Hj -> -> -> -> Hk.
rewrite !st4x_get_xor64 1..8:/#.
have E: forall c, 0 <= c < 4 => (4*j+c) %% 4 = c /\ (4*j+c) %/ 4 = j by smt().
have [E00 E01] : (4*j) %% 4 = 0 /\ (4*j) %/ 4 = j by smt().
have [E10 E11] := E 1 _ => //; have [E20 E21] := E 2 _ => //; have [E30 E31] := E 3 _ => //.
rewrite E00 E01 E10 E11 E20 E21 E30 E31.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

lemma st4x_get_xorbcast (st: state4x) j t k:
 0 <= j < 25 => 0 <= k < 4 =>
 st4x_get st.[j <- VPBROADCAST_4u64 t `^` st.[j]] k = addstate_at (st4x_get st k) (8*j) (u64bytes t).
proof.
move=> Hj Hk; rewrite st4x_get_set // xorb64E VPBROADCAST_4u64_bits64 // -st4x_getiE //.
by rewrite xorwC setw_addstate_at.
qed.

(* the __addstate_bcast_avx2x4 loop/final store (byte offset q = 32*j) *)
lemma st4x_get_xorbcast256 (st: state4x) q j t k:
 0 <= j < 25 => q = 32*j => 0 <= k < 4 =>
 st4x_get (Array25.init (WArray800.get256 (WArray800.set256_direct (WArray800.init256 ("_.[_]" st)) q
             (VPBROADCAST_4u64 t `^` get256_direct (WArray800.init256 ("_.[_]" st)) q)))) k
 = addstate_at (st4x_get st k) (8*j) (u64bytes t).
proof. by move=> Hj -> Hk; rewrite get256_init256 // init256_set256 // st4x_get_xorbcast. qed.

lemma nth4_const (x0 x: 'a) k: 0 <= k < 4 => nth x0 [x; x; x; x] k = x.
proof.
move=> Hk; have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

(* the __dumpstate_avx2x4 loads: byte offset 4*i (+ lane/word shift) of the
   WArray800 view, for a position i (in bytes, per lane) multiple of 8 *)
lemma get256_init256_at (st: state4x) o j:
 0 <= j < 25 => o = 32 * j =>
 get256_direct (WArray800.init256 ("_.[_]" st)) o = st.[j].
proof. by move=> Hj ->; rewrite get256_init256. qed.

lemma get64_init256_at (st: state4x) o i k:
 0 <= i < 200 => i %% 8 = 0 => 0 <= k < 4 => o = 4 * i + 8 * k =>
 get64_direct (WArray800.init256 ("_.[_]" st)) o = st.[i %/ 8] \bits64 k.
proof.
move=> Hi Hm Hk ->; rewrite (_: 4 * i + 8 * k = 8 * (i %/ 2 + k)) 1:/# get64_init256 1:/#.
by congr; smt().
qed.

(* ---- absorb on the four lanes, shared by the array and the memory variants:
   the inputs are lists (to_list buf_k, or memread mem buf_k len) ---- *)

(* lane k of an __addstate result: chunk k (and the trailing byte) added at `at` *)
op addstate_lanes (st: state4x) at (cs: W8.t list list) tb (stc: state4x) =
 forall k, 0 <= k < 4 => st4x_get stc k
    = addstate_at (st4x_get st k) at (nth [] cs k ++ if tb <> 0 then [W8.of_int tb] else []).

(* the absorb invariant: lane k has absorbed its prefix and the first n bytes of input k *)
op pabsorb4 r8 (ls ins: W8.t list list) n (st: state4x) =
 forall k, 0 <= k < 4 => pabsorb_spec r8 (nth [] ls k ++ take n (nth [] ins k)) (st4x_get st k).

lemma pabsorb4_init r8 (l0 l1 l2 l3: W8.t list) ins (st: state4x):
 pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 st => pabsorb4 r8 [l0; l1; l2; l3] ins 0 st.
proof.
rewrite pabsorb_spec_avx2x4E => [#] _ _ _ H k Hk.
by rewrite take0 cats0; apply H.
qed.

lemma pabsorb4_r8 r8 ls ins n (st: state4x): pabsorb4 r8 ls ins n st => 0 < r8 <= 200.
proof. by move=> H; move: (H 0 _) => //; rewrite /pabsorb_spec => [#]. qed.

(* complete the current block on every lane (pabsorb_fill) *)
lemma pabsorb4_fill r8 s (ls: W8.t list list) (i0 i1 i2 i3: W8.t list) n m a (st st': state4x):
 0 <= n => a = (s + n) %% r8 => m = r8 - a => n + m <= size i0 =>
 size i1 = size i0 => size i2 = size i0 => size i3 = size i0 =>
 (forall k, 0 <= k < 4 => size (nth [] ls k) = s) =>
 pabsorb4 r8 ls [i0; i1; i2; i3] n st =>
 addstate_lanes st a
   [take m (drop n i0); take m (drop n i1); take m (drop n i2); take m (drop n i3)] 0 st' =>
 pabsorb4 r8 ls [i0; i1; i2; i3] (n + m) (st4x_map keccak_f1600_op st').
proof.
move=> Hn -> Em Hfit S1 S2 S3 Hs H Hst k Hk.
have Hr8 := pabsorb4_r8 _ _ _ _ _ H.
have Ha0: 0 <= (s + n) %% r8 < r8 by smt(modz_ge0 ltz_pmod).
rewrite st4x_get_map // Hst // addstate_at_bytes 1:/#.
move: (H k Hk) (Hs k Hk).
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /= Hk' Hsk; rewrite Em -Hsk;
   apply (pabsorb_fill r8 _ _ n _ Hn _ Hk'); smt().
qed.

(* the last (partial) block on every lane (pabsorb_last) *)
lemma pabsorb4_last r8 s (ls: W8.t list list) (i0 i1 i2 i3: W8.t list) n m a (st st': state4x) tb:
 0 <= n <= size i0 => m = size i0 - n => a = (s + n) %% r8 =>
 size i1 = size i0 => size i2 = size i0 => size i3 = size i0 =>
 a + m < r8 =>
 (forall k, 0 <= k < 4 => size (nth [] ls k) = s) =>
 pabsorb4 r8 ls [i0; i1; i2; i3] n st =>
 addstate_lanes st a
   [take m (drop n i0); take m (drop n i1); take m (drop n i2); take m (drop n i3)] tb st' =>
 (tb <> 0 => forall k, 0 <= k < 4 =>
    addratebit r8 (st4x_get st' k) = ABSORB1600 (W8.of_int tb) r8 (nth [] ls k ++ nth [] [i0; i1; i2; i3] k))
 /\ (tb = 0 => forall k, 0 <= k < 4 =>
    pabsorb_spec r8 (nth [] ls k ++ nth [] [i0; i1; i2; i3] k) (st4x_get st' k)).
proof.
move=> Hn Em -> S1 S2 S3 Hfit Hs H Hst.
have Hr8 := pabsorb4_r8 _ _ _ _ _ H.
have Hl: forall k, 0 <= k < 4 =>
  st4x_get st' k = addstate (st4x_get st k)
    (bytes2state (u8zeros ((s + n) %% r8) ++ drop n (nth [] [i0; i1; i2; i3] k) ++ [W8.of_int tb])).
 move=> k Hk; rewrite Hst // addstate_at_bytes 1:/#.
 have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
 by case => [->|[->|[->|->]]] /=; rewrite Em take_oversize // size_drop //; smt().
split => Htb k Hk; rewrite Hl //; move: (H k Hk) (Hs k Hk).
+ have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
  by case => [->|[->|[->|->]]] /= Hk' Hsk; rewrite -Hsk;
     have [H1 _] := pabsorb_last r8 _ _ n _ tb _ _ Hk'; smt().
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /= Hk' Hsk; rewrite -Hsk;
   have [_ H0] := pabsorb_last r8 _ _ n _ tb _ _ Hk'; smt().
qed.

lemma nth_lcat4 (l0 l1 l2 l3 i0 i1 i2 i3: W8.t list) k: 0 <= k < 4 =>
 nth [] [l0 ++ i0; l1 ++ i1; l2 ++ i2; l3 ++ i3] k
 = nth [] [l0; l1; l2; l3] k ++ nth [] [i0; i1; i2; i3] k.
proof.
move=> Hk; have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

(* ---- memory: lane k reads memread mem b_k len, with its own cursor c_k
   (the pointer buf_k); the ref memory proofs read on each lane ---- *)

op addstate_spec4m (st4: state4x) at mem (bs: int list) len tb sz (cs: int list) (st4': state4x) at' len' tb' =
 forall k, 0 <= k < 4 =>
  addstate_spec (st4x_get st4 k) at (memread mem (nth 0 bs k) len) tb sz (nth 0 bs k) (nth 0 cs k)
                (st4x_get st4' k) at' len' tb'.

(* the result of __addstate_m on the four lanes *)
op addstate_res4m (st: state4x) at mem (b0 b1 b2 b3: int) len tb (stc: state4x) at1 (c0 c1 c2 c3: int) =
 addstate_lanes st at [memread mem b0 len; memread mem b1 len; memread mem b2 len; memread mem b3 len] tb stc
 /\ at1 = at + len + b2i (tb <> 0)
 /\ c0 = b0 + len /\ c1 = b1 + len /\ c2 = b2 + len /\ c3 = b3 + len.

lemma addstate_spec4m_init (st: state4x) at mem bs len tb sz:
 0 <= sz <= at => 0 <= len => addstate_spec4m st at mem bs len tb sz bs st at len tb.
proof. by move=> Hsz Hl k Hk; apply addstate_spec_init => //; smt(size_memread). qed.

(* the bookkeeping of a read depends on the control arguments only *)
lemma msubread_same mem mem' (lw lw': W8.t list) cur at off off' len tb a o l t a' o' l' t':
 size lw = size lw' =>
 msubread mem lw cur at off len tb a o l t =>
 msubread mem' lw' cur at off' len tb a' o' l' t' =>
 msubread mem lw cur at off len tb a' o l' t'.
proof.
rewrite /msubread => Hs [Hsr [_ [Eo [_ _]]]] [_ [-> [_ [-> ->]]]].
by rewrite Hsr Eo Hs.
qed.

lemma addstate_spec4m_msubread mem bs (ws: W64.t list) cur (st: state4x) at len tb (stc stc': state4x)
                               at0 cs len0 tb0 cur1 at1 cs1 len1 tb1:
 0 <= at => 0 <= len => 0 <= tb < 256 =>
 0 <= cur <= at0 < cur+8 => cur1 = cur + 8 =>
 (forall k, 0 <= k < 4 => st4x_get stc' k = addstate_at (st4x_get stc k) cur (u64bytes (nth W64.zero ws k))) =>
 (forall k, 0 <= k < 4 => msubread mem (u64bytes (nth W64.zero ws k)) cur at0 (nth 0 cs k) len0 tb0 at1 (nth 0 cs1 k) len1 tb1) =>
 addstate_spec4m st at mem bs len tb cur cs stc at0 len0 tb0 =>
 addstate_spec4m st at mem bs len tb cur1 cs1 stc' at1 len1 tb1.
proof.
move=> Hat Hlen Htb Hc Hc1 Hst Hr H k Hk.
rewrite Hst //.
exact (addstate_msubread_u64 mem (nth W64.zero ws k) cur (st4x_get st k) at (nth 0 bs k) len tb
         (st4x_get stc k) at0 (nth 0 cs k) len0 tb0 cur1 at1 (nth 0 cs1 k) len1 tb1
         Hat Hlen Htb Hc Hc1 (H k Hk) (Hr k Hk)).
qed.

lemma addstate_spec4m_fullword mem bs sz (st: state4x) at len tb (stc stc': state4x) (c0 c1 c2 c3: int) at0 len0 tb0:
 0 <= at => 0 <= tb < 256 => at <= sz => 8 <= len0 => 0 <= len =>
 (forall k, 0 <= k < 4 => st4x_get stc' k
    = addstate_at (st4x_get stc k) at0 (u64bytes (loadW64 mem (nth 0 [c0; c1; c2; c3] k)))) =>
 addstate_spec4m st at mem bs len tb sz [c0; c1; c2; c3] stc at0 len0 tb0 =>
 addstate_spec4m st at mem bs len tb (sz + 8) [c0 + 8; c1 + 8; c2 + 8; c3 + 8] stc' (at0 + 8) (len0 - 8) tb0.
proof.
move=> Hat Htb Hsz Hl0 Hlen Hst H k Hk.
have Ec: nth 0 [c0 + 8; c1 + 8; c2 + 8; c3 + 8] k = nth 0 [c0; c1; c2; c3] k + 8.
 have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
 by case => [->|[->|[->|->]]].
rewrite Hst // Ec.
have Hs: size (u64bytes (loadW64 mem (nth 0 [c0; c1; c2; c3] k))) = 8 by rewrite /u64bytes size_to_list.
apply (addstate_spec_fullword _ _ sz (st4x_get st k) at tb (st4x_get stc k) (nth 0 bs k)
         (nth 0 [c0; c1; c2; c3] k) at0 len0 tb0) => //; rewrite ?Hs //.
+ exact (H k Hk).
by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ (H k Hk)) //; apply loadW64_memread; smt().
qed.

lemma addstate_spec4m_finish mem (b0 b1 b2 b3: int) (ws: W64.t list) sz (st: state4x) at len tb (stc stc': state4x)
                             (c0 c1 c2 c3: int) at0 len0 tb0 at1 (d0 d1 d2 d3: int) len1 tb1:
 0 <= at => 0 <= tb < 256 => at <= sz => 0 <= len =>
 len0 < 8 => (0 < len0 \/ tb0 <> 0) =>
 (forall k, 0 <= k < 4 => st4x_get stc' k = addstate_at (st4x_get stc k) at0 (u64bytes (nth W64.zero ws k))) =>
 (forall k, 0 <= k < 4 => msubread mem (u64bytes (nth W64.zero ws k)) at0 at0 (nth 0 [c0; c1; c2; c3] k) len0 tb0
                                    at1 (nth 0 [d0; d1; d2; d3] k) len1 tb1) =>
 addstate_spec4m st at mem [b0; b1; b2; b3] len tb sz [c0; c1; c2; c3] stc at0 len0 tb0 =>
 addstate_res4m st at mem b0 b1 b2 b3 len tb stc' at1 d0 d1 d2 d3.
proof.
move=> Hat Htb Hsz Hlen Hl0 Hg Hst Hr H.
have Hl: forall k, 0 <= k < 4 =>
   addstate_at (st4x_get stc k) at0 (u64bytes (nth W64.zero ws k))
   = addstate_at (st4x_get st k) at (memread mem (nth 0 [b0; b1; b2; b3] k) len ++ if tb <> 0 then [W8.of_int tb] else [])
   /\ at1 = at + len + b2i (tb <> 0) /\ nth 0 [d0; d1; d2; d3] k = nth 0 [b0; b1; b2; b3] k + len.
 move=> k Hk.
 have Hs: size (u64bytes (nth W64.zero ws k)) = 8 by rewrite /u64bytes size_to_list.
 have Hk' := H k Hk.
 move: (Hr k Hk); rewrite /msubread Hs => [#] Hsr Eat Ebuf _ _.
 apply (addstate_spec_finish (memread mem (nth 0 [b0; b1; b2; b3] k) len) (u64bytes (nth W64.zero ws k)) len sz
          (st4x_get st k) at tb (st4x_get stc k) (nth 0 [b0; b1; b2; b3] k) (nth 0 [c0; c1; c2; c3] k)
          at0 len0 tb0 at1 (nth 0 [d0; d1; d2; d3] k)) => //.
 + by rewrite size_memread.
 by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ Hk').
have [_ [Eat _]] := Hl 0 _ => //.
have [_ [_ /= E0]] := Hl 0 _ => //.
have [_ [_ /= E1]] := Hl 1 _ => //.
have [_ [_ /= E2]] := Hl 2 _ => //.
have [_ [_ /= E3]] := Hl 3 _ => //.
rewrite /addstate_res4m Eat E0 E1 E2 E3 /=.
move=> k Hk; rewrite Hst //; have [-> _] := Hl k Hk.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

lemma addstate_spec4m_done mem (b0 b1 b2 b3: int) sz (st: state4x) at len tb (stc: state4x) (c0 c1 c2 c3: int) at0 tb0:
 0 <= at => 0 <= tb < 256 => tb0 %% 256 = 0 => 0 <= len =>
 addstate_spec4m st at mem [b0; b1; b2; b3] len tb sz [c0; c1; c2; c3] stc at0 0 tb0 =>
 addstate_res4m st at mem b0 b1 b2 b3 len tb stc at0 c0 c1 c2 c3.
proof.
move=> Hat Htb Htb0 Hlen H.
have Hl: forall k, 0 <= k < 4 =>
   st4x_get stc k = addstate_at (st4x_get st k) at (memread mem (nth 0 [b0; b1; b2; b3] k) len ++ if tb <> 0 then [W8.of_int tb] else [])
   /\ at0 = at + len + b2i (tb <> 0) /\ nth 0 [c0; c1; c2; c3] k = nth 0 [b0; b1; b2; b3] k + len.
 move=> k Hk.
 by apply (addstate_spec_done (memread mem (nth 0 [b0; b1; b2; b3] k) len) len sz (st4x_get st k) at tb
             (st4x_get stc k) (nth 0 [b0; b1; b2; b3] k) (nth 0 [c0; c1; c2; c3] k) at0 tb0 _ Hat Htb Htb0 (H k Hk));
    rewrite size_memread.
have [_ [Eat _]] := Hl 0 _ => //.
have [_ [_ /= E0]] := Hl 0 _ => //.
have [_ [_ /= E1]] := Hl 1 _ => //.
have [_ [_ /= E2]] := Hl 2 _ => //.
have [_ [_ /= E3]] := Hl 3 _ => //.
rewrite /addstate_res4m Eat E0 E1 E2 E3 /=.
move=> k Hk; have [-> _] := Hl k Hk.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

(* the addstate result, lane by lane, as chunks of the input lists *)
lemma addstate_res4m_lanes (st: state4x) at mem (b0 b1 b2 b3: int) blen (p0 p1 p2 p3: int) n m tb (stc: state4x) at1 c0 c1 c2 c3:
 0 <= n => 0 <= m => n + m <= blen =>
 p0 = b0 + n => p1 = b1 + n => p2 = b2 + n => p3 = b3 + n =>
 addstate_res4m st at mem p0 p1 p2 p3 m tb stc at1 c0 c1 c2 c3 =>
 addstate_lanes st at [take m (drop n (memread mem b0 blen)); take m (drop n (memread mem b1 blen));
                       take m (drop n (memread mem b2 blen)); take m (drop n (memread mem b3 blen))] tb stc.
proof.
move=> Hn Hm Hnm -> -> -> -> [Hl _] k Hk; rewrite Hl //.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /=; rewrite slice_memread.
qed.

(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_m_bcast_avx2x4_ll: islossless M.__addstate_m_bcast_avx2x4.
proof.
proc.
seq 5: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.

lemma addstate_m_avx2x4_ll: islossless M.__addstate_m_avx2x4.
proof.
proc.
seq 5: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
by auto => /#.
qed.

hoare addstate_m_avx2x4_h _mem _st _at _buf0 _buf1 _buf2 _buf3 _len _tb:
 M.__addstate_m_avx2x4
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _tb < 256
 ==> Glob.mem = _mem
     /\ addstate_res4m _st _at _mem _buf0 _buf1 _buf2 _buf3 _len _tb res.`1 res.`2 res.`3 res.`4 res.`5 res.`6.
proof.
(* addstate_avx2x4_h with the pointers buf_k as the lanes' cursors *)
proc => /=.
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 3: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] _len _tb nbase [buf0; buf1; buf2; buf3] st aT _LEN _TRAILB).
+ seq 2: (Glob.mem = _mem /\ st = _st /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
          /\ _LEN = _len /\ _TRAILB = _tb
          /\ 0 <= _at <= 200 /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _tb < 256
          /\ aT8 = _at /\ aT = 8 * (_at %/ 8)); first by auto.
  if.
  - wp; ecall (m_ilen_read_upto8_at_h buf3 _LEN _TRAILB aT aT8).
    wp; ecall (m_ilen_read_upto8_at_h buf2 _LEN _TRAILB aT aT8).
    wp; ecall (m_ilen_read_upto8_at_h buf1 _LEN _TRAILB aT aT8).
    wp; ecall (m_ilen_read_upto8_at_h buf0 _LEN _TRAILB aT aT8).
    auto => |> Hat0 Hat1 Hlen Hal Htb0 Htb1 Hnal r0 H0 r1 H1 r2 H2 r3 H3.
    apply (addstate_spec4m_msubread _mem [_buf0; _buf1; _buf2; _buf3] [r0.`5; r1.`5; r2.`5; r3.`5] (8 * (_at %/ 8))
             _st _at _len _tb _st _ _at [_buf0; _buf1; _buf2; _buf3] _len _tb nbase r3.`4
             [r0.`1; r1.`1; r2.`1; r3.`1] r3.`2 r3.`3) => //.
    + smt().
    + by rewrite /nbase; smt().
    + by move=> k Hk; rewrite (st4x_get_xor64x4 _st (_at %/ 8)) //; smt().
    + have Hs: forall (w w': W64.t), size (u64bytes w) = size (u64bytes w') by move=> w w'; rewrite /u64bytes !size_to_list.
      rewrite forall4 /=.
      split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H0 H3).
      split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H1 H3).
      split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H2 H3).
      exact H3.
    by apply addstate_spec4m_init => //; smt().
  auto => |> Hat0 Hat1 Hlen Hal Htb0 Htb1 Hal8.
  have ->: nbase = 8 * (_at %/ 8) by rewrite /nbase; smt().
  have ->: 8 * (_at %/ 8) = _at by smt().
  by apply addstate_spec4m_init; smt().
(* word loop: word `at %/ 4` of each lane; the spec advances by 8 bytes per iteration *)
seq 2: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ 0 <= _LEN /\ at = 4 * (aT %/ 8) + 4 * (_LEN %/ 8)
       /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] _len _tb (nbase + 8 * (_LEN %/ 8)) [buf0; buf1; buf2; buf3] st (aT + 8 * (_LEN %/ 8)) (_LEN - 8 * (_LEN %/ 8)) _TRAILB).
+ while (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
         /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
         /\ 0 <= _LEN /\ at %% 4 = 0 /\ aT %/ 8 <= at %/ 4 <= aT %/ 8 + _LEN %/ 8
         /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] _len _tb (nbase + 8 * (at %/ 4 - aT %/ 8)) [buf0; buf1; buf2; buf3] st (aT + 8 * (at %/ 4 - aT %/ 8)) (_LEN - 8 * (at %/ 4 - aT %/ 8)) _TRAILB).
  + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL Ha4 H1 H2 H Hb.
    split; first smt().
    split; first smt().
    pose d := at{m} %/ 4 - aT{m} %/ 8.
    move: (H 0 _) => //= Hk0.
    have Hd0: 0 <= d by smt().
    have Hl8: 8 <= _LEN{m} - 8 * d by smt().
    have Ea: aT{m} + 8 * d = nbase + 8 * d.
     by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    have Hfit: aT{m} + 8 * d + (_LEN{m} - 8 * d) = _at + size (memread _mem _buf0 _len).
     by apply (addstate_spec_fit _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    rewrite size_memread // in Hfit.
    have Hal8: aT{m} + 8 * d = 8 * (at{m} %/ 4) by move: Ea; rewrite /d /nbase; smt().
    rewrite (_: (at{m} + 4) %/ 4 - aT{m} %/ 8 = d + 1) 1:/#.
    rewrite (_: nbase + 8 * (d + 1) = (nbase + 8 * d) + 8) 1:/# (_: aT{m} + 8 * (d + 1) = (aT{m} + 8 * d) + 8) 1:/# (_: _LEN{m} - 8 * (d + 1) = (_LEN{m} - 8 * d) - 8) 1:/#.
    apply (addstate_spec4m_fullword _mem [_buf0; _buf1; _buf2; _buf3] (nbase + 8 * d) _st _at _len _tb st{m} _
             buf0{m} buf1{m} buf2{m} buf3{m} (aT{m} + 8 * d) (_LEN{m} - 8 * d) _TRAILB{m}) => //.
    + smt().
    move=> k Hk; rewrite Hal8.
    have Hk4: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
    by case: Hk4 => [->|[->|[->|->]]] /=; rewrite (st4x_get_xor64x4 st{m} (at{m} %/ 4)) //; smt().
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal H.
  have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ (H 0 _) => //; smt().
  have E: 4 * (aT{m} %/ 8) %/ 4 - aT{m} %/ 8 = 0 by smt().
  rewrite E /=; split.
  + split; first smt().
    split; first smt().
    split; first smt().
    exact H.
  move=> at0 b0 b1 b2 b3 st0 Hex _ Ha H1 H2 Hs.
  have E2: at0 %/ 4 - aT{m} %/ 8 = _LEN{m} %/ 8 by smt().
  split; first smt().
  by move: Hs; rewrite E2.
(* bookkeeping; when the last word is read, aT is aligned and `at` is its word index *)
seq 2: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ 0 <= _LEN < 8
       /\ exists sz, _at <= sz
          /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] _len _tb sz [buf0; buf1; buf2; buf3] st aT _LEN _TRAILB
          /\ (aT = sz => aT %% 8 = 0 /\ at = 4 * (aT %/ 8))).
+ auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL H.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  split; first by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
  by rewrite /nbase; smt().
if.
+ wp; ecall (m_ilen_read_upto8_at_h buf3 _LEN _TRAILB aT aT).
  wp; ecall (m_ilen_read_upto8_at_h buf2 _LEN _TRAILB aT aT).
  wp; ecall (m_ilen_read_upto8_at_h buf1 _LEN _TRAILB aT aT).
  wp; ecall (m_ilen_read_upto8_at_h buf0 _LEN _TRAILB aT aT).
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL0 HL1 sz Hsz H Hal8 Hg r0 H0 r1 H1 r2 H2 r3 H3.
  move: (H 0 _) => //= Hk0.
  have Ea: aT{m} = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ Hk0); smt().
  have [Ha8 Ea4] := Hal8 Ea.
  have Hab: aT{m} < 200 by move: Hk0; rewrite /addstate_spec size_memread //; smt().
  apply (addstate_spec4m_finish _mem _buf0 _buf1 _buf2 _buf3 [r0.`5; r1.`5; r2.`5; r3.`5] sz _st _at _len _tb
           st{m} _ buf0{m} buf1{m} buf2{m} buf3{m} aT{m} _LEN{m} _TRAILB{m} r3.`4 r0.`1 r1.`1 r2.`1 r3.`1 r3.`2 r3.`3) => //.
  + smt().
  + by move=> k Hk; rewrite (st4x_get_xor64x4 st{m} (aT{m} %/ 8)) //; smt().
  have Hs: forall (w w': W64.t), size (u64bytes w) = size (u64bytes w') by move=> w w'; rewrite /u64bytes !size_to_list.
  rewrite forall4 /=.
  split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H0 H3).
  split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H1 H3).
  split; first exact (msubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H2 H3).
  exact H3.
(* nothing left: the stream and the trailing byte are already absorbed *)
auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL0 HL1 sz Hsz H _ Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec4m_done _mem _buf0 _buf1 _buf2 _buf3 sz _st _at _len _tb st{m} buf0{m} buf1{m} buf2{m} buf3{m} aT{m} _TRAILB{m}) => //; smt().
qed.

hoare addstate_m_bcast_avx2x4_h _mem _st _at _buf _len _tb:
 M.__addstate_m_bcast_avx2x4
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _tb < 256
 ==> Glob.mem = _mem
     /\ addstate_res4m _st _at _mem _buf _buf _buf _buf _len _tb res.`1 res.`2 res.`3 res.`3 res.`3 res.`3.
proof.
(* addstate_m_avx2x4_h with the same (broadcast) word on every lane *)
proc => /=.
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 3: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] _len _tb nbase [buf; buf; buf; buf] st aT _LEN _TRAILB).
+ seq 2: (Glob.mem = _mem /\ st = _st /\ buf = _buf /\ _LEN = _len /\ _TRAILB = _tb
          /\ 0 <= _at <= 200 /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _tb < 256
          /\ aT8 = _at /\ aT = 8 * (_at %/ 8)); first by auto.
  if.
  - wp; ecall (m_ilen_read_bcast_upto8_at_h buf _LEN _TRAILB aT aT8).
    auto => |> Hat0 Hat1 Hlen Hal Htb0 Htb1 Hnal r t Et H.
    rewrite Et (_: 8 * (_at %/ 8) %/ 8 = _at %/ 8) 1:/#.
    apply (addstate_spec4m_msubread _mem [_buf; _buf; _buf; _buf] [t; t; t; t] (8 * (_at %/ 8))
             _st _at _len _tb _st _ _at [_buf; _buf; _buf; _buf] _len _tb nbase r.`4
             [r.`1; r.`1; r.`1; r.`1] r.`2 r.`3) => //.
    + smt().
    + by rewrite /nbase; smt().
    + by move=> k Hk; rewrite nth4_const // st4x_get_xorbcast //; smt().
    + by move=> k Hk; rewrite !nth4_const.
    by apply addstate_spec4m_init => //; smt().
  auto => |> Hat0 Hat1 Hlen Hal Htb0 Htb1 Hal8.
  have ->: nbase = 8 * (_at %/ 8) by rewrite /nbase; smt().
  have ->: 8 * (_at %/ 8) = _at by smt().
  by apply addstate_spec4m_init; smt().
(* word loop: one broadcast word per iteration, at = 32 * (word index) *)
seq 2: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ 0 <= _LEN /\ at = 32 * (aT %/ 8 + _LEN %/ 8)
       /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] _len _tb (nbase + 8 * (_LEN %/ 8)) [buf; buf; buf; buf] st (aT + 8 * (_LEN %/ 8)) (_LEN - 8 * (_LEN %/ 8)) _TRAILB).
+ while (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
         /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
         /\ 0 <= _LEN /\ at %% 32 = 0 /\ aT %/ 8 <= at %/ 32 <= aT %/ 8 + _LEN %/ 8
         /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] _len _tb (nbase + 8 * (at %/ 32 - aT %/ 8)) [buf; buf; buf; buf] st (aT + 8 * (at %/ 32 - aT %/ 8)) (_LEN - 8 * (at %/ 32 - aT %/ 8)) _TRAILB).
  + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL Ha4 H1 H2 H Hb.
    split; first smt().
    split; first smt().
    pose d := at{m} %/ 32 - aT{m} %/ 8.
    move: (H 0 _) => //= Hk0.
    have Hd0: 0 <= d by smt().
    have Hl8: 8 <= _LEN{m} - 8 * d by smt().
    have Ea: aT{m} + 8 * d = nbase + 8 * d.
     by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    have Hfit: aT{m} + 8 * d + (_LEN{m} - 8 * d) = _at + size (memread _mem _buf _len).
     by apply (addstate_spec_fit _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    rewrite size_memread // in Hfit.
    have Hal8: aT{m} + 8 * d = 8 * (at{m} %/ 32) by move: Ea; rewrite /d /nbase; smt().
    rewrite (_: (at{m} + 32) %/ 32 - aT{m} %/ 8 = d + 1) 1:/#.
    rewrite (_: nbase + 8 * (d + 1) = (nbase + 8 * d) + 8) 1:/# (_: aT{m} + 8 * (d + 1) = (aT{m} + 8 * d) + 8) 1:/# (_: _LEN{m} - 8 * (d + 1) = (_LEN{m} - 8 * d) - 8) 1:/#.
    apply (addstate_spec4m_fullword _mem [_buf; _buf; _buf; _buf] (nbase + 8 * d) _st _at _len _tb st{m} _
             buf{m} buf{m} buf{m} buf{m} (aT{m} + 8 * d) (_LEN{m} - 8 * d) _TRAILB{m}) => //.
    + smt().
    by move=> k Hk; rewrite Hal8 nth4_const // (st4x_get_xorbcast256 st{m} at{m} (at{m} %/ 32)) //; smt().
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal H.
  have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ (H 0 _) => //; smt().
  have E: 32 * (aT{m} %/ 8) %/ 32 - aT{m} %/ 8 = 0 by smt().
  rewrite E /=; split.
  + split; first smt().
    split; first smt().
    split; first smt().
    exact H.
  move=> at0 b st0 Hex _ Ha H1 H2 Hs.
  have E2: at0 %/ 32 - aT{m} %/ 8 = _LEN{m} %/ 8 by smt().
  split; first smt().
  by move: Hs; rewrite E2.
seq 2: (Glob.mem = _mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
       /\ 0 <= _LEN < 8
       /\ exists sz, _at <= sz
          /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] _len _tb sz [buf; buf; buf; buf] st aT _LEN _TRAILB
          /\ (aT = sz => aT %% 8 = 0 /\ at = 32 * (aT %/ 8))).
+ auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL H.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  split; first by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
  by rewrite /nbase; smt().
if.
+ wp; ecall (m_ilen_read_bcast_upto8_at_h buf _LEN _TRAILB aT aT).
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL0 HL1 sz Hsz H Hal8 Hg r t Et H0.
  move: (H 0 _) => //= Hk0.
  have Ea: aT{m} = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ Hk0); smt().
  have [Ha8 Ea4] := Hal8 Ea.
  have Hab: aT{m} < 200 by move: Hk0; rewrite /addstate_spec size_memread //; smt().
  rewrite Et.
  apply (addstate_spec4m_finish _mem _buf _buf _buf _buf [t; t; t; t] sz _st _at _len _tb
           st{m} _ buf{m} buf{m} buf{m} buf{m} aT{m} _LEN{m} _TRAILB{m} r.`4 r.`1 r.`1 r.`1 r.`1 r.`2 r.`3) => //.
  + smt().
  + by move=> k Hk; rewrite nth4_const // (st4x_get_xorbcast256 st{m} at{m} (aT{m} %/ 8)) //; smt().
  by move=> k Hk; rewrite !nth4_const.
auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal HL0 HL1 sz Hsz H _ Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec4m_done _mem _buf _buf _buf _buf sz _st _at _len _tb st{m} buf{m} buf{m} buf{m} buf{m} aT{m} _TRAILB{m}) => //; smt().
qed.

lemma absorb_m_bcast_avx2x4_ll: islossless M.__absorb_m_bcast_avx2x4.
proof.
proc.
seq 2: true => //.
 call addstate_m_bcast_avx2x4_ll.
 if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_m_bcast_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 wp; call addstate_m_bcast_avx2x4_ll.
 by auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

lemma absorb_m_avx2x4_ll: islossless M.__absorb_m_avx2x4.
proof.
proc.
seq 2: true => //.
 call addstate_m_avx2x4_ll.
 if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  call addstate_m_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 by wp; call addstate_m_avx2x4_ll; auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

hoare absorb_m_avx2x4_h _l0 _l1 _l2 _l3 _mem _st _buf0 _buf1 _buf2 _buf3 _len _tb _r8:
 M.__absorb_m_avx2x4
 : Glob.mem=_mem /\ st=_st /\ aT=size _l0 %% _r8 /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 /\ 0 <= _len
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ memread _mem _buf0 _len) (_l1 ++ memread _mem _buf1 _len)
            (_l2 ++ memread _mem _buf2 _len) (_l3 ++ memread _mem _buf3 _len) res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ memread _mem _buf0 _len) (_l1 ++ memread _mem _buf1 _len)
            (_l2 ++ memread _mem _buf2 _len) (_l3 ++ memread _mem _buf3 _len) res.`1
       /\ res.`2 = (size _l0 + _len) %% _r8.
proof.
(* absorb_avx2x4_h with the inputs read from memory; the lanes' pointers advance together *)
proc => /=.
seq 1: (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0 /\ 0 <= _len
       /\ _buf0 <= buf0 <= _buf0 + _len
       /\ buf1 = _buf1 + (buf0 - _buf0) /\ buf2 = _buf2 + (buf0 - _buf0) /\ buf3 = _buf3 + (buf0 - _buf0)
       /\ _LEN = _len - (buf0 - _buf0)
       /\ aT = (size _l0 + (buf0 - _buf0)) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] (buf0 - _buf0) st).
+ if => //; last first.
   auto => |> Hs1 Hs2 Hs3 H Htb0 Htb1 Hlen Hg.
   have H4 := pabsorb4_init _ _ _ _ _ [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] _ H.
   have Hr8 := pabsorb4_r8 _ _ _ _ _ H4.
   do 3! (split; first smt()).
   exact H4.
  wp; while (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
             /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0 /\ 0 <= _len
             /\ iTERS = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 /\ 0 <= i <= iTERS
             /\ buf0 = _buf0 + (_r8 - size _l0 %% _r8 + i * _r8) /\ buf1 = _buf1 + (_r8 - size _l0 %% _r8 + i * _r8)
             /\ buf2 = _buf2 + (_r8 - size _l0 %% _r8 + i * _r8) /\ buf3 = _buf3 + (_r8 - size _l0 %% _r8 + i * _r8)
             /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] (_r8 - size _l0 %% _r8 + i * _r8) st).
  + wp; ecall (keccakf1600_avx2x4_h st); ecall (addstate_m_avx2x4_h Glob.mem st 0 buf0 buf1 buf2 buf3 _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hi0 Hi1 IH Hb.
    have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
    have Hm: 0 <= i{m} * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
    have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by rewrite StdOrder.IntOrder.ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_len - (_r8 - size _l0 %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> _ _ r Hr.
    have [_ [_ [E0 [E1 [E2 E3]]]]] := Hr.
    split; first smt().
    do 4! (split; first smt()).
    have Ha0: (size _l0 + (_r8 - size _l0 %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    rewrite (_: _r8 - size _l0 %% _r8 + (i{m} + 1) * _r8 = _r8 - size _l0 %% _r8 + i{m} * _r8 + _r8) 1:/#.
    by apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs IH (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_memread //; smt().
  wp; ecall (keccakf1600_avx2x4_h st); wp; ecall (addstate_m_avx2x4_h Glob.mem st aT buf0 buf1 buf2 buf3 (_RATE8 - aT) 0); auto => |>.
  move=> Hs1 Hs2 Hs3 H Htb0 Htb1 Hlen Hg.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  have H4 := pabsorb4_init _ _ _ _ _ [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] _ H.
  have [Hr0 Hr1] := pabsorb4_r8 _ _ _ _ _ H4.
  have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> _ _ _ _ r Hr.
  have [_ [_ [E0 [E1 [E2 E3]]]]] := Hr.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   do 4! (split; first smt()).
   have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len]
              (0 + (_r8 - size _l0 %% _r8)) (st4x_map keccak_f1600_op r.`1).
    by apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs H4 (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_memread //; smt().
   by move: HH => /=.
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs0.
  have Ei: i0 = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 by smt().
  have Ed: _len - (_r8 - size _l0 %% _r8) = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 + (_len - (_r8 - size _l0 %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l0 = size _l0 %/ _r8 * _r8 + size _l0 %% _r8 by exact divz_eq.
  have Hq: 0 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
  have Hmd: 0 <= (_len - (_r8 - size _l0 %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite (_: _buf0 + (_r8 - size _l0 %% _r8 + i0 * _r8) - _buf0 = _r8 - size _l0 %% _r8 + i0 * _r8) 1:/#.
  split; first smt().
  do 3! (split; first done).
  split; first smt().
  split.
   by rewrite Ei (_: size _l0 + (_r8 - size _l0 %% _r8 + (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8) = (size _l0 %/ _r8 + 1 + (_len - (_r8 - size _l0 %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
  split; first smt().
  exact Hs0.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2x4_h _RATE8 st); ecall (addstate_m_avx2x4_h Glob.mem st aT buf0 buf1 buf2 buf3 _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hb0 Hb1 Hfit H Htb.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  split; first smt().
  move=> _ _ _ _ r Hr.
  have [Hl _] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf0 _len) (memread _mem _buf1 _len) (memread _mem _buf2 _len) (memread _mem _buf3 _len) (buf0{m} - _buf0) (_len - (buf0{m} - _buf0)) ((size _l0 + (buf0{m} - _buf0)) %% _r8) st{m} r.`1 _tb _ _ _ _ _ _ _ Hs H (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_memread //; 1..5: smt().
  rewrite absorb_spec_avx2x4E => k Hk.
  by rewrite st4x_get_map // (Hl Htb) // nth_lcat4.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_m_avx2x4_h Glob.mem st aT buf0 buf1 buf2 buf3 _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hb0 Hb1 Hfit H.
have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
split; first smt().
move=> _ _ _ _ r Hr.
have [_ H0] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf0 _len) (memread _mem _buf1 _len) (memread _mem _buf2 _len) (memread _mem _buf3 _len) (buf0{m} - _buf0) (_len - (buf0{m} - _buf0)) ((size _l0 + (buf0{m} - _buf0)) %% _r8) st{m} r.`1 0 _ _ _ _ _ _ _ Hs H (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_memread //; 1..5: smt().
have [_ [Eat _]] := Hr.
split.
 rewrite pabsorb_spec_avx2x4E !size_cat !size_memread // Hs1 Hs2 Hs3; do 3! (split; first done).
 by move=> k Hk; rewrite nth_lcat4 // H0.
rewrite Eat /=.
have E: (size _l0 + (buf0{m} - _buf0)) %% _r8 + (_len - (buf0{m} - _buf0)) = (size _l0 + _len) + (- (size _l0 + (buf0{m} - _buf0)) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l0 + (buf0{m} - _buf0)) %% _r8 + (_len - (buf0{m} - _buf0))) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

hoare absorb_m_bcast_avx2x4_h _l0 _l1 _l2 _l3 _mem _st _buf _len _tb _r8:
 M.__absorb_m_bcast_avx2x4
 : Glob.mem=_mem /\ st=_st /\ aT=size _l0 %% _r8 /\ buf=_buf
 /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 /\ 0 <= _len
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ memread _mem _buf _len) (_l1 ++ memread _mem _buf _len)
            (_l2 ++ memread _mem _buf _len) (_l3 ++ memread _mem _buf _len) res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ memread _mem _buf _len) (_l1 ++ memread _mem _buf _len)
            (_l2 ++ memread _mem _buf _len) (_l3 ++ memread _mem _buf _len) res.`1
       /\ res.`2 = (size _l0 + _len) %% _r8.
proof.
(* absorb_avx2x4_h with the inputs read from memory; the lanes' pointers advance together *)
proc => /=.
seq 1: (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0 /\ 0 <= _len
       /\ _buf <= buf <= _buf + _len
       /\ _LEN = _len - (buf - _buf)
       /\ aT = (size _l0 + (buf - _buf)) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] (buf - _buf) st).
+ if => //; last first.
   auto => |> Hs1 Hs2 Hs3 H Htb0 Htb1 Hlen Hg.
   have H4 := pabsorb4_init _ _ _ _ _ [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] _ H.
   have Hr8 := pabsorb4_r8 _ _ _ _ _ H4.
   do 3! (split; first smt()).
   exact H4.
  wp; while (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
             /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0 /\ 0 <= _len
             /\ iTERS = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 /\ 0 <= i <= iTERS
             /\ buf = _buf + (_r8 - size _l0 %% _r8 + i * _r8)
             /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] (_r8 - size _l0 %% _r8 + i * _r8) st).
  + wp; ecall (keccakf1600_avx2x4_h st); ecall (addstate_m_bcast_avx2x4_h Glob.mem st 0 buf _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hi0 Hi1 IH Hb.
    have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
    have Hm: 0 <= i{m} * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
    have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by rewrite StdOrder.IntOrder.ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_len - (_r8 - size _l0 %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> _ _ r Hr.
    have [_ [_ [E0 [E1 [E2 E3]]]]] := Hr.
    split; first smt().
    split; first smt().
    have Ha0: (size _l0 + (_r8 - size _l0 %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    rewrite (_: _r8 - size _l0 %% _r8 + (i{m} + 1) * _r8 = _r8 - size _l0 %% _r8 + i{m} * _r8 + _r8) 1:/#.
    by apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs IH (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_memread //; smt().
  wp; ecall (keccakf1600_avx2x4_h st); wp; ecall (addstate_m_bcast_avx2x4_h Glob.mem st aT buf (_RATE8 - aT) 0); auto => |>.
  move=> Hs1 Hs2 Hs3 H Htb0 Htb1 Hlen Hg.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  have H4 := pabsorb4_init _ _ _ _ _ [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] _ H.
  have [Hr0 Hr1] := pabsorb4_r8 _ _ _ _ _ H4.
  have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> _ _ _ _ r Hr.
  have [_ [_ [E0 [E1 [E2 E3]]]]] := Hr.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   split; first smt().
   have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len]
              (0 + (_r8 - size _l0 %% _r8)) (st4x_map keccak_f1600_op r.`1).
    by apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs H4 (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_memread //; smt().
   by move: HH => /=.
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs0.
  have Ei: i0 = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 by smt().
  have Ed: _len - (_r8 - size _l0 %% _r8) = (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 + (_len - (_r8 - size _l0 %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l0 = size _l0 %/ _r8 * _r8 + size _l0 %% _r8 by exact divz_eq.
  have Hq: 0 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
  have Hmd: 0 <= (_len - (_r8 - size _l0 %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite (_: _buf + (_r8 - size _l0 %% _r8 + i0 * _r8) - _buf = _r8 - size _l0 %% _r8 + i0 * _r8) 1:/#.
  split; first smt().
  split; first smt().
  split.
   by rewrite Ei (_: size _l0 + (_r8 - size _l0 %% _r8 + (_len - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8) = (size _l0 %/ _r8 + 1 + (_len - (_r8 - size _l0 %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
  split; first smt().
  exact Hs0.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2x4_h _RATE8 st); ecall (addstate_m_bcast_avx2x4_h Glob.mem st aT buf _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hb0 Hb1 Hfit H Htb.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  split; first smt().
  move=> _ _ _ _ r Hr.
  have [Hl _] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (buf{m} - _buf) (_len - (buf{m} - _buf)) ((size _l0 + (buf{m} - _buf)) %% _r8) st{m} r.`1 _tb _ _ _ _ _ _ _ Hs H (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_memread //; 1..8: smt().
  rewrite absorb_spec_avx2x4E => k Hk.
  by rewrite st4x_get_map // (Hl Htb) // nth_lcat4.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_m_bcast_avx2x4_h Glob.mem st aT buf _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Hs1 Hs2 Hs3 Hlen Hb0 Hb1 Hfit H.
have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
split; first smt().
move=> _ _ _ _ r Hr.
have [_ H0] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (buf{m} - _buf) (_len - (buf{m} - _buf)) ((size _l0 + (buf{m} - _buf)) %% _r8) st{m} r.`1 0 _ _ _ _ _ _ _ Hs H (addstate_res4m_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_memread //; 1..8: smt().
have [_ [Eat _]] := Hr.
split.
 rewrite pabsorb_spec_avx2x4E !size_cat !size_memread // Hs1 Hs2 Hs3; do 3! (split; first done).
 by move=> k Hk; rewrite nth_lcat4 // H0.
rewrite Eat /=.
have E: (size _l0 + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf)) = (size _l0 + _len) + (- (size _l0 + (buf{m} - _buf)) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l0 + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf))) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

(* ---- memory dump/squeeze: lane k writes its bytes at b_k; the four regions are disjoint ---- *)

op stores4 (m: global_mem_t) (b0 b1 b2 b3: address) (l0 l1 l2 l3: W8.t list) =
 stores (stores (stores (stores m b0 l0) b1 l1) b2 l2) b3 l3.

op disj4 (b0 b1 b2 b3 n: int) =
    (b0 + n <= b1 \/ b1 + n <= b0) /\ (b0 + n <= b2 \/ b2 + n <= b0) /\ (b0 + n <= b3 \/ b3 + n <= b0)
 /\ (b1 + n <= b2 \/ b2 + n <= b1) /\ (b1 + n <= b3 \/ b3 + n <= b1) /\ (b2 + n <= b3 \/ b3 + n <= b2).

lemma disj4_le b0 b1 b2 b3 n n': n' <= n => disj4 b0 b1 b2 b3 n => disj4 b0 b1 b2 b3 n'.
proof. by rewrite /disj4; smt(). qed.

lemma disj4_shift b0 b1 b2 b3 n d n':
 0 <= d => d + n' <= n => disj4 b0 b1 b2 b3 n => disj4 (b0 + d) (b1 + d) (b2 + d) (b3 + d) n'.
proof. by rewrite /disj4; smt(). qed.

(* appending to the four regions at once *)
lemma stores4_cat m b0 b1 b2 b3 (l0 l1 l2 l3 w0 w1 w2 w3: W8.t list) n q:
 size l0 = n => size l1 = n => size l2 = n => size l3 = n =>
 size w0 = q => size w1 = q => size w2 = q => size w3 = q =>
 disj4 b0 b1 b2 b3 (n + q) =>
 stores4 (stores4 m b0 b1 b2 b3 l0 l1 l2 l3) (b0 + n) (b1 + n) (b2 + n) (b3 + n) w0 w1 w2 w3
 = stores4 m b0 b1 b2 b3 (l0 ++ w0) (l1 ++ w1) (l2 ++ w2) (l3 ++ w3).
proof.
rewrite /stores4 /disj4 => S0 S1 S2 S3 T0 T1 T2 T3 D.
apply mem_eq_ext => j; rewrite !get_storesE !size_cat S0 S1 S2 S3 T0 T1 T2 T3.
smt(nth_cat size_ge0).
qed.

(* the bytes of one 32-byte block / one word / the last partial word of a lane *)
lemma sub_stbytes_add32 (S: state) i (y: W256.t):
 0 <= i => i %% 32 = 0 => i + 32 <= 200 =>
 y = u256_pack4 S.[i %/ 8] S.[i %/ 8 + 1] S.[i %/ 8 + 2] S.[i %/ 8 + 3] =>
 sub (stbytes S) 0 (i + 32) = sub (stbytes S) 0 i ++ W32u8.to_list y.
proof.
move=> Hi Hm Hl ->.
rewrite (sub_cat (stbytes S) 0 i 32) 1,2:/# add0z; congr.
have ->: sub (stbytes S) i 32 = sub (stbytes S) (8 * (i %/ 8)) 32 by congr; smt().
by rewrite sub_stbytes_4lanes 1,2:/# /u64bytes u256_pack4_to_list.
qed.

lemma sub_stbytes_add8 (S: state) i (t: W64.t):
 0 <= i => i %% 8 = 0 => i + 8 <= 200 => t = S.[i %/ 8] =>
 sub (stbytes S) 0 (i + 8) = sub (stbytes S) 0 i ++ W8u8.to_list t.
proof.
move=> Hi Hm Hl ->.
rewrite (sub_cat (stbytes S) 0 i 8) 1,2:/# add0z; congr.
have ->: W8u8.to_list S.[i %/ 8] = u64bytes S.[i %/ 8] by rewrite /u64bytes.
by rewrite u64bytes_stword 1:/#; congr; smt().
qed.

lemma sub_stbytes_last (S: state) len (t: W64.t):
 0 <= len <= 200 => 0 < len %% 8 => t = S.[len %/ 8] =>
 sub (stbytes S) 0 len = sub (stbytes S) 0 (8 * (len %/ 8)) ++ take (len %% 8) (u64bytes t).
proof.
move=> Hl Hm ->.
rewrite u64bytes_stword 1:/# take_sub200 1:/#.
have := sub_cat (stbytes S) 0 (8 * (len %/ 8)) (len %% 8) _ _; 1,2: smt().
by rewrite /= (_: 8 * (len %/ 8) + len %% 8 = len) 1:/#.
qed.

lemma stores4_dump32 m (S4: state4x) b0 b1 b2 b3 len i (y0 y1 y2 y3: W256.t):
 0 <= i => i %% 32 = 0 => i + 32 <= len => len <= 200 => disj4 b0 b1 b2 b3 len =>
 y0 = u256_pack4 (S4.[i %/ 8] \bits64 0) (S4.[i %/ 8 + 1] \bits64 0) (S4.[i %/ 8 + 2] \bits64 0) (S4.[i %/ 8 + 3] \bits64 0) =>
 y1 = u256_pack4 (S4.[i %/ 8] \bits64 1) (S4.[i %/ 8 + 1] \bits64 1) (S4.[i %/ 8 + 2] \bits64 1) (S4.[i %/ 8 + 3] \bits64 1) =>
 y2 = u256_pack4 (S4.[i %/ 8] \bits64 2) (S4.[i %/ 8 + 1] \bits64 2) (S4.[i %/ 8 + 2] \bits64 2) (S4.[i %/ 8 + 3] \bits64 2) =>
 y3 = u256_pack4 (S4.[i %/ 8] \bits64 3) (S4.[i %/ 8 + 1] \bits64 3) (S4.[i %/ 8 + 2] \bits64 3) (S4.[i %/ 8 + 3] \bits64 3) =>
 storeW256 (storeW256 (storeW256 (storeW256 (stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 i) (sub (stbytes (st4x_get S4 1)) 0 i) (sub (stbytes (st4x_get S4 2)) 0 i) (sub (stbytes (st4x_get S4 3)) 0 i))
   (b0 + i) y0) (b1 + i) y1) (b2 + i) y2) (b3 + i) y3
 = stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 (i + 32)) (sub (stbytes (st4x_get S4 1)) 0 (i + 32)) (sub (stbytes (st4x_get S4 2)) 0 (i + 32)) (sub (stbytes (st4x_get S4 3)) 0 (i + 32)).
proof.
move=> Hi Hm Hl Hl2 Hd E0 E1 E2 E3.
rewrite (sub_stbytes_add32 (st4x_get S4 0) i y0) 1..3:/#; first by rewrite E0 !st4x_getiE //; smt().
rewrite (sub_stbytes_add32 (st4x_get S4 1) i y1) 1..3:/#; first by rewrite E1 !st4x_getiE //; smt().
rewrite (sub_stbytes_add32 (st4x_get S4 2) i y2) 1..3:/#; first by rewrite E2 !st4x_getiE //; smt().
rewrite (sub_stbytes_add32 (st4x_get S4 3) i y3) 1..3:/#; first by rewrite E3 !st4x_getiE //; smt().
have Hd': disj4 b0 b1 b2 b3 (i + 32) by apply (disj4_le _ _ _ _ len) => /#.
rewrite -(stores4_cat m b0 b1 b2 b3 _ _ _ _ _ _ _ _ i 32) ?size_sub ?size_to_list //.
by rewrite !storeW256E /stores4.
qed.

lemma stores4_dump8 m (S4: state4x) b0 b1 b2 b3 len i (t0 t1 t2 t3: W64.t):
 0 <= i => i %% 8 = 0 => i + 8 <= len => len <= 200 => disj4 b0 b1 b2 b3 len =>
 t0 = S4.[i %/ 8] \bits64 0 => t1 = S4.[i %/ 8] \bits64 1 =>
 t2 = S4.[i %/ 8] \bits64 2 => t3 = S4.[i %/ 8] \bits64 3 =>
 storeW64 (storeW64 (storeW64 (storeW64 (stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 i) (sub (stbytes (st4x_get S4 1)) 0 i) (sub (stbytes (st4x_get S4 2)) 0 i) (sub (stbytes (st4x_get S4 3)) 0 i))
   (b0 + i) t0) (b1 + i) t1) (b2 + i) t2) (b3 + i) t3
 = stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 (i + 8)) (sub (stbytes (st4x_get S4 1)) 0 (i + 8)) (sub (stbytes (st4x_get S4 2)) 0 (i + 8)) (sub (stbytes (st4x_get S4 3)) 0 (i + 8)).
proof.
move=> Hi Hm Hl Hl2 Hd E0 E1 E2 E3.
rewrite (sub_stbytes_add8 (st4x_get S4 0) i t0) 1..3:/#; first by rewrite E0 st4x_getiE //; smt().
rewrite (sub_stbytes_add8 (st4x_get S4 1) i t1) 1..3:/#; first by rewrite E1 st4x_getiE //; smt().
rewrite (sub_stbytes_add8 (st4x_get S4 2) i t2) 1..3:/#; first by rewrite E2 st4x_getiE //; smt().
rewrite (sub_stbytes_add8 (st4x_get S4 3) i t3) 1..3:/#; first by rewrite E3 st4x_getiE //; smt().
have Hd': disj4 b0 b1 b2 b3 (i + 8) by apply (disj4_le _ _ _ _ len) => /#.
rewrite -(stores4_cat m b0 b1 b2 b3 _ _ _ _ _ _ _ _ i 8) ?size_sub ?size_to_list //.
by rewrite !storeW64E /stores4.
qed.

lemma stores4_dumplast m (S4: state4x) b0 b1 b2 b3 len (t0 t1 t2 t3: W64.t) m1 m2 m3 m4 c0 c1 c2 c3 l0 l1 l2 l3:
 0 <= len <= 200 => 0 < len %% 8 => disj4 b0 b1 b2 b3 len =>
 t0 = S4.[len %/ 8] \bits64 0 => t1 = S4.[len %/ 8] \bits64 1 =>
 t2 = S4.[len %/ 8] \bits64 2 => t3 = S4.[len %/ 8] \bits64 3 =>
 msubwrite (stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 (8 * (len %/ 8))) (sub (stbytes (st4x_get S4 1)) 0 (8 * (len %/ 8))) (sub (stbytes (st4x_get S4 2)) 0 (8 * (len %/ 8))) (sub (stbytes (st4x_get S4 3)) 0 (8 * (len %/ 8)))) m1 (u64bytes t0) (b0 + 8 * (len %/ 8)) (len %% 8) c0 l0 =>
 msubwrite m1 m2 (u64bytes t1) (b1 + 8 * (len %/ 8)) (len %% 8) c1 l1 =>
 msubwrite m2 m3 (u64bytes t2) (b2 + 8 * (len %/ 8)) (len %% 8) c2 l2 =>
 msubwrite m3 m4 (u64bytes t3) (b3 + 8 * (len %/ 8)) (len %% 8) c3 l3 =>
 m4 = stores4 m b0 b1 b2 b3 (sub (stbytes (st4x_get S4 0)) 0 len) (sub (stbytes (st4x_get S4 1)) 0 len) (sub (stbytes (st4x_get S4 2)) 0 len) (sub (stbytes (st4x_get S4 3)) 0 len)
 /\ c0 = b0 + len /\ c1 = b1 + len /\ c2 = b2 + len /\ c3 = b3 + len.
proof.
move=> Hl Hm Hd E0 E1 E2 E3 [-> [-> _]] [-> [-> _]] [-> [-> _]] [-> [-> _]].
have Hs: forall (t: W64.t), min (size (u64bytes t)) (max 0 (len %% 8)) = len %% 8.
 by move=> t; rewrite /u64bytes size_to_list; smt().
rewrite !Hs; split; last smt().
rewrite (sub_stbytes_last (st4x_get S4 0) len t0) //; first by rewrite E0 st4x_getiE //; smt().
rewrite (sub_stbytes_last (st4x_get S4 1) len t1) //; first by rewrite E1 st4x_getiE //; smt().
rewrite (sub_stbytes_last (st4x_get S4 2) len t2) //; first by rewrite E2 st4x_getiE //; smt().
rewrite (sub_stbytes_last (st4x_get S4 3) len t3) //; first by rewrite E3 st4x_getiE //; smt().
have Hd': disj4 b0 b1 b2 b3 (8 * (len %/ 8) + len %% 8) by apply (disj4_le _ _ _ _ len) => /#.
have Ht: forall (t: W64.t), size (take (len %% 8) (u64bytes t)) = len %% 8.
 by move=> t; rewrite size_take' 1:/# /u64bytes size_to_list; smt().
by rewrite -(stores4_cat m b0 b1 b2 b3 _ _ _ _ _ _ _ _ (8 * (len %/ 8)) (len %% 8)) ?size_sub ?Ht //; smt().
qed.

(* the blocks squeezed so far, on the four lanes *)
lemma stores4_squeeze_step m r8 (S4: state4x) b0 b1 b2 b3 len i:
 0 < r8 <= 200 => 0 <= i => r8 * (i + 1) <= len => disj4 b0 b1 b2 b3 len =>
 stores4 (stores4 m b0 b1 b2 b3 (squeezeblocks r8 (st4x_get S4 0) i) (squeezeblocks r8 (st4x_get S4 1) i) (squeezeblocks r8 (st4x_get S4 2) i) (squeezeblocks r8 (st4x_get S4 3) i))
   (b0 + r8 * i) (b1 + r8 * i) (b2 + r8 * i) (b3 + r8 * i) (sub (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 0)) 0 r8) (sub (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 1)) 0 r8) (sub (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 2)) 0 r8) (sub (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 3)) 0 r8)
 = stores4 m b0 b1 b2 b3 (squeezeblocks r8 (st4x_get S4 0) (i + 1)) (squeezeblocks r8 (st4x_get S4 1) (i + 1)) (squeezeblocks r8 (st4x_get S4 2) (i + 1)) (squeezeblocks r8 (st4x_get S4 3) (i + 1)).
proof.
move=> Hr Hi Hl Hd.
rewrite !st4x_get_iter // 1..4:/# !squeezeblocks_step //.
have Hd': disj4 b0 b1 b2 b3 (r8 * i + r8) by apply (disj4_le _ _ _ _ len) => /#.
by apply (stores4_cat m b0 b1 b2 b3 _ _ _ _ _ _ _ _ (r8 * i) r8) => //; rewrite ?size_squeezeblocks ?size_sub //; smt().
qed.

lemma stores4_squeeze_last m r8 (S4: state4x) b0 b1 b2 b3 len:
 0 < r8 <= 200 => 0 <= len => 0 < len %% r8 => disj4 b0 b1 b2 b3 len =>
 stores4 (stores4 m b0 b1 b2 b3 (squeezeblocks r8 (st4x_get S4 0) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 1) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 2) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 3) (len %/ r8)))
   (b0 + r8 * (len %/ r8)) (b1 + r8 * (len %/ r8)) (b2 + r8 * (len %/ r8)) (b3 + r8 * (len %/ r8)) (sub (stbytes (st4x_get (iter (len %/ r8 + 1) keccak_f1600_x4 S4) 0)) 0 (len %% r8)) (sub (stbytes (st4x_get (iter (len %/ r8 + 1) keccak_f1600_x4 S4) 1)) 0 (len %% r8)) (sub (stbytes (st4x_get (iter (len %/ r8 + 1) keccak_f1600_x4 S4) 2)) 0 (len %% r8)) (sub (stbytes (st4x_get (iter (len %/ r8 + 1) keccak_f1600_x4 S4) 3)) 0 (len %% r8))
 = stores4 m b0 b1 b2 b3 (SQUEEZE1600 r8 len (st4x_get S4 0)) (SQUEEZE1600 r8 len (st4x_get S4 1)) (SQUEEZE1600 r8 len (st4x_get S4 2)) (SQUEEZE1600 r8 len (st4x_get S4 3)).
proof.
move=> Hr Hl C Hd.
have Hq: 0 <= len %/ r8 by smt(divz_ge0).
rewrite !(SQUEEZE1600_split r8 len) // C /= !st4x_get_iter // 1..4:/#.
have Hd': disj4 b0 b1 b2 b3 (r8 * (len %/ r8) + len %% r8) by apply (disj4_le _ _ _ _ len) => //; smt().
by apply (stores4_cat m b0 b1 b2 b3 _ _ _ _ _ _ _ _ (r8 * (len %/ r8)) (len %% r8)) => //; rewrite ?size_squeezeblocks ?size_sub //; smt(modz_ge0).
qed.

lemma stores4_squeeze_fin m r8 (S4: state4x) b0 b1 b2 b3 len:
 0 < r8 <= 200 => 0 <= len => !(0 < len %% r8) =>
 stores4 m b0 b1 b2 b3 (squeezeblocks r8 (st4x_get S4 0) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 1) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 2) (len %/ r8)) (squeezeblocks r8 (st4x_get S4 3) (len %/ r8)) = stores4 m b0 b1 b2 b3 (SQUEEZE1600 r8 len (st4x_get S4 0)) (SQUEEZE1600 r8 len (st4x_get S4 1)) (SQUEEZE1600 r8 len (st4x_get S4 2)) (SQUEEZE1600 r8 len (st4x_get S4 3)).
proof. by move=> Hr Hl C; rewrite !(SQUEEZE1600_split r8 len) // (_: (0 < len %% r8) = false) 1:/# /= !cats0. qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_m_avx2x4_ll: islossless M.__dumpstate_m_avx2x4.
proof.
proc.
seq 3: true => //.
 while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
by auto => /#.
qed.

hoare dumpstate_m_avx2x4_h _mem _buf0 _buf1 _buf2 _buf3 _len _st:
 M.__dumpstate_m_avx2x4
 : Glob.mem=_mem /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) 0 _len) (sub (stbytes (st4x_get _st 1)) 0 _len) (sub (stbytes (st4x_get _st 2)) 0 _len) (sub (stbytes (st4x_get _st 3)) 0 _len)
  /\ res = (_buf0 + _len, _buf1 + _len, _buf2 + _len, _buf3 + _len).
proof.
(* dumpstate_avx2x4_h with the four pointers as the lanes' cursors *)
proc.
seq 2: (0 <= _len <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ st = _st
        /\ i = 32 * (_len %/ 32)
        /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i
        /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) 0 i) (sub (stbytes (st4x_get _st 1)) 0 i) (sub (stbytes (st4x_get _st 2)) 0 i) (sub (stbytes (st4x_get _st 3)) 0 i)).
+ while (0 <= _len <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ st = _st
         /\ 0 <= i <= 32 * (_len %/ 32) /\ i %% 32 = 0
         /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i
         /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) 0 i) (sub (stbytes (st4x_get _st 1)) 0 i) (sub (stbytes (st4x_get _st 2)) 0 i) (sub (stbytes (st4x_get _st 3)) 0 i)).
  + wp; ecall (u64x4_u256x4_h x0 x1 x2 x3); auto => |> &m.
    move=> Hl0 Hl1 Hd Hi0 Hi1 Hm Hb r.
    rewrite (get256_init256_at _st (4 * i{m}) (i{m} %/ 8)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 32) (i{m} %/ 8 + 1)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 64) (i{m} %/ 8 + 2)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 96) (i{m} %/ 8 + 3)) 1,2:/#.
    move=> E0 E1 E2 E3.
    do 6! (split; first smt()).
    by apply (stores4_dump32 _mem _st _buf0 _buf1 _buf2 _buf3 _len i{m} r.`1 r.`2 r.`3 r.`4) => //; smt().
  auto => |> Hl0 Hl1 Hd.
  have E0: forall (S: WArray200.t), sub S 0 0 = [] by move=> S; rewrite -size_eq0 size_sub.
  split; first by split; [smt(divz_ge0) | rewrite !E0 /stores4 !store0].
  smt().
seq 1: (0 <= _len <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ st = _st
        /\ i = 8 * (_len %/ 8)
        /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i
        /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) 0 i) (sub (stbytes (st4x_get _st 1)) 0 i) (sub (stbytes (st4x_get _st 2)) 0 i) (sub (stbytes (st4x_get _st 3)) 0 i)).
+ while (0 <= _len <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ st = _st
         /\ 32 * (_len %/ 32) <= i <= 8 * (_len %/ 8) /\ i %% 8 = 0
         /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i
         /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) 0 i) (sub (stbytes (st4x_get _st 1)) 0 i) (sub (stbytes (st4x_get _st 2)) 0 i) (sub (stbytes (st4x_get _st 3)) 0 i)).
  + auto => |> &m.
    move=> Hl0 Hl1 Hd Hi0 Hi1 Hm Hb.
    do 6! (split; first smt()).
    have T0: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m}) = _st.[i{m} %/ 8] \bits64 0 by apply (get64_init256_at _st _ i{m} 0); smt().
    have T1: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 8) = _st.[i{m} %/ 8] \bits64 1 by apply (get64_init256_at _st _ i{m} 1); smt().
    have T2: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 16) = _st.[i{m} %/ 8] \bits64 2 by apply (get64_init256_at _st _ i{m} 2); smt().
    have T3: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 24) = _st.[i{m} %/ 8] \bits64 3 by apply (get64_init256_at _st _ i{m} 3); smt().
    by apply (stores4_dump8 _mem _st _buf0 _buf1 _buf2 _buf3 _len i{m}) => //; smt().
  auto => |> Hl0 Hl1 Hd; split; smt().
if.
+ wp; ecall (m_ilen_write_upto8_h Glob.mem buf3 (_LEN %% 8) t3).
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf2 (_LEN %% 8) t2).
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf1 (_LEN %% 8) t1).
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf0 (_LEN %% 8) t0).
  auto => |>.
  move=> Hl0 Hl1 Hd Hm r0 m1 W0 r1 m2 W1 r2 m3 W2 r3 m4 W3.
  have E8: 8 * (_len %/ 8) %/ 8 = _len %/ 8 by smt().
  have T0: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8))) = _st.[_len %/ 8] \bits64 0.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 0) 1..4:/# E8.
  have T1: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 8) = _st.[_len %/ 8] \bits64 1.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 1) 1..4:/# E8.
  have T2: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 16) = _st.[_len %/ 8] \bits64 2.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 2) 1..4:/# E8.
  have T3: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 24) = _st.[_len %/ 8] \bits64 3.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 3) 1..4:/# E8.
  by apply (stores4_dumplast _mem _st _buf0 _buf1 _buf2 _buf3 _len _ _ _ _ m1 m2 m3 m4 r0.`1 r1.`1 r2.`1 r3.`1 r0.`2 r1.`2 r2.`2 r3.`2 _ Hm Hd T0 T1 T2 T3 W0 W1 W2 W3).
auto => |> Hl0 Hl1 Hd Hm.
have ->: 8 * (_len %/ 8) = _len by smt().
done.
qed.

lemma squeeze_m_avx2x4_ll: islossless M.__squeeze_m_avx2x4.
proof.
proc.
seq 3: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_m_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_m_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.

hoare squeeze_m_avx2x4_h _mem _buf0 _buf1 _buf2 _buf3 _len _st _r8:
 M.__squeeze_m_avx2x4
 : Glob.mem=_mem /\ st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ _LEN=_len /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (SQUEEZE1600 _r8 _len (st4x_get _st 0)) (SQUEEZE1600 _r8 _len (st4x_get _st 1)) (SQUEEZE1600 _r8 _len (st4x_get _st 2)) (SQUEEZE1600 _r8 _len (st4x_get _st 3))
     /\ res = iter ((_len - 1) %/ _r8 + 1) keccak_f1600_x4 _st.
proof.
(* squeeze_avx2x4_h with the four pointers as the lanes' cursors *)
proc.
seq 3: (0 <= _len /\ 0 < _r8 <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ _RATE8 = _r8
        /\ lO = _len %% _r8 /\ st = iter (_len %/ _r8) keccak_f1600_x4 _st
        /\ buf0 = _buf0 + _r8 * (_len %/ _r8) /\ buf1 = _buf1 + _r8 * (_len %/ _r8)
        /\ buf2 = _buf2 + _r8 * (_len %/ _r8) /\ buf3 = _buf3 + _r8 * (_len %/ _r8)
        /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (squeezeblocks _r8 (st4x_get _st 0) (_len %/ _r8)) (squeezeblocks _r8 (st4x_get _st 1) (_len %/ _r8)) (squeezeblocks _r8 (st4x_get _st 2) (_len %/ _r8)) (squeezeblocks _r8 (st4x_get _st 3) (_len %/ _r8))).
+ sp; if.
  - while (0 <= i <= _len %/ _r8 /\ iTERS = _len %/ _r8
           /\ 0 <= _len /\ 0 < _r8 <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ _LEN = _len /\ _RATE8 = _r8
           /\ lO = _len %% _r8 /\ st = iter i keccak_f1600_x4 _st
           /\ buf0 = _buf0 + _r8 * i /\ buf1 = _buf1 + _r8 * i /\ buf2 = _buf2 + _r8 * i /\ buf3 = _buf3 + _r8 * i
           /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3 (squeezeblocks _r8 (st4x_get _st 0) i) (squeezeblocks _r8 (st4x_get _st 1) i) (squeezeblocks _r8 (st4x_get _st 2) i) (squeezeblocks _r8 (st4x_get _st 3) i)).
    + wp; ecall (dumpstate_m_avx2x4_h Glob.mem buf0 buf1 buf2 buf3 _RATE8 st); ecall (keccakf1600_avx2x4_h st).
      auto => |> &m.
      move=> Hi0 Hi1 Hl Hr0 Hr1 Hd Hb.
      have Hle: _r8 * (i{m} + 1) <= _len by apply mul_divz_le => /#.
      have Est: st4x_map keccak_f1600_op (iter i{m} keccak_f1600_x4 _st) = iter (i{m} + 1) keccak_f1600_x4 _st by rewrite iterS.
      split.
       split; first smt().
       by apply (disj4_shift _ _ _ _ _len) => /#.
      move=> _ _ _; rewrite Est.
      do 6! (split; first smt()).
      by apply (stores4_squeeze_step _mem _r8 _st _buf0 _buf1 _buf2 _buf3 _len i{m}) => //; smt().
    auto => |>.
    move=> Hl Hr0 Hr1 Hd Hg.
    have E0: forall (S: state), squeezeblocks _r8 S 0 = [] by move=> S; rewrite /squeezeblocks iota0 //= flatten_nil.
    split; first by split; [smt() | split; [by rewrite iter0 | by rewrite !E0 /stores4 !store0]].
    move=> i0 Hex Hi0 Hi1.
    have ->: i0 = _len %/ _r8 by smt().
    done.
  auto => |> Hl Hr0 Hr1 Hd Hg.
  have ->: _len %/ _r8 = 0 by smt(divz_ge0).
  have E0: forall (S: state), squeezeblocks _r8 S 0 = [] by move=> S; rewrite /squeezeblocks iota0 //= flatten_nil.
  by rewrite iter0 //= !E0 /stores4 !store0.
if.
+ ecall (dumpstate_m_avx2x4_h Glob.mem buf0 buf1 buf2 buf3 lO st); ecall (keccakf1600_avx2x4_h st).
  auto => |>.
  move=> Hl Hr0 Hr1 Hd C.
  have Hq: 0 <= _len %/ _r8 by smt(divz_ge0).
  have Hle: _r8 * (_len %/ _r8) <= _len by apply mul_divz_le => /#.
  have Est: st4x_map keccak_f1600_op (iter (_len %/ _r8) keccak_f1600_x4 _st) = iter (_len %/ _r8 + 1) keccak_f1600_x4 _st by rewrite iterS.
  split.
   split; first smt(modz_ge0).
   by apply (disj4_shift _ _ _ _ _len) => //; smt().
  move=> _ _ _; rewrite Est.
  split; first by apply (stores4_squeeze_last _mem _r8 _st _buf0 _buf1 _buf2 _buf3 _len).
  by rewrite divz_pred_pos 1,2:/#.
auto => |> Hl Hr0 Hr1 Hd C.
split; first by apply (stores4_squeeze_fin _mem _r8 _st _buf0 _buf1 _buf2 _buf3 _len).
by rewrite divz_pred_zero 1,2:/#.
qed.





abstract theory KeccakArrayAvx2x4.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

clone import ReadWriteArray as RW
 with op _ASIZE <- _ASIZE,
      theory A <- A,
      theory WA <- WA
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

(* ---- 4-lane versions of the shared read steps (lane k reads bk) ---- *)

lemma nth_sub4 (b0 b1 b2 b3: W8.t A.t) off len k:
 0 <= k < 4 =>
 nth [] [sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len] k
 = sub (nth witness [b0; b1; b2; b3] k) off len.
proof.
move=> Hk; have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]].
qed.

(* the bookkeeping of a read depends on the control arguments only *)
lemma asubread_same (b b': W8.t A.t) off (lw lw': W8.t list) cur at dlt len tb a d l t a' d' l' t':
 size lw = size lw' =>
 asubread b off lw cur at dlt len tb a d l t =>
 asubread b' off lw' cur at dlt len tb a' d' l' t' =>
 asubread b off lw cur at dlt len tb a' d' l' t'.
proof.
rewrite /asubread => Hs [Hsr [_ [_ [_ _]]]] [_ [-> [-> [-> ->]]]].
by rewrite Hs.
qed.

lemma addstate_spec4_asubread (b0 b1 b2 b3: W8.t A.t) (ws: W64.t list) cur (st: state4x) at off len tb
                              (stc stc': state4x) at0 dlt len0 tb0 cur1 at1 dlt1 len1 tb1:
 0 <= at => 0 <= len => 0 <= tb < 256 => 0 <= off => off + len <= _ASIZE =>
 0 <= cur <= at0 < cur+8 => cur1 = cur + 8 =>
 (forall k, 0 <= k < 4 => st4x_get stc' k = addstate_at (st4x_get stc k) cur (u64bytes (nth W64.zero ws k))) =>
 (forall k, 0 <= k < 4 => asubread (nth witness [b0; b1; b2; b3] k) off (u64bytes (nth W64.zero ws k)) cur at0 dlt len0 tb0 at1 dlt1 len1 tb1) =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb cur off (off + dlt) stc at0 len0 tb0 =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb cur1 off (off + dlt1) stc' at1 len1 tb1.
proof.
move=> Hat Hlen Htb Hoff Hsz Hc Hc1 Hst Hr H k Hk.
rewrite Hst // nth_sub4 //.
have := H k Hk; rewrite nth_sub4 // => Hk'.
apply (addstate_asubread_u64 (nth witness [b0; b1; b2; b3] k) (nth W64.zero ws k) cur (st4x_get st k) at off len tb
                             (st4x_get stc k) at0 dlt len0 tb0 cur1 at1 dlt1 len1 tb1) => //.
exact (Hr k Hk).
qed.

lemma addstate_spec4_fullword (b0 b1 b2 b3: W8.t A.t) (ws: W64.t list) sz (st: state4x) at off len tb
                              (stc stc': state4x) c at0 len0 tb0:
 0 <= at => 0 <= tb < 256 => at <= sz => 8 <= len0 => 0 <= off => 0 <= len => off + len <= _ASIZE =>

 (forall k, 0 <= k < 4 => st4x_get stc' k = addstate_at (st4x_get stc k) at0 (u64bytes (nth W64.zero ws k))) =>
 (forall k, 0 <= k < 4 => nth W64.zero ws k = get64_direct (WA.init8 ("_.[_]" (nth witness [b0; b1; b2; b3] k))) c) =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb sz off c stc at0 len0 tb0 =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb (sz + 8) off (c + 8) stc' (at0 + 8) (len0 - 8) tb0.
proof.
move=> Hat Htb Hsz Hl0 Hoff Hlen Hosz Hst Hw H k Hk.
rewrite Hst // nth_sub4 //.
have := H k Hk; rewrite nth_sub4 // => Hk'.
have Hs: size (u64bytes (nth W64.zero ws k)) = 8 by rewrite /u64bytes size_to_list.
have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz Hk'.
apply (addstate_spec_fullword _ (u64bytes (nth W64.zero ws k)) sz (st4x_get st k) at tb (st4x_get stc k)
                              off c at0 len0 tb0) => //; rewrite ?Hs //.
by rewrite Erem Hw //; apply getW64_bytearray; smt().
qed.

(* the result of __addstate on the four lanes *)
op addstate_res4 (st: state4x) at (bs: W8.t A.t list) off len tb (stc: state4x) at1 c1 =
 (forall k, 0 <= k < 4 => st4x_get stc k
    = addstate_at (st4x_get st k) at (sub (nth witness bs k) off len ++ if tb <> 0 then [W8.of_int tb] else []))
 /\ at1 = at + len + b2i (tb <> 0) /\ c1 = off + len.

lemma addstate_spec4_finish (b0 b1 b2 b3: W8.t A.t) (ws: W64.t list) sz (st: state4x) at off len tb
                            (stc stc': state4x) c at0 len0 tb0 at1 dlt1 len1 tb1:
 0 <= at => 0 <= tb < 256 => at <= sz => 0 <= off => 0 <= len => off + len <= _ASIZE =>
 len0 < 8 => (0 < len0 \/ tb0 <> 0) =>
 (forall k, 0 <= k < 4 => st4x_get stc' k = addstate_at (st4x_get stc k) at0 (u64bytes (nth W64.zero ws k))) =>
 (forall k, 0 <= k < 4 => asubread (nth witness [b0; b1; b2; b3] k) c (u64bytes (nth W64.zero ws k)) at0 at0 0 len0 tb0 at1 dlt1 len1 tb1) =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb sz off c stc at0 len0 tb0 =>
 addstate_res4 st at [b0; b1; b2; b3] off len tb stc' at1 (c + dlt1).
proof.
move=> Hat Htb Hsz Hoff Hlen Hosz Hl0 Hg Hst Hr H; rewrite /addstate_res4.
have Hl: forall k, 0 <= k < 4 =>
   addstate_at (st4x_get stc k) at0 (u64bytes (nth W64.zero ws k))
   = addstate_at (st4x_get st k) at (sub (nth witness [b0; b1; b2; b3] k) off len ++ if tb <> 0 then [W8.of_int tb] else [])
   /\ at1 = at + len + b2i (tb <> 0) /\ c + dlt1 = off + len.
 move=> k Hk.
 have := H k Hk; rewrite nth_sub4 // => Hk'.
 have Hs: size (u64bytes (nth W64.zero ws k)) = 8 by rewrite /u64bytes size_to_list.
 have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz Hk'.
 move: (Hr k Hk); rewrite /asubread Hs => [#] Hsr Eat Edlt _ _.
 apply (addstate_spec_finish (sub (nth witness [b0; b1; b2; b3] k) off len) (u64bytes (nth W64.zero ws k)) len sz
          (st4x_get st k) at tb (st4x_get stc k) off c at0 len0 tb0 at1 (c + dlt1)) => //.
 + by rewrite size_sub.
 + smt().
 + by rewrite Erem (_: c = c + 0) 1:/#; apply Hsr; smt().
split; first by move=> k Hk; rewrite Hst //; have [-> _] := Hl k Hk.
by have [_ ->] := Hl 0 _.
qed.

lemma addstate_spec4_done (b0 b1 b2 b3: W8.t A.t) sz (st: state4x) at off len tb (stc: state4x) c at0 tb0:
 0 <= at => 0 <= tb < 256 => tb0 %% 256 = 0 => 0 <= off => 0 <= len =>
 addstate_spec4 st at ([sub b0 off len; sub b1 off len; sub b2 off len; sub b3 off len]) tb sz off c stc at0 0 tb0 =>
 addstate_res4 st at [b0; b1; b2; b3] off len tb stc at0 c.
proof.
move=> Hat Htb Htb0 Hoff Hlen H; rewrite /addstate_res4.
have Hl: forall k, 0 <= k < 4 =>
   st4x_get stc k = addstate_at (st4x_get st k) at (sub (nth witness [b0; b1; b2; b3] k) off len ++ if tb <> 0 then [W8.of_int tb] else [])
   /\ at0 = at + len + b2i (tb <> 0) /\ c = off + len.
 move=> k Hk; have := H k Hk; rewrite nth_sub4 // => Hk'.
 by apply (addstate_spec_done (sub (nth witness [b0; b1; b2; b3] k) off len) len sz (st4x_get st k) at tb
             (st4x_get stc k) off c at0 tb0) => //; rewrite size_sub.
split; first by move=> k Hk; have [-> _] := Hl k Hk.
by have [_ ->] := Hl 0 _.
qed.

(* the addstate result, lane by lane, as chunks of the input lists *)
lemma addstate_res4_lanes (st: state4x) at (b0 b1 b2 b3: W8.t A.t) off len tb (stc: state4x) at1 c1:
 0 <= off => 0 <= len => off + len <= _ASIZE =>
 addstate_res4 st at [b0; b1; b2; b3] off len tb stc at1 c1 =>
 addstate_lanes st at [take len (drop off (to_list b0)); take len (drop off (to_list b1));
                       take len (drop off (to_list b2)); take len (drop off (to_list b3))] tb stc.
proof.
move=> H0 H1 H2 [Hl _] k Hk; rewrite Hl //.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /=; rewrite slice_to_list.
qed.

(* dump: one 32-byte block, one word, the last partial word, on a single lane *)
lemma asubwrite_lane_step32 (S: state) a b off len i p y:
 0 <= i => i %% 32 = 0 => i + 32 <= len => len <= 200 => p = off + i =>
 y = u256_pack4 S.[i %/ 8] S.[i %/ 8 + 1] S.[i %/ 8 + 2] S.[i %/ 8 + 3] =>
 asubwrite a b off (sub (stbytes S) 0 i) 0 len i (len - i) =>
 asubwrite a (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" b)) p y)))
   off (sub (stbytes S) 0 (i + 32)) 0 len (i + 32) (len - (i + 32)).
proof.
move=> Hi Hm Hl Hl2 Hp -> H.
apply (asubwrite_dump_step (stbytes S) a b _ off len i 32
         (u256bytes (u256_pack4 S.[i %/ 8] S.[i %/ 8 + 1] S.[i %/ 8 + 2] S.[i %/ 8 + 3]))
         i (i + 32) (i + 32) (len - i) (len - (i + 32)) _ _ _ _ _ _ H); 1..6: smt().
+ have ->: sub (stbytes S) i 32 = sub (stbytes S) (8 * (i %/ 8)) 32 by congr; smt().
  by rewrite sub_stbytes_4lanes 1,2:/# /u256bytes /u64bytes u256_pack4_to_list.
by apply asubwrite_set256; smt().
qed.

lemma asubwrite_lane_step8 (S: state) a b off len i p t:
 0 <= i => i %% 8 = 0 => i + 8 <= len => len <= 200 => p = off + i => t = S.[i %/ 8] =>
 asubwrite a b off (sub (stbytes S) 0 i) 0 len i (len - i) =>
 asubwrite a (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" b)) p t)))
   off (sub (stbytes S) 0 (i + 8)) 0 len (i + 8) (len - (i + 8)).
proof.
move=> Hi Hm Hl Hl2 Hp -> H.
apply (asubwrite_dump_step (stbytes S) a b _ off len i 8 (u64bytes S.[i %/ 8])
         i (i + 8) (i + 8) (len - i) (len - (i + 8)) _ _ _ _ _ _ H); 1..6: smt().
+ by rewrite u64bytes_stword 1:/#; congr; smt().
by apply asubwrite_set64; smt().
qed.

lemma asubwrite_lane_last (S: state) a b c off len p t d l:
 0 <= len <= 200 => 0 < len %% 8 => p = off + 8 * (len %/ 8) => t = S.[len %/ 8] =>
 asubwrite a b off (sub (stbytes S) 0 (8 * (len %/ 8))) 0 len (8 * (len %/ 8)) (len - 8 * (len %/ 8)) =>
 asubwrite b c p (u64bytes t) 0 (len %% 8) d l =>
 c = A.fill (fun i => (stbytes S).[i - off]) off len a.
proof.
move=> Hl Hm -> -> Hsw H2.
have := asubwrite_rebase _ _ _ off _ _ _ _ _ H2.
rewrite (_: 0 + (off + 8 * (len %/ 8) - off) = 8 * (len %/ 8)) 1:/# (_: len %% 8 = len - 8 * (len %/ 8)) 1:/# => H2'.
have [-> _] := asubwrite_dump_last (stbytes S) a b c off len (8 * (len %/ 8)) 8 _ _ _ _ _ _ _ _ Hsw _ H2'; 1..3: smt().
+ by rewrite u64bytes_stword /#.
done.
qed.

(* the dump invariant on the four lanes *)
op asubwrite4 (S4: state4x) (a0 a1 a2 a3 b0 b1 b2 b3: W8.t A.t) off n len d l =
    asubwrite a0 b0 off (sub (stbytes (st4x_get S4 0)) 0 n) 0 len d l
 /\ asubwrite a1 b1 off (sub (stbytes (st4x_get S4 1)) 0 n) 0 len d l
 /\ asubwrite a2 b2 off (sub (stbytes (st4x_get S4 2)) 0 n) 0 len d l
 /\ asubwrite a3 b3 off (sub (stbytes (st4x_get S4 3)) 0 n) 0 len d l.

lemma asubwrite4_init (S4: state4x) a0 a1 a2 a3 off len:
 0 <= len => asubwrite4 S4 a0 a1 a2 a3 a0 a1 a2 a3 off 0 len 0 len.
proof.
move=> H; rewrite /asubwrite4.
by do 3! (split; first exact (asubwrite_dump0 _ _ _ _ H)); exact (asubwrite_dump0 _ _ _ _ H).
qed.

lemma asubwrite4_step32 (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 off len i p y0 y1 y2 y3:
 0 <= i => i %% 32 = 0 => i + 32 <= len => len <= 200 => p = off + i =>
 y0 = u256_pack4 (S4.[i %/ 8] \bits64 0) (S4.[i %/ 8 + 1] \bits64 0) (S4.[i %/ 8 + 2] \bits64 0) (S4.[i %/ 8 + 3] \bits64 0) =>
 y1 = u256_pack4 (S4.[i %/ 8] \bits64 1) (S4.[i %/ 8 + 1] \bits64 1) (S4.[i %/ 8 + 2] \bits64 1) (S4.[i %/ 8 + 3] \bits64 1) =>
 y2 = u256_pack4 (S4.[i %/ 8] \bits64 2) (S4.[i %/ 8 + 1] \bits64 2) (S4.[i %/ 8 + 2] \bits64 2) (S4.[i %/ 8 + 3] \bits64 2) =>
 y3 = u256_pack4 (S4.[i %/ 8] \bits64 3) (S4.[i %/ 8 + 1] \bits64 3) (S4.[i %/ 8 + 2] \bits64 3) (S4.[i %/ 8 + 3] \bits64 3) =>
 asubwrite4 S4 a0 a1 a2 a3 b0 b1 b2 b3 off i len i (len - i) =>
 asubwrite4 S4 a0 a1 a2 a3
   (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" b0)) p y0)))
   (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" b1)) p y1)))
   (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" b2)) p y2)))
   (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" b3)) p y3)))
   off (i + 32) len (i + 32) (len - (i + 32)).
proof.
move=> Hi Hm Hl Hl2 Hp E0 E1 E2 E3 [H0 [H1 [H2 H3]]]; rewrite /asubwrite4.
split; first by apply (asubwrite_lane_step32 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H0); rewrite E0 !st4x_getiE //; smt().
split; first by apply (asubwrite_lane_step32 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H1); rewrite E1 !st4x_getiE //; smt().
split; first by apply (asubwrite_lane_step32 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H2); rewrite E2 !st4x_getiE //; smt().
by apply (asubwrite_lane_step32 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H3); rewrite E3 !st4x_getiE //; smt().
qed.

lemma asubwrite4_step8 (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 off len i p t0 t1 t2 t3:
 0 <= i => i %% 8 = 0 => i + 8 <= len => len <= 200 => p = off + i =>
 t0 = S4.[i %/ 8] \bits64 0 => t1 = S4.[i %/ 8] \bits64 1 =>
 t2 = S4.[i %/ 8] \bits64 2 => t3 = S4.[i %/ 8] \bits64 3 =>
 asubwrite4 S4 a0 a1 a2 a3 b0 b1 b2 b3 off i len i (len - i) =>
 asubwrite4 S4 a0 a1 a2 a3
   (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" b0)) p t0)))
   (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" b1)) p t1)))
   (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" b2)) p t2)))
   (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" b3)) p t3)))
   off (i + 8) len (i + 8) (len - (i + 8)).
proof.
move=> Hi Hm Hl Hl2 Hp E0 E1 E2 E3 [H0 [H1 [H2 H3]]]; rewrite /asubwrite4.
have Ej: forall k, 0 <= k < 4 => (st4x_get S4 k).[i %/ 8] = S4.[i %/ 8] \bits64 k.
 by move=> k Hk; rewrite st4x_getiE //; smt().
split; first by apply (asubwrite_lane_step8 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H0); rewrite E0 Ej.
split; first by apply (asubwrite_lane_step8 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H1); rewrite E1 Ej.
split; first by apply (asubwrite_lane_step8 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H2); rewrite E2 Ej.
by apply (asubwrite_lane_step8 _ _ _ _ _ _ _ _ Hi Hm Hl Hl2 Hp _ H3); rewrite E3 Ej.
qed.

lemma asubwrite4_last (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 off len p t0 t1 t2 t3 d0 d1 d2 d3 l0 l1 l2 l3:
 0 <= len <= 200 => 0 < len %% 8 => p = off + 8 * (len %/ 8) =>
 t0 = S4.[len %/ 8] \bits64 0 => t1 = S4.[len %/ 8] \bits64 1 =>
 t2 = S4.[len %/ 8] \bits64 2 => t3 = S4.[len %/ 8] \bits64 3 =>
 asubwrite4 S4 a0 a1 a2 a3 b0 b1 b2 b3 off (8 * (len %/ 8)) len (8 * (len %/ 8)) (len - 8 * (len %/ 8)) =>
 asubwrite b0 c0 p (u64bytes t0) 0 (len %% 8) d0 l0 =>
 asubwrite b1 c1 p (u64bytes t1) 0 (len %% 8) d1 l1 =>
 asubwrite b2 c2 p (u64bytes t2) 0 (len %% 8) d2 l2 =>
 asubwrite b3 c3 p (u64bytes t3) 0 (len %% 8) d3 l3 =>
    c0 = A.fill (fun i => (stbytes (st4x_get S4 0)).[i - off]) off len a0
 /\ c1 = A.fill (fun i => (stbytes (st4x_get S4 1)).[i - off]) off len a1
 /\ c2 = A.fill (fun i => (stbytes (st4x_get S4 2)).[i - off]) off len a2
 /\ c3 = A.fill (fun i => (stbytes (st4x_get S4 3)).[i - off]) off len a3.
proof.
move=> Hl Hm Hp E0 E1 E2 E3 [H0 [H1 [H2 H3]]] W0 W1 W2 W3.
have Ej: forall k, 0 <= k < 4 => (st4x_get S4 k).[len %/ 8] = S4.[len %/ 8] \bits64 k.
 by move=> k Hk; rewrite st4x_getiE //; smt().
split; first by apply (asubwrite_lane_last _ _ _ _ _ _ _ _ _ _ Hl Hm Hp _ H0 W0); rewrite E0 Ej.
split; first by apply (asubwrite_lane_last _ _ _ _ _ _ _ _ _ _ Hl Hm Hp _ H1 W1); rewrite E1 Ej.
split; first by apply (asubwrite_lane_last _ _ _ _ _ _ _ _ _ _ Hl Hm Hp _ H2 W2); rewrite E2 Ej.
by apply (asubwrite_lane_last _ _ _ _ _ _ _ _ _ _ Hl Hm Hp _ H3 W3); rewrite E3 Ej.
qed.

lemma asubwrite4_fin (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 off len d:
 0 <= len =>
 asubwrite4 S4 a0 a1 a2 a3 b0 b1 b2 b3 off len len d 0 =>
    b0 = A.fill (fun i => (stbytes (st4x_get S4 0)).[i - off]) off len a0
 /\ b1 = A.fill (fun i => (stbytes (st4x_get S4 1)).[i - off]) off len a1
 /\ b2 = A.fill (fun i => (stbytes (st4x_get S4 2)).[i - off]) off len a2
 /\ b3 = A.fill (fun i => (stbytes (st4x_get S4 3)).[i - off]) off len a3.
proof.
move=> Hl [H0 [H1 [H2 H3]]].
have [-> _] := asubwrite_dump_fin _ _ _ _ _ _ Hl H0.
have [-> _] := asubwrite_dump_fin _ _ _ _ _ _ Hl H1.
have [-> _] := asubwrite_dump_fin _ _ _ _ _ _ Hl H2.
by have [-> _] := asubwrite_dump_fin _ _ _ _ _ _ Hl H3.
qed.

(* squeeze: the blocks squeezed so far, on a single lane and on the four lanes *)
lemma asubwrite_squeeze0 r8 (st: state) a:
 asubwrite a a 0 (squeezeblocks r8 st 0) 0 _ASIZE 0 (_ASIZE - 0).
proof.
rewrite /squeezeblocks iota0 //= flatten_nil /asubwrite /=; split; last smt(_ASIZE_ge0).
by rewrite tP => i Hi; rewrite filliE // /#.
qed.

lemma asubwrite_squeeze_step r8 (st: state) a b c i:
 0 < r8 <= 200 => 0 <= i => r8 * (i + 1) <= _ASIZE =>
 asubwrite a b 0 (squeezeblocks r8 st i) 0 _ASIZE (r8 * i) (_ASIZE - r8 * i) =>
 c = A.fill (fun j => (stbytes (st_i st (i + 1))).[j - r8 * i]) (r8 * i) r8 b =>
 asubwrite a c 0 (squeezeblocks r8 st (i + 1)) 0 _ASIZE (r8 * (i + 1)) (_ASIZE - r8 * (i + 1)).
proof.
move=> Hr Hi Hl Hsw ->.
rewrite squeezeblocks_step 1,2:/#.
apply (asubwrite_app_dump _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsw); 2..5: smt().
by rewrite size_squeezeblocks 1,2:/#; smt().
qed.

op asqueeze4 r8 (S4: state4x) (a0 a1 a2 a3 b0 b1 b2 b3: W8.t A.t) n off =
    asubwrite a0 b0 0 (squeezeblocks r8 (st4x_get S4 0) n) 0 _ASIZE off (_ASIZE - off)
 /\ asubwrite a1 b1 0 (squeezeblocks r8 (st4x_get S4 1) n) 0 _ASIZE off (_ASIZE - off)
 /\ asubwrite a2 b2 0 (squeezeblocks r8 (st4x_get S4 2) n) 0 _ASIZE off (_ASIZE - off)
 /\ asubwrite a3 b3 0 (squeezeblocks r8 (st4x_get S4 3) n) 0 _ASIZE off (_ASIZE - off).

lemma asqueeze4_init r8 (S4: state4x) a0 a1 a2 a3:
 asqueeze4 r8 S4 a0 a1 a2 a3 a0 a1 a2 a3 0 0.
proof. by rewrite /asqueeze4 !asubwrite_squeeze0. qed.

lemma asqueeze4_step r8 (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 i:
 0 < r8 <= 200 => 0 <= i => r8 * (i + 1) <= _ASIZE =>
 asqueeze4 r8 S4 a0 a1 a2 a3 b0 b1 b2 b3 i (r8 * i) =>
 c0 = A.fill (fun j => (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 0)).[j - r8 * i]) (r8 * i) r8 b0 =>
 c1 = A.fill (fun j => (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 1)).[j - r8 * i]) (r8 * i) r8 b1 =>
 c2 = A.fill (fun j => (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 2)).[j - r8 * i]) (r8 * i) r8 b2 =>
 c3 = A.fill (fun j => (stbytes (st4x_get (iter (i + 1) keccak_f1600_x4 S4) 3)).[j - r8 * i]) (r8 * i) r8 b3 =>
 asqueeze4 r8 S4 a0 a1 a2 a3 c0 c1 c2 c3 (i + 1) (r8 * (i + 1)).
proof.
move=> Hr Hi Hl [H0 [H1 [H2 H3]]] E0 E1 E2 E3; rewrite /asqueeze4.
split; first by apply (asubwrite_squeeze_step _ _ _ _ _ _ Hr Hi Hl H0); rewrite E0 st4x_get_iter // /#.
split; first by apply (asubwrite_squeeze_step _ _ _ _ _ _ Hr Hi Hl H1); rewrite E1 st4x_get_iter // /#.
split; first by apply (asubwrite_squeeze_step _ _ _ _ _ _ Hr Hi Hl H2); rewrite E2 st4x_get_iter // /#.
by apply (asubwrite_squeeze_step _ _ _ _ _ _ Hr Hi Hl H3); rewrite E3 st4x_get_iter // /#.
qed.

lemma asqueeze4_last r8 (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3:
 0 < r8 <= 200 => 0 < _ASIZE %% r8 =>
 asqueeze4 r8 S4 a0 a1 a2 a3 b0 b1 b2 b3 (_ASIZE %/ r8) (r8 * (_ASIZE %/ r8)) =>
 c0 = A.fill (fun j => (stbytes (st4x_get (iter (_ASIZE %/ r8 + 1) keccak_f1600_x4 S4) 0)).[j - r8 * (_ASIZE %/ r8)]) (r8 * (_ASIZE %/ r8)) (_ASIZE %% r8) b0 =>
 c1 = A.fill (fun j => (stbytes (st4x_get (iter (_ASIZE %/ r8 + 1) keccak_f1600_x4 S4) 1)).[j - r8 * (_ASIZE %/ r8)]) (r8 * (_ASIZE %/ r8)) (_ASIZE %% r8) b1 =>
 c2 = A.fill (fun j => (stbytes (st4x_get (iter (_ASIZE %/ r8 + 1) keccak_f1600_x4 S4) 2)).[j - r8 * (_ASIZE %/ r8)]) (r8 * (_ASIZE %/ r8)) (_ASIZE %% r8) b2 =>
 c3 = A.fill (fun j => (stbytes (st4x_get (iter (_ASIZE %/ r8 + 1) keccak_f1600_x4 S4) 3)).[j - r8 * (_ASIZE %/ r8)]) (r8 * (_ASIZE %/ r8)) (_ASIZE %% r8) b3 =>
    c0 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 0))
 /\ c1 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 1))
 /\ c2 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 2))
 /\ c3 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 3)).
proof.
move=> Hr C [H0 [H1 [H2 H3]]] E0 E1 E2 E3.
have Hn: 0 <= _ASIZE %/ r8 + 1 by smt(divz_ge0 _ASIZE_ge0).
have L0 := asubwrite_squeeze_last r8 _ _ _ _ _ _ Hr C (eq_refl _) H0.
have L1 := asubwrite_squeeze_last r8 _ _ _ _ _ _ Hr C (eq_refl _) H1.
have L2 := asubwrite_squeeze_last r8 _ _ _ _ _ _ Hr C (eq_refl _) H2.
have L3 := asubwrite_squeeze_last r8 _ _ _ _ _ _ Hr C (eq_refl _) H3.
split; first by rewrite E0 st4x_get_iter // -L0 to_listK.
split; first by rewrite E1 st4x_get_iter // -L1 to_listK.
split; first by rewrite E2 st4x_get_iter // -L2 to_listK.
by rewrite E3 st4x_get_iter // -L3 to_listK.
qed.

lemma asqueeze4_fin r8 (S4: state4x) a0 a1 a2 a3 b0 b1 b2 b3 d:
 0 < r8 <= 200 => !(0 < _ASIZE %% r8) =>
 asqueeze4 r8 S4 a0 a1 a2 a3 b0 b1 b2 b3 (_ASIZE %/ r8) d =>
    b0 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 0))
 /\ b1 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 1))
 /\ b2 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 2))
 /\ b3 = of_list W8.zero (SQUEEZE1600 r8 _ASIZE (st4x_get S4 3)).
proof.
move=> Hr C [H0 [H1 [H2 H3]]].
split; first by rewrite -(asubwrite_squeeze_fin _ _ _ _ _ _ Hr C H0) to_listK.
split; first by rewrite -(asubwrite_squeeze_fin _ _ _ _ _ _ Hr C H1) to_listK.
split; first by rewrite -(asubwrite_squeeze_fin _ _ _ _ _ _ Hr C H2) to_listK.
by rewrite -(asubwrite_squeeze_fin _ _ _ _ _ _ Hr C H3) to_listK.
qed.

module MM = {
  proc __addstate_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                buf:W8.t A.t, offset:int, _LEN:int,
                                _TRAILB:int) : W256.t Array25.t * int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ RW.MM.__a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, aT, aT8);
      w <- (w `^` st.[(aT %/ 8)]);
      st.[(aT %/ 8)] <- w;
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (32 * (aT %/ 8));
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      w <-
      (VPBROADCAST_4u64
      (get64_direct (WA.init8 (fun i => buf.[i])) offset));
      offset <- (offset + 8);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      at <- (at + 32);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_bcast_upto8_at (
      buf, offset, 0, _LEN, _TRAILB, aT, aT);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                              buf:W8.t A.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ M._keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_bcast_avx2x4 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ M._keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __addstate_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t A.t,
                          buf1:W8.t A.t, buf2:W8.t A.t,
                          buf3:W8.t A.t, offset:int, _LEN:int,
                          _TRAILB:int) : W256.t Array25.t * int * int = {
    var dELTA:int;
    var aT8:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var at:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    var  _8:int;
    var  _9:int;
    var  _10:int;
    var  _11:int;
    var  _12:int;
    var  _13:int;
    var  _14:int;
    var  _15:int;
    var  _16:int;
    var  _17:int;
    var  _18:int;
    var  _19:int;
    var  _20:int;
    var  _21:int;
    var  _22:int;
    var  _23:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      ( _0,  _1,  _2,  _3, t0) <@ RW.MM.__a_ilen_read_upto8_at (buf0, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 0)) `^`
      t0))));
      ( _4,  _5,  _6,  _7, t1) <@ RW.MM.__a_ilen_read_upto8_at (buf1, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 1)) `^`
      t1))));
      ( _8,  _9,  _10,  _11, t2) <@ RW.MM.__a_ilen_read_upto8_at (buf2, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 2)) `^`
      t2))));
      (dELTA, _LEN, _TRAILB, aT8, t3) <@ RW.MM.__a_ilen_read_upto8_at (buf3,
      offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 3)) `^`
      t3))));
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (4 * (aT %/ 8));
    while ((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))))) {
      t0 <- (get64_direct (WA.init8 (fun i => buf0.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      t1 <- (get64_direct (WA.init8 (fun i => buf1.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      t2 <- (get64_direct (WA.init8 (fun i => buf2.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      t3 <- (get64_direct (WA.init8 (fun i => buf3.[i])) offset);
      offset <- (offset + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      at <- (at + 4);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      ( _12,  _13,  _14,  _15, t0) <@ RW.MM.__a_ilen_read_upto8_at (buf0, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      ( _16,  _17,  _18,  _19, t1) <@ RW.MM.__a_ilen_read_upto8_at (buf1, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      ( _20,  _21,  _22,  _23, t2) <@ RW.MM.__a_ilen_read_upto8_at (buf2, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      (dELTA, _LEN, _TRAILB, aT, t3) <@ RW.MM.__a_ilen_read_upto8_at (buf3, 
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t A.t,
                        buf1:W8.t A.t, buf2:W8.t A.t,
                        buf3:W8.t A.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, 
      buf3, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ M._keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_avx2x4 (st, 0, buf0, buf1, buf2,
        buf3, offset, _RATE8, 0);
        st <@ M._keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, buf3,
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                           buf2:W8.t A.t, buf3:W8.t A.t,
                           offset:int, _LEN:int, st:W256.t Array25.t) : 
  W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t * int = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    i <- 0;
    while ((i < (32 * (_LEN %/ 32)))) {
      x0 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 32)));
      x1 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 32)));
      x2 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 32)));
      x3 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 32)));
      i <- (i + 32);
      (x0, x1, x2, x3) <@ M.__4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      offset x0)));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      offset x1)));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      offset x2)));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      offset x3)));
      offset <- (offset + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      buf0 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      offset t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      offset t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      offset t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      offset t3)));
      i <- (i + 8);
      offset <- (offset + 8);
    }
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0,  _1) <@ RW.MM.__a_ilen_write_upto8 (buf0, offset, 0, (_LEN %% 8),
      t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _2,  _3) <@ RW.MM.__a_ilen_write_upto8 (buf1, offset, 0, (_LEN %% 8),
      t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _4,  _5) <@ RW.MM.__a_ilen_write_upto8 (buf2, offset, 0, (_LEN %% 8),
      t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _6,  _7) <@ RW.MM.__a_ilen_write_upto8 (buf3, offset, 0, (_LEN %% 8),
      t3);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc __squeeze_avx2x4 (st:W256.t Array25.t, buf0:W8.t A.t,
                         buf1:W8.t A.t, buf2:W8.t A.t,
                         buf3:W8.t A.t, _RATE8:int) : W256.t Array25.t *
                                                             W8.t A.t *
                                                             W8.t A.t *
                                                             W8.t A.t *
                                                             W8.t A.t = {
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    offset <- 0;
    _LEN <- _ASIZE;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    if ((0 < iTERS)) {
      i <- 0;
      while ((i < iTERS)) {
        st <@ M._keccakf1600_avx2x4 (st);
        (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, 
        buf1, buf2, buf3, offset, _RATE8, st);
        i <- (i + 1);
      }
    } else {
      
    }
    if ((0 < lO)) {
      st <@ M._keccakf1600_avx2x4 (st);
      (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, buf1,
      buf2, buf3, offset, lO, st);
    } else {
      
    }
    return (st, buf0, buf1, buf2, buf3);
  }
}.


(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_bcast_avx2x4_ll: islossless MM.__addstate_bcast_avx2x4.
proof.
proc.
seq 7: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.

lemma addstate_avx2x4_ll: islossless MM.__addstate_avx2x4.
proof.
proc.
seq 7: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
by auto => /#.
qed.

hoare addstate_avx2x4_h _st _at _buf0 _buf1 _buf2 _buf3 _off _len _tb:
 MM.__addstate_avx2x4
 : st=_st /\ aT=_at /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _off /\ _off + _len <= _ASIZE
 /\ 0 <= _tb < 256
 ==> addstate_res4 _st _at [_buf0; _buf1; _buf2; _buf3] _off _len _tb res.`1 res.`2 res.`3.
proof.
(* the ref scalar __addstate on each lane: aligned prefix, word loop, last word *)
proc => /=.
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 5: (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec4 _st _at [sub _buf0 _off _len; sub _buf1 _off _len; sub _buf2 _off _len; sub _buf3 _off _len] _tb nbase _off offset st aT _LEN _TRAILB
       /\ 0 <= offset).
+ seq 3: (st = _st /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
          /\ offset = _off /\ _LEN = _len /\ _TRAILB = _tb
          /\ 0 <= _at <= 200 /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
          /\ 0 <= _off /\ _off + _len <= _ASIZE /\ 0 <= _tb < 256
          /\ dELTA = 0 /\ aT8 = _at /\ aT = 8 * (_at %/ 8)); first by auto.
  wp; if.
  - wp; ecall (a_ilen_read_upto8_at_h buf3 offset dELTA _LEN _TRAILB aT aT8).
    wp; ecall (a_ilen_read_upto8_at_h buf2 offset dELTA _LEN _TRAILB aT aT8).
    wp; ecall (a_ilen_read_upto8_at_h buf1 offset dELTA _LEN _TRAILB aT aT8).
    wp; ecall (a_ilen_read_upto8_at_h buf0 offset dELTA _LEN _TRAILB aT aT8).
    auto => |> Hat0 Hat1 Hlen Hal Hoff Hosz Htb0 Htb1 Hnal r0 H0 r1 H1 r2 H2 r3 H3.
    split; last by move: H3; rewrite /asubread; smt().
    apply (addstate_spec4_asubread _buf0 _buf1 _buf2 _buf3 [r0.`5; r1.`5; r2.`5; r3.`5] (8 * (_at %/ 8))
             _st _at _off _len _tb _st _ _at 0 _len _tb nbase r3.`4 r3.`1 r3.`2 r3.`3) => //.
    + smt().
    + by rewrite /nbase; smt().
    + by move=> k Hk; rewrite (st4x_get_xor64x4 _st (_at %/ 8)) //; smt().
    + have Hs: forall (w w': W64.t), size (u64bytes w) = size (u64bytes w') by move=> w w'; rewrite /u64bytes !size_to_list.
      rewrite forall4 /=.
      split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H0 H3).
      split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H1 H3).
      split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H2 H3).
      exact H3.
    apply addstate_spec4_init => //; first smt().
    by move=> k Hk; rewrite nth_sub4 // size_sub; smt().
  auto => |> Hat0 Hat1 Hlen Hal Hoff Hosz Htb0 Htb1 Hal8.
  have ->: nbase = 8 * (_at %/ 8) by rewrite /nbase; smt().
  have ->: 8 * (_at %/ 8) = _at by smt().
  apply addstate_spec4_init; first smt().
  by move=> k Hk; rewrite nth_sub4 // size_sub; smt().
(* word loop: word `at %/ 4` of each lane; the spec advances by 8 bytes per iteration *)
seq 2: (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ 0 <= _LEN /\ 0 <= offset /\ at = 4 * (aT %/ 8) + 4 * (_LEN %/ 8)
       /\ addstate_spec4 _st _at [sub _buf0 _off _len; sub _buf1 _off _len; sub _buf2 _off _len; sub _buf3 _off _len] _tb (nbase + 8 * (_LEN %/ 8)) _off offset st (aT + 8 * (_LEN %/ 8)) (_LEN - 8 * (_LEN %/ 8)) _TRAILB).
+ while (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
         /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
         /\ 0 <= _LEN /\ 0 <= offset /\ at %% 4 = 0 /\ aT %/ 8 <= at %/ 4 <= aT %/ 8 + _LEN %/ 8
         /\ addstate_spec4 _st _at [sub _buf0 _off _len; sub _buf1 _off _len; sub _buf2 _off _len; sub _buf3 _off _len] _tb (nbase + 8 * (at %/ 4 - aT %/ 8)) _off offset st (aT + 8 * (at %/ 4 - aT %/ 8)) (_LEN - 8 * (at %/ 4 - aT %/ 8)) _TRAILB).
  + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL Ho Ha4 H1 H2 H Hb.
    split; first smt().
    split; first smt().
    split; first smt().
    pose d := at{m} %/ 4 - aT{m} %/ 8.
    have Hk0 := H 0 _ => //=.
    have Hd0: 0 <= d by smt().
    have Hl8: 8 <= _LEN{m} - 8 * d by smt().
    have Ea: aT{m} + 8 * d = nbase + 8 * d.
     by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    have Hfit: aT{m} + 8 * d + (_LEN{m} - 8 * d) = _at + size (sub _buf0 _off _len).
     by apply (addstate_spec_fit _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    rewrite size_sub // in Hfit.
    have Hal8: aT{m} + 8 * d = 8 * (at{m} %/ 4) by move: Ea; rewrite /d /nbase; smt().
    rewrite (_: (at{m} + 4) %/ 4 - aT{m} %/ 8 = d + 1) 1:/#.
    rewrite (_: nbase + 8 * (d + 1) = (nbase + 8 * d) + 8) 1:/# (_: aT{m} + 8 * (d + 1) = (aT{m} + 8 * d) + 8) 1:/# (_: _LEN{m} - 8 * (d + 1) = (_LEN{m} - 8 * d) - 8) 1:/#.
    apply (addstate_spec4_fullword _buf0 _buf1 _buf2 _buf3 [get64_direct (WA.init8 ("_.[_]" _buf0)) offset{m}; get64_direct (WA.init8 ("_.[_]" _buf1)) offset{m}; get64_direct (WA.init8 ("_.[_]" _buf2)) offset{m}; get64_direct (WA.init8 ("_.[_]" _buf3)) offset{m}] (nbase + 8 * d) _st _at _off _len _tb st{m} _ offset{m} (aT{m} + 8 * d) (_LEN{m} - 8 * d) _TRAILB{m}) => //.
    + smt().
    + by move=> k Hk; rewrite Hal8 (st4x_get_xor64x4 st{m} (at{m} %/ 4)) //; smt().
    + by rewrite forall4.
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz H Ho.
  have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ (H 0 _) => //; smt().
  have E: 4 * (aT{m} %/ 8) %/ 4 - aT{m} %/ 8 = 0 by smt().
  rewrite E /=; split.
  + split; first smt().
    split; first smt().
    split; first smt().
    exact H.
  move=> at0 off0 st0 Hex _ _ Ha H1 H2 Hs.
  have E2: at0 %/ 4 - aT{m} %/ 8 = _LEN{m} %/ 8 by smt().
  split; first smt().
  by move: Hs; rewrite E2.
(* bookkeeping (existential sz, as in the ref proof); when the last word is
   read, aT is aligned and `at` is its word index *)
seq 2: (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ 0 <= _LEN < 8 /\ 0 <= offset
       /\ exists sz, _at <= sz
          /\ addstate_spec4 _st _at [sub _buf0 _off _len; sub _buf1 _off _len; sub _buf2 _off _len; sub _buf3 _off _len] _tb sz _off offset st aT _LEN _TRAILB
          /\ (aT = sz => aT %% 8 = 0 /\ at = 4 * (aT %/ 8))).
+ auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL Ho H.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  split; first by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
  by rewrite /nbase; smt().
if.
+ wp; ecall (a_ilen_read_upto8_at_h buf3 offset 0 _LEN _TRAILB aT aT).
  wp; ecall (a_ilen_read_upto8_at_h buf2 offset 0 _LEN _TRAILB aT aT).
  wp; ecall (a_ilen_read_upto8_at_h buf1 offset 0 _LEN _TRAILB aT aT).
  wp; ecall (a_ilen_read_upto8_at_h buf0 offset 0 _LEN _TRAILB aT aT).
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL0 HL1 Ho sz Hsz H Hal8 Hg r0 H0 r1 H1 r2 H2 r3 H3.
  move: (H 0 _) => //= Hk0.
  have Ea: aT{m} = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ Hk0); smt().
  have [Ha8 Ea4] := Hal8 Ea.
  have Hab: aT{m} < 200 by move: Hk0; rewrite /addstate_spec size_sub //; smt().
  apply (addstate_spec4_finish _buf0 _buf1 _buf2 _buf3 [r0.`5; r1.`5; r2.`5; r3.`5] sz _st _at _off _len _tb
           st{m} _ offset{m} aT{m} _LEN{m} _TRAILB{m} r3.`4 r3.`1 r3.`2 r3.`3) => //.
  + smt().
  + by move=> k Hk; rewrite (st4x_get_xor64x4 st{m} (aT{m} %/ 8)) //; smt().
  have Hs: forall (w w': W64.t), size (u64bytes w) = size (u64bytes w') by move=> w w'; rewrite /u64bytes !size_to_list.
  rewrite forall4 /=.
  split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H0 H3).
  split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H1 H3).
  split; first exact (asubread_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hs _ _) H2 H3).
  exact H3.
(* nothing left: the stream and the trailing byte are already absorbed *)
auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL0 HL1 Ho sz Hsz H _ Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec4_done _buf0 _buf1 _buf2 _buf3 sz _st _at _off _len _tb st{m} offset{m} aT{m} _TRAILB{m}) => //; smt().
qed.

hoare addstate_bcast_avx2x4_h _st _at _buf _off _len _tb:
 MM.__addstate_bcast_avx2x4
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _off /\ _off + _len <= _ASIZE
 /\ 0 <= _tb < 256
 ==> addstate_res4 _st _at [_buf; _buf; _buf; _buf] _off _len _tb res.`1 res.`2 res.`3.
proof.
(* addstate_avx2x4_h with the same (broadcast) word on every lane *)
proc => /=.
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 5: (buf = _buf
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec4 _st _at [sub _buf _off _len; sub _buf _off _len; sub _buf _off _len; sub _buf _off _len] _tb nbase _off offset st aT _LEN _TRAILB
       /\ 0 <= offset).
+ seq 3: (st = _st /\ buf = _buf
          /\ offset = _off /\ _LEN = _len /\ _TRAILB = _tb
          /\ 0 <= _at <= 200 /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0)
          /\ 0 <= _off /\ _off + _len <= _ASIZE /\ 0 <= _tb < 256
          /\ dELTA = 0 /\ aT8 = _at /\ aT = 8 * (_at %/ 8)); first by auto.
  wp; if.
  - wp; ecall (a_ilen_read_bcast_upto8_at_h buf offset dELTA _LEN _TRAILB aT aT8).
    auto => |> Hat0 Hat1 Hlen Hal Hoff Hosz Htb0 Htb1 Hnal r t Et H.
    split; last by move: H; rewrite /asubread; smt().
    rewrite Et (_: 8 * (_at %/ 8) %/ 8 = _at %/ 8) 1:/#.
    apply (addstate_spec4_asubread _buf _buf _buf _buf [t; t; t; t] (8 * (_at %/ 8))
             _st _at _off _len _tb _st _ _at 0 _len _tb nbase r.`4 r.`1 r.`2 r.`3) => //.
    + smt().
    + by rewrite /nbase; smt().
    + by move=> k Hk; rewrite nth4_const // st4x_get_xorbcast //; smt().
    + by move=> k Hk; rewrite !nth4_const.
    apply addstate_spec4_init => //; first smt().
    by move=> k Hk; rewrite nth4_const // size_sub; smt().
  auto => |> Hat0 Hat1 Hlen Hal Hoff Hosz Htb0 Htb1 Hal8.
  have ->: nbase = 8 * (_at %/ 8) by rewrite /nbase; smt().
  have ->: 8 * (_at %/ 8) = _at by smt().
  apply addstate_spec4_init; first smt().
  by move=> k Hk; rewrite nth4_const // size_sub; smt().
(* word loop: one broadcast word per iteration, at = 32 * (word index) *)
seq 2: (buf = _buf
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ 0 <= _LEN /\ 0 <= offset /\ at = 32 * (aT %/ 8 + _LEN %/ 8)
       /\ addstate_spec4 _st _at [sub _buf _off _len; sub _buf _off _len; sub _buf _off _len; sub _buf _off _len] _tb (nbase + 8 * (_LEN %/ 8)) _off offset st (aT + 8 * (_LEN %/ 8)) (_LEN - 8 * (_LEN %/ 8)) _TRAILB).
+ while (buf = _buf
         /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
         /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
         /\ 0 <= _LEN /\ 0 <= offset /\ at %% 32 = 0 /\ aT %/ 8 <= at %/ 32 <= aT %/ 8 + _LEN %/ 8
         /\ addstate_spec4 _st _at [sub _buf _off _len; sub _buf _off _len; sub _buf _off _len; sub _buf _off _len] _tb (nbase + 8 * (at %/ 32 - aT %/ 8)) _off offset st (aT + 8 * (at %/ 32 - aT %/ 8)) (_LEN - 8 * (at %/ 32 - aT %/ 8)) _TRAILB).
  + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL Ho Ha4 H1 H2 H Hb.
    split; first smt().
    split; first smt().
    split; first smt().
    pose d := at{m} %/ 32 - aT{m} %/ 8.
    move: (H 0 _) => //= Hk0.
    have Hd0: 0 <= d by smt().
    have Hl8: 8 <= _LEN{m} - 8 * d by smt().
    have Ea: aT{m} + 8 * d = nbase + 8 * d.
     by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    have Hfit: aT{m} + 8 * d + (_LEN{m} - 8 * d) = _at + size (sub _buf _off _len).
     by apply (addstate_spec_fit _ _ _ _ _ _ _ _ _ _ _ _ _ Hk0); smt().
    rewrite size_sub // in Hfit.
    have Hal8: aT{m} + 8 * d = 8 * (at{m} %/ 32) by move: Ea; rewrite /d /nbase; smt().
    rewrite (_: (at{m} + 32) %/ 32 - aT{m} %/ 8 = d + 1) 1:/#.
    rewrite (_: nbase + 8 * (d + 1) = (nbase + 8 * d) + 8) 1:/# (_: aT{m} + 8 * (d + 1) = (aT{m} + 8 * d) + 8) 1:/# (_: _LEN{m} - 8 * (d + 1) = (_LEN{m} - 8 * d) - 8) 1:/#.
    apply (addstate_spec4_fullword _buf _buf _buf _buf
             [get64_direct (WA.init8 ("_.[_]" _buf)) offset{m}; get64_direct (WA.init8 ("_.[_]" _buf)) offset{m};
              get64_direct (WA.init8 ("_.[_]" _buf)) offset{m}; get64_direct (WA.init8 ("_.[_]" _buf)) offset{m}]
             (nbase + 8 * d) _st _at _off _len _tb st{m} _ offset{m} (aT{m} + 8 * d) (_LEN{m} - 8 * d) _TRAILB{m}) => //.
    + smt().
    + by move=> k Hk; rewrite Hal8 nth4_const // (st4x_get_xorbcast256 st{m} at{m} (at{m} %/ 32)) //; smt().
    + by rewrite forall4.
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz H Ho.
  have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ (H 0 _) => //; smt().
  have E: 32 * (aT{m} %/ 8) %/ 32 - aT{m} %/ 8 = 0 by smt().
  rewrite E /=; split.
  + split; first smt().
    split; first smt().
    split; first smt().
    exact H.
  move=> at0 off0 st0 Hex _ _ Ha H1 H2 Hs.
  have E2: at0 %/ 32 - aT{m} %/ 8 = _LEN{m} %/ 8 by smt().
  split; first smt().
  by move: Hs; rewrite E2.
seq 2: (buf = _buf
       /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ 0 <= _LEN < 8 /\ 0 <= offset
       /\ exists sz, _at <= sz
          /\ addstate_spec4 _st _at [sub _buf _off _len; sub _buf _off _len; sub _buf _off _len; sub _buf _off _len] _tb sz _off offset st aT _LEN _TRAILB
          /\ (aT = sz => aT %% 8 = 0 /\ at = 32 * (aT %/ 8))).
+ auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL Ho H.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  split; first by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
  by rewrite /nbase; smt().
if.
+ wp; ecall (a_ilen_read_bcast_upto8_at_h buf offset 0 _LEN _TRAILB aT aT).
  auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL0 HL1 Ho sz Hsz H Hal8 Hg r t Et H0.
  move: (H 0 _) => //= Hk0.
  have Ea: aT{m} = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ Hk0); smt().
  have [Ha8 Ea4] := Hal8 Ea.
  have Hab: aT{m} < 200 by move: Hk0; rewrite /addstate_spec size_sub //; smt().
  rewrite Et.
  apply (addstate_spec4_finish _buf _buf _buf _buf [t; t; t; t] sz _st _at _off _len _tb
           st{m} _ offset{m} aT{m} _LEN{m} _TRAILB{m} r.`4 r.`1 r.`2 r.`3) => //.
  + smt().
  + by move=> k Hk; rewrite nth4_const // (st4x_get_xorbcast256 st{m} at{m} (aT{m} %/ 8)) //; smt().
  by move=> k Hk; rewrite !nth4_const.
auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL0 HL1 Ho sz Hsz H _ Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec4_done _buf _buf _buf _buf sz _st _at _off _len _tb st{m} offset{m} aT{m} _TRAILB{m}) => //; smt().
qed.

lemma absorb_bcast_avx2x4_ll: islossless MM.__absorb_bcast_avx2x4.
proof.
proc.
seq 4: true => //.
 call addstate_bcast_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_bcast_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 wp; call addstate_bcast_avx2x4_ll.
 by auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

hoare absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _tb _r8:
 MM.__absorb_bcast_avx2x4
 : st=_st /\ buf=_buf /\ _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8.
proof.
(* ref absorb_h on every lane: `offset` bytes of each buffer are absorbed *)
proc => /=.
have HA := _ASIZE_ge0.
seq 3: (buf = _buf
       /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
       /\ 0 <= offset <= _ASIZE /\ _LEN = _ASIZE - offset
       /\ aT = (size _l0 + offset) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf; to_list _buf; to_list _buf; to_list _buf] offset st).
+ sp; if => //; last first.
   auto => |> Hs1 Hs2 Hs3 H Htb0 Htb1 Hg.
   have H4 := pabsorb4_init _ _ _ _ _ [to_list _buf; to_list _buf; to_list _buf; to_list _buf] _ H.
   have Hr8 := pabsorb4_r8 _ _ _ _ _ H4.
   split; first smt().
   split; first smt().
   exact H4.
  wp; while (buf = _buf
             /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
             /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
             /\ iTERS = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 /\ 0 <= i <= iTERS
             /\ offset = _r8 - size _l0 %% _r8 + i * _r8
             /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf; to_list _buf; to_list _buf; to_list _buf] offset st).
  + wp; ecall (keccakf1600_avx2x4_h st); ecall (addstate_bcast_avx2x4_h st 0 buf offset _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hi0 Hi1 IH Hb.
    have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
    have Hm: 0 <= i{m} * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
    have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by rewrite StdOrder.IntOrder.ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_ASIZE - (_r8 - size _l0 %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ???? r Hr.
    have [_ [_ Eoff]] := Hr.
    split; first smt().
    split; first smt().
    have Ha0: (size _l0 + (_r8 - size _l0 %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf; to_list _buf; to_list _buf; to_list _buf]
               (_r8 - size _l0 %% _r8 + i{m} * _r8 + _r8) (st4x_map keccak_f1600_op r.`1).
     apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs IH
              (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_to_list; smt().
    by rewrite Eoff.
  wp; ecall (keccakf1600_avx2x4_h st); wp; ecall (addstate_bcast_avx2x4_h st aT buf offset (_RATE8 - aT) 0); auto => |>.
  move=> Hs1 Hs2 Hs3 H Htb0 Htb1 Hg.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  have H4 := pabsorb4_init _ _ _ _ _ [to_list _buf; to_list _buf; to_list _buf; to_list _buf] _ H.
  have [Hr0 Hr1] := pabsorb4_r8 _ _ _ _ _ H4.
  have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ????? r Hr.
  have [_ [_ Eoff]] := Hr.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   split; first smt().
   have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf; to_list _buf; to_list _buf; to_list _buf]
              (0 + (_r8 - size _l0 %% _r8)) (st4x_map keccak_f1600_op r.`1).
    apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs H4
             (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_to_list; smt().
   by rewrite Eoff.
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs0.
  have Ei: i0 = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 by smt().
  have Ed: _ASIZE - (_r8 - size _l0 %% _r8) = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 + (_ASIZE - (_r8 - size _l0 %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l0 = size _l0 %/ _r8 * _r8 + size _l0 %% _r8 by exact divz_eq.
  have Hq: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
  have Hmd: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite Ei; split; first smt().
  split; first smt().
  split; last smt().
  by rewrite (_: size _l0 + (_r8 - size _l0 %% _r8 + (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8) = (size _l0 %/ _r8 + 1 + (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2x4_h _RATE8 st); ecall (addstate_bcast_avx2x4_h st aT buf offset _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Ho0 Ho1 Hfit H Htb.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  split; first smt().
  move=> ????? r Hr.
  have [Hl _] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (to_list _buf) (to_list _buf) (to_list _buf) (to_list _buf) offset{m} (_ASIZE - offset{m})
                    ((size _l0 + offset{m}) %% _r8) st{m} r.`1 _tb _ _ _ _ _ _ _ Hs H
                    (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_to_list; 1..10: smt().
  rewrite absorb_spec_avx2x4E => k Hk.
  by rewrite st4x_get_map // (Hl Htb) // nth_lcat4.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_bcast_avx2x4_h st aT buf offset _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Hs1 Hs2 Hs3 Ho0 Ho1 Hfit H.
have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
split; first smt().
move=> ????? r Hr.
have [_ H0] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (to_list _buf) (to_list _buf) (to_list _buf) (to_list _buf) offset{m} (_ASIZE - offset{m})
                  ((size _l0 + offset{m}) %% _r8) st{m} r.`1 0 _ _ _ _ _ _ _ Hs H
                  (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_to_list; 1..10: smt().
have [_ [Eat _]] := Hr.
split.
 rewrite pabsorb_spec_avx2x4E !size_cat !size_to_list Hs1 Hs2 Hs3; do 3! (split; first done).
 by move=> k Hk; rewrite nth_lcat4 // H0.
rewrite Eat /=.
have E: (size _l0 + offset{m}) %% _r8 + (_ASIZE - offset{m}) = (size _l0 + _ASIZE) + (- (size _l0 + offset{m}) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l0 + offset{m}) %% _r8 + (_ASIZE - offset{m})) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_bcast_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf _tb _r8:
 [ MM.__absorb_bcast_avx2x4
 : st=_st /\ buf=_buf /\ _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8
  ] = 1%r.
proof.
by conseq absorb_bcast_avx2x4_ll (absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _tb _r8).
qed.

lemma absorb_avx2x4_ll: islossless MM.__absorb_avx2x4.
proof.
proc.
seq 4: true => //.
 call addstate_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  call addstate_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 by wp; call addstate_avx2x4_ll; auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

hoare absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8:
 MM.__absorb_avx2x4
 : st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
 _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8.
proof.
(* ref absorb_h on every lane: `offset` bytes of each buffer are absorbed *)
proc => /=.
have HA := _ASIZE_ge0.
seq 3: (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
       /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
       /\ 0 <= offset <= _ASIZE /\ _LEN = _ASIZE - offset
       /\ aT = (size _l0 + offset) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3] offset st).
+ sp; if => //; last first.
   auto => |> Hs1 Hs2 Hs3 H Htb0 Htb1 Hg.
   have H4 := pabsorb4_init _ _ _ _ _ [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3] _ H.
   have Hr8 := pabsorb4_r8 _ _ _ _ _ H4.
   split; first smt().
   split; first smt().
   exact H4.
  wp; while (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
             /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
             /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
             /\ iTERS = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 /\ 0 <= i <= iTERS
             /\ offset = _r8 - size _l0 %% _r8 + i * _r8
             /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3] offset st).
  + wp; ecall (keccakf1600_avx2x4_h st); ecall (addstate_avx2x4_h st 0 buf0 buf1 buf2 buf3 offset _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Hi0 Hi1 IH Hb.
    have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
    have Hm: 0 <= i{m} * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
    have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by rewrite StdOrder.IntOrder.ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_ASIZE - (_r8 - size _l0 %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ???? r Hr.
    have [_ [_ Eoff]] := Hr.
    split; first smt().
    split; first smt().
    have Ha0: (size _l0 + (_r8 - size _l0 %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3]
               (_r8 - size _l0 %% _r8 + i{m} * _r8 + _r8) (st4x_map keccak_f1600_op r.`1).
     apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs IH
              (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_to_list; smt().
    by rewrite Eoff.
  wp; ecall (keccakf1600_avx2x4_h st); wp; ecall (addstate_avx2x4_h st aT buf0 buf1 buf2 buf3 offset (_RATE8 - aT) 0); auto => |>.
  move=> Hs1 Hs2 Hs3 H Htb0 Htb1 Hg.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  have H4 := pabsorb4_init _ _ _ _ _ [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3] _ H.
  have [Hr0 Hr1] := pabsorb4_r8 _ _ _ _ _ H4.
  have Hat: 0 <= size _l0 %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ????? r Hr.
  have [_ [_ Eoff]] := Hr.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   split; first smt().
   have HH: pabsorb4 _r8 [_l0; _l1; _l2; _l3] [to_list _buf0; to_list _buf1; to_list _buf2; to_list _buf3]
              (0 + (_r8 - size _l0 %% _r8)) (st4x_map keccak_f1600_op r.`1).
    apply (pabsorb4_fill _r8 (size _l0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs H4
             (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr)); rewrite ?size_to_list; smt().
   by rewrite Eoff.
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs0.
  have Ei: i0 = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 by smt().
  have Ed: _ASIZE - (_r8 - size _l0 %% _r8) = (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 + (_ASIZE - (_r8 - size _l0 %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l0 = size _l0 %/ _r8 * _r8 + size _l0 %% _r8 by exact divz_eq.
  have Hq: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8 by apply StdOrder.IntOrder.mulr_ge0 => /#.
  have Hmd: 0 <= (_ASIZE - (_r8 - size _l0 %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite Ei; split; first smt().
  split; first smt().
  split; last smt().
  by rewrite (_: size _l0 + (_r8 - size _l0 %% _r8 + (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8 * _r8) = (size _l0 %/ _r8 + 1 + (_ASIZE - (_r8 - size _l0 %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2x4_h _RATE8 st); ecall (addstate_avx2x4_h st aT buf0 buf1 buf2 buf3 offset _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hs1 Hs2 Hs3 Ho0 Ho1 Hfit H Htb.
  have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
  split; first smt().
  move=> ????? r Hr.
  have [Hl _] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (to_list _buf0) (to_list _buf1) (to_list _buf2) (to_list _buf3) offset{m} (_ASIZE - offset{m})
                    ((size _l0 + offset{m}) %% _r8) st{m} r.`1 _tb _ _ _ _ _ _ _ Hs H
                    (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_to_list; 1..10: smt().
  rewrite absorb_spec_avx2x4E => k Hk.
  by rewrite st4x_get_map // (Hl Htb) // nth_lcat4.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_avx2x4_h st aT buf0 buf1 buf2 buf3 offset _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Hs1 Hs2 Hs3 Ho0 Ho1 Hfit H.
have Hs: forall k, 0 <= k < 4 => size (nth [] [_l0; _l1; _l2; _l3] k) = size _l0 by rewrite forall4 /= Hs1 Hs2 Hs3.
split; first smt().
move=> ????? r Hr.
have [_ H0] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (to_list _buf0) (to_list _buf1) (to_list _buf2) (to_list _buf3) offset{m} (_ASIZE - offset{m})
                  ((size _l0 + offset{m}) %% _r8) st{m} r.`1 0 _ _ _ _ _ _ _ Hs H
                  (addstate_res4_lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr); rewrite ?size_to_list; 1..10: smt().
have [_ [Eat _]] := Hr.
split.
 rewrite pabsorb_spec_avx2x4E !size_cat !size_to_list Hs1 Hs2 Hs3; do 3! (split; first done).
 by move=> k Hk; rewrite nth_lcat4 // H0.
rewrite Eat /=.
have E: (size _l0 + offset{m}) %% _r8 + (_ASIZE - offset{m}) = (size _l0 + _ASIZE) + (- (size _l0 + offset{m}) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l0 + offset{m}) %% _r8 + (_ASIZE - offset{m})) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8:
 [ MM.__absorb_avx2x4
 : st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
 _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8
  ] = 1%r.
proof.
by conseq absorb_avx2x4_ll (absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_avx2x4_ll: islossless MM.__dumpstate_avx2x4.
proof.
proc.
seq 3: true => //.
 while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
by auto => /#.
qed.

hoare dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st:
 MM.__dumpstate_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`2 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3
  /\ res.`5 = _off + _len.
proof.
(* the ref scalar __dumpstate on each lane: 32-byte blocks (one transposed
   4x4 word block), 8-byte words, then the last partial word *)
proc.
seq 2: (0 <= _len <= 200 /\ _off + _len <= _ASIZE /\ _LEN = _len /\ st = _st
        /\ i = 32 * (_len %/ 32) /\ offset = _off + i
        /\ asubwrite4 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 _off i _len i (_len - i)).
+ while (0 <= _len <= 200 /\ _off + _len <= _ASIZE /\ _LEN = _len /\ st = _st
         /\ 0 <= i <= 32 * (_len %/ 32) /\ i %% 32 = 0 /\ offset = _off + i
         /\ asubwrite4 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 _off i _len i (_len - i)).
  + wp; ecall (u64x4_u256x4_h x0 x1 x2 x3); auto => |> &m.
    move=> Hl0 Hl1 Hoff Hi0 Hi1 Hm H Hb r.
    rewrite (get256_init256_at _st (4 * i{m}) (i{m} %/ 8)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 32) (i{m} %/ 8 + 1)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 64) (i{m} %/ 8 + 2)) 1,2:/#.
    rewrite (get256_init256_at _st (4 * i{m} + 96) (i{m} %/ 8 + 3)) 1,2:/#.
    move=> E0 E1 E2 E3.
    do 3! (split; first smt()).
    by apply (asubwrite4_step32 _st _buf0 _buf1 _buf2 _buf3 buf0{m} buf1{m} buf2{m} buf3{m} _off _len i{m} (_off + i{m}) r.`1 r.`2 r.`3 r.`4) => //; smt().
  auto => |> Hl0 Hl1 Hoff; split; first by split; [smt(divz_ge0) | apply asubwrite4_init].
  smt().
seq 1: (0 <= _len <= 200 /\ _off + _len <= _ASIZE /\ _LEN = _len /\ st = _st
        /\ i = 8 * (_len %/ 8) /\ offset = _off + i
        /\ asubwrite4 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 _off i _len i (_len - i)).
+ while (0 <= _len <= 200 /\ _off + _len <= _ASIZE /\ _LEN = _len /\ st = _st
         /\ 32 * (_len %/ 32) <= i <= 8 * (_len %/ 8) /\ i %% 8 = 0 /\ offset = _off + i
         /\ asubwrite4 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 _off i _len i (_len - i)).
  + auto => |> &m.
    move=> Hl0 Hl1 Hoff Hi0 Hi1 Hm H Hb.
    do 3! (split; first smt()).
    have T0: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m}) = _st.[i{m} %/ 8] \bits64 0 by apply (get64_init256_at _st _ i{m} 0); smt().
    have T1: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 8) = _st.[i{m} %/ 8] \bits64 1 by apply (get64_init256_at _st _ i{m} 1); smt().
    have T2: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 16) = _st.[i{m} %/ 8] \bits64 2 by apply (get64_init256_at _st _ i{m} 2); smt().
    have T3: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * i{m} + 24) = _st.[i{m} %/ 8] \bits64 3 by apply (get64_init256_at _st _ i{m} 3); smt().
    by apply (asubwrite4_step8 _st _buf0 _buf1 _buf2 _buf3 buf0{m} buf1{m} buf2{m} buf3{m} _off _len i{m} (_off + i{m})) => //; smt().
  auto => |> &m Hl0 Hl1 Hoff H; split; smt().
if.
+ wp; ecall (a_ilen_write_upto8_h buf3 offset 0 (_LEN %% 8) t3).
  wp; ecall (a_ilen_write_upto8_h buf2 offset 0 (_LEN %% 8) t2).
  wp; ecall (a_ilen_write_upto8_h buf1 offset 0 (_LEN %% 8) t1).
  wp; ecall (a_ilen_write_upto8_h buf0 offset 0 (_LEN %% 8) t0).
  auto => |> &m.
  move=> Hl0 Hl1 Hoff H Hm r0 W0 r1 W1 r2 W2 r3 W3.
  have E8: 8 * (_len %/ 8) %/ 8 = _len %/ 8 by smt().
  have T0: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8))) = _st.[_len %/ 8] \bits64 0.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 0) 1..4:/# E8.
  have T1: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 8) = _st.[_len %/ 8] \bits64 1.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 1) 1..4:/# E8.
  have T2: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 16) = _st.[_len %/ 8] \bits64 2.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 2) 1..4:/# E8.
  have T3: get64_direct (WArray800.init256 ("_.[_]" _st)) (4 * (8 * (_len %/ 8)) + 24) = _st.[_len %/ 8] \bits64 3.
   by rewrite (get64_init256_at _st _ (8 * (_len %/ 8)) 3) 1..4:/# E8.
  move: W0 W1 W2 W3; rewrite T0 T1 T2 T3 => W0 W1 W2 W3.
  have [E0 [E1 [E2 E3]]] := asubwrite4_last _st _buf0 _buf1 _buf2 _buf3 buf0{m} buf1{m} buf2{m} buf3{m} r0.`1 r1.`1 r2.`1 r3.`1 _off _len (_off + 8 * (_len %/ 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ Hm _ _ _ _ _ H W0 W1 W2 W3 => //.
  split; first exact E0.
  split; first exact E1.
  split; first exact E2.
  split; first exact E3.
  smt().
auto => |> &m Hl0 Hl1 Hoff H Hm.
have E: 8 * (_len %/ 8) = _len by smt().
move: H; rewrite E (_: _len - _len = 0) 1:/# => H.
have [E0 [E1 [E2 E3]]] := asubwrite4_fin _ _ _ _ _ _ _ _ _ _ _ _ Hl0 H.
by rewrite E0 E1 E2 E3.
qed.

phoare dumpstate_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _off _len _st:
 [ MM.__dumpstate_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`2 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3
  /\ res.`5 = _off + _len
  ] = 1%r.
proof.
by conseq dumpstate_avx2x4_ll (dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st).
qed.

lemma squeeze_avx2x4_ll: islossless MM.__squeeze_avx2x4.
proof.
proc.
seq 5: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.

hoare squeeze_avx2x4_h _buf0 _buf1 _buf2 _buf3 _st _r8:
 MM.__squeeze_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==>
    res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0))
 /\ res.`3 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1))
 /\ res.`4 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2))
 /\ res.`5 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3)).
proof.
(* ref squeeze_h on every lane; the state itself is iterated on all lanes *)
proc.
seq 5: (0 < _r8 <= 200 /\ _RATE8 = _r8 /\ lO = _ASIZE %% _r8
        /\ st = iter (_ASIZE %/ _r8) keccak_f1600_x4 _st /\ offset = _r8 * (_ASIZE %/ _r8)
        /\ asqueeze4 _r8 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 (_ASIZE %/ _r8) offset).
+ sp; if.
  - while (0 <= i <= _ASIZE %/ _r8 /\ iTERS = _ASIZE %/ _r8 /\ 0 < _r8 <= 200 /\ _RATE8 = _r8
           /\ lO = _ASIZE %% _r8 /\ st = iter i keccak_f1600_x4 _st /\ offset = _r8 * i
           /\ asqueeze4 _r8 _st _buf0 _buf1 _buf2 _buf3 buf0 buf1 buf2 buf3 i offset).
    + wp; ecall (dumpstate_avx2x4_h buf0 buf1 buf2 buf3 offset _RATE8 st); ecall (keccakf1600_avx2x4_h st).
      auto => |> &m.
      move=> Hi0 Hi1 Hr0 Hr1 H Hb.
      have Hl: _r8 * (i{m} + 1) <= _ASIZE by have := mul_divz_le _r8 _ASIZE (i{m}+1) _ _; smt().
      have Est: st4x_map keccak_f1600_op (iter i{m} keccak_f1600_x4 _st) = iter (i{m} + 1) keccak_f1600_x4 _st by rewrite iterS 1:/#.
      split; first smt().
      move=> _ _ _ r; rewrite Est => E0 E1 E2 E3 E5.
      split; first smt().
      split; first done.
      split; first smt().
      rewrite E5 (_: _r8 * i{m} + _r8 = _r8 * (i{m} + 1)) 1:/#.
      by apply (asqueeze4_step _r8 _st _buf0 _buf1 _buf2 _buf3 buf0{m} buf1{m} buf2{m} buf3{m} r.`1 r.`2 r.`3 r.`4 i{m}) => //; smt().
    auto => |> Hr0 Hr1 Hg.
    split; first by split; [smt() | split; [by rewrite iter0 | exact asqueeze4_init]].
    move=> b0 b1 b2 b3 i0 Hex Hi0 Hi1 H.
    have <-: i0 = _ASIZE %/ _r8 by smt().
    done.
  auto => |> Hr0 Hr1 Hg.
  have ->: _ASIZE %/ _r8 = 0 by smt(divz_ge0 _ASIZE_ge0).
  by rewrite iter0 //=; exact asqueeze4_init.
if.
+ ecall (dumpstate_avx2x4_h buf0 buf1 buf2 buf3 offset lO st); ecall (keccakf1600_avx2x4_h st).
  auto => |> &m.
  move=> Hr0 Hr1 H C.
  have Hn: 0 <= _ASIZE %/ _r8 by smt(divz_ge0 _ASIZE_ge0).
  have Est: st4x_map keccak_f1600_op (iter (_ASIZE %/ _r8) keccak_f1600_x4 _st) = iter (_ASIZE %/ _r8 + 1) keccak_f1600_x4 _st by rewrite iterS.
  split; first smt(mul_divz_le).
  move=> _ _ _ r; rewrite Est => E0 E1 E2 E3 _.
  split; first by rewrite divz_pred_pos 1,2:/#.
  by apply (asqueeze4_last _r8 _st _buf0 _buf1 _buf2 _buf3 buf0{m} buf1{m} buf2{m} buf3{m} r.`1 r.`2 r.`3 r.`4) => //.
auto => |> &m Hr0 Hr1 H C.
split; first by rewrite divz_pred_zero 1,2:/#.
by apply (asqueeze4_fin _ _ _ _ _ _ _ _ _ _ _ _ C H).
qed.

phoare squeeze_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _st _r8:
 [ MM.__squeeze_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==>
    res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0))
 /\ res.`3 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1))
 /\ res.`4 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2))
 /\ res.`5 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3))
 ] = 1%r.
proof.
by conseq squeeze_avx2x4_ll (squeeze_avx2x4_h _buf0 _buf1 _buf2 _buf3 _st _r8).
qed.

end KeccakArrayAvx2x4.


