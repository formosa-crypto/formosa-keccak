(******************************************************************************
   Keccak1600_statebytes.ec:

   Representation-independent support lemmas shared by the Keccak1600 proofs
   (ref, avx2 and avx2x4 variants):
   - the byte view of the Array25 state and its additive updates
     (addstate_at, with the WArray200 word-store bridges);
   - the incremental absorb predicates (addstate_spec for one __addstate
     call, pabsorb_spec for a partially absorbed input) and their
     list-level algebra;
   - the squeeze algebra (SQUEEZE1600 as whole blocks ++ remainder).
   Nothing here mentions an extracted procedure or a word-level read/write
   primitive: the srspec / msubread / asubread / msubwrite / asubwrite glue
   built on this file lives in Keccak1600_subreadwrite.ec.
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.
import IntOrder.
require import BitEncoding.
import BitEncoding.BitChunking.

from Jasmin require import JModel_x86.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

from JazzEC require import WArray200.
from JazzEC require import Array25.

(* ------------------------------------------------------------------------ *)
(* Byte view of the state: XORing a byte list at a byte offset, and the      *)
(* word stores emitted by the extractor as instances of it.                  *)
(* ------------------------------------------------------------------------ *)

op addstate_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill
   (fun i => (stbytes st).[i] `^` l.[i-at]) at (size l) (stbytes st)).

lemma bytes2state_cat l1 l2:
 bytes2state (l1++l2)
 = addstate (bytes2state l1) (bytes2state (u8zeros (size l1)++l2)).
proof.
rewrite -bytes2stbytesP.
have: bytes2stbytes (l1 ++ l2)
      = stbytes (addstate (bytes2state l1) (bytes2state (u8zeros (size l1) ++ l2))).
 rewrite tP stbytes_addstate => i Hi.
 rewrite /addstbytes map2iE // -!bytes2stbytesP !stwordsK !get_of_list // !nth_cat size_nseq ler_maxr.
  smt(size_ge0).
 case: (i < size l1) => C.
  by rewrite nth_u8zeros.
 by rewrite (nth_out _ l1) 1:/#.
by move => ->; rewrite stbytesK.
qed.

lemma stateabsorb_iblocks_rcons l x st:
 stateabsorb_iblocks (rcons l x) st
 = keccak_f1600_op (stateabsorb (stateabsorb_iblocks l st) x).
proof. by rewrite /stateabsorb_iblocks foldl_rcons /=. qed.

(* addstate_at st at l  =  XOR the byte list l into st at byte offset `at`.
   This identifies it with the generic `addstate` of the zero-padded list,
   which is the form the outer absorb proof (and bytes2state_cat) consumes. *)
lemma addstate_atE st at l:
 0 <= at =>
 addstate_at st at l = addstate st (bytes2state (u8zeros at ++ l)).
proof.
move=> Hat.
apply stbytes_inj.
rewrite /addstate_at stwordsK stbytes_addstate.
have ->: stbytes (bytes2state (u8zeros at ++ l)) = bytes2stbytes (u8zeros at ++ l).
 by rewrite -bytes2stbytesP stwordsK.
rewrite /addstbytes tP => i Hi.
rewrite filliE 1:// map2iE 1:// get_of_list 1:// nth_cat size_nseq ler_maxr 1:/# nth_u8zeros.
smt(nth_out nth_change_dfl W8.xorw0).
qed.

(* byte accessors of the word-to-bytes views *)
lemma get_u256bytes i w:
 (u256bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 32) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

lemma get_u128bytes i w:
 (u128bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 16) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

lemma get_u64bytes i w:
 (u64bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 8) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

lemma u64bits8_xor (a b: W64.t) j:
 (a `^` b) \bits8 j = (a \bits8 j) `^` (b \bits8 j).
proof.
apply W8.wordP => k hk.
by rewrite W8.xorwE !bits8iE //.
qed.

lemma u128bits8_xor (a b: W128.t) j:
 (a `^` b) \bits8 j = (a \bits8 j) `^` (b \bits8 j).
proof.
apply W8.wordP => k hk.
by rewrite W8.xorwE !bits8iE //.
qed.

lemma u256bits8_xor (a b: W256.t) j:
 (a `^` b) \bits8 j = (a \bits8 j) `^` (b \bits8 j).
proof.
apply W8.wordP => k hk.
by rewrite W8.xorwE !bits8iE //.
qed.

lemma get64_bits8 (t: WArray200.t) o j:
 0 <= j < 8 =>
 (get64_direct t o) \bits8 j = t.[o + j].
proof. by move=> hj; rewrite get64E pack8bE 1:/# W8u8.Pack.initiE 1:// /=. qed.

lemma get128_bits8 (t: WArray200.t) o j:
 0 <= j < 16 =>
 (get128_direct t o) \bits8 j = t.[o + j].
proof. by move=> hj; rewrite get128E pack16bE 1:/# W16u8.Pack.initiE 1:// /=. qed.

lemma get256_bits8 (t: WArray200.t) o j:
 0 <= j < 32 =>
 (get256_direct t o) \bits8 j = t.[o + j].
proof. by move=> hj; rewrite get256E pack32bE 1:/# W32u8.Pack.initiE 1:// /=. qed.

(* Single u64 store bridge: XORing a word into stbytes at offset o (the shape
   emitted by the extractor: `stwords (set64_direct (stbytes st) o (get64 .. ^ w))`)
   equals adding the word's 8 bytes at offset o. *)
lemma set64_addstate_at st o w:
 0 <= o => (*o + 8 <= 200 =>*)
 stwords (set64_direct (stbytes st) o (get64_direct (stbytes st) o `^` w))
 = addstate_at st o (u64bytes w).
proof.
move=> H0 (*H1*); apply stbytes_inj; rewrite stwordsK /addstate_at stwordsK tP => i Hi.
have Hsz: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
rewrite set64E initiE 1:// filliE 1:// Hsz.
case: (o <= i < o + 8) => C; last by rewrite iffalse 1:/#.
rewrite iftrue 1://.
by rewrite get_u64bytes u64bits8_xor get64_bits8 1:/# (:o + (i-o) = i) 1:/#.
qed.

lemma set128_addstate_at st o w:
 0 <= o => (*o + 16 <= 200 =>*)
 stwords (set128_direct (stbytes st) o (get128_direct (stbytes st) o `^` w))
 = addstate_at st o (u128bytes w).
proof.
move => Ho1 (*Ho2*); apply stbytes_inj; rewrite stwordsK /addstate_at stwordsK tP => i Hi.
have Hsz: size (u128bytes w) = 16 by rewrite /u128bytes size_to_list.
rewrite set128E initiE 1:// filliE 1:// Hsz.
case: (o <= i < o + 16) => C; last by rewrite iffalse 1:/#.
rewrite iftrue 1://.
by rewrite get_u128bytes u128bits8_xor get128_bits8 1:/# (:o + (i-o) = i) 1:/#.
qed.

lemma set256_addstate_at st o w:
 0 <= o => (*o + 32 <= 200 =>*)
 stwords (set256_direct (stbytes st) o (get256_direct (stbytes st) o `^` w))
 = addstate_at st o (u256bytes w).
proof.
move => Ho1 (*Ho2*); apply stbytes_inj; rewrite stwordsK /addstate_at stwordsK tP => i Hi.
have Hsz: size (u256bytes w) = 32 by rewrite /u256bytes size_to_list.
rewrite set256E initiE 1:// filliE 1:// Hsz.
case: (o <= i < o + 32) => C; last by rewrite iffalse 1:/#.
rewrite iftrue 1://.
by rewrite get_u256bytes u256bits8_xor get256_bits8 1:/# (:o + (i-o) = i) 1:/#.
qed.

(* word-indexed XOR of a u64 into the state (array variant's scalar loop) *)
lemma setw_addstate_at (st: W64.t Array25.t) k w:
 0 <= k < 25 =>
 st.[k <- st.[k] `^` w] = addstate_at st (8*k) (u64bytes w).
proof.
move=> Hk; rewrite -set64_addstate_at 1:/#.
have E: forall i, 0 <= i < 25 => WArray200.get64 (stbytes st) i = st.[i].
 by move=> i Hi; rewrite -{2}(stbytesK st) initiE.
rewrite tP => i Hi; rewrite get_setE // initiE //= WArray200.get_set64E 1,2:/#.
by rewrite !E.
qed.

(* ------------------------------------------------------------------------ *)
(* One __addstate call, incrementally: addstate_spec and its interface.      *)
(* ------------------------------------------------------------------------ *)

(* (cur0,cur') is an abstract input cursor (memory pointer `buf` / array
   `offset`): the consumed count is recoverable from the remaining data, so
   the cursor is pinned by `cur' = cur0 + (size l - len')`. *)
op addstate_spec st at l tb sz cur0 cur' st' at' len' tb' =
 0 <= at
 /\ st' = addstate st (bytes2state (take sz (u8zeros at ++ l ++[of_int tb])))
 /\ len' = (if at < sz then max 0 (at + size l - sz) else size l)
 /\ at' = max at (min sz (at + size l + b2i (tb<>0)))
 /\ tb' = (if at+size l < sz then 0 else tb)
 /\ cur' = cur0 + (size l - len').

lemma addstate_spec_init st at l tb sz cur0 cur1 st1 at1 len1 tb1:
 0 <= sz <= at =>
 cur1=cur0 => st1=st => at1=at => len1=size l => tb1=tb =>
 addstate_spec st at l tb sz cur0 cur1 st1 at1 len1 tb1.
proof.
move => Hsz />; split; first smt().
split.
 rewrite -catA take_cat' size_nseq ifT 1:/# take_nseq -cat0s bytes2state_zext bytes2state0.
 by rewrite addstateC addstate_st0.
smt(size_ge0).
qed.

lemma addstate_spec_len st at l tb sz cur0 cur1 st1 at1 len1 tb1:
 addstate_spec st at l tb sz cur0 cur1 st1 at1 len1 tb1 =>
 0 <= len1 <= size l.
proof. move=> />; smt(size_ge0). qed.

lemma addstate_spec_cur st at l tb sz cur0 cur1 st1 at1 len1 tb1:
 addstate_spec st at l tb sz cur0 cur1 st1 at1 len1 tb1 =>
 cur1 = cur0 + (size l - len1).
proof. by move=> />. qed.

lemma addstate_spec_sz st at l tb sz cur0 cur1 st1 at1 len1 tb1:
 at <= sz =>
 (0 < len1 \/ tb1<>0) =>
 addstate_spec st at l tb sz cur0 cur1 st1 at1 len1 tb1 =>
 at1 = sz.
proof. by move => />* /#. qed.

lemma addstate_spec_finished st at l tb sz cur0 cur1 st1 at1 len1 tb1:
 len1=0 => tb1=0 =>
 addstate_spec st at l tb sz cur0 cur1 st1 at1 len1 tb1 =>
 st1 = addstate_at st at (l++[of_int tb]) /\ at1 = at+size l+b2i (tb<>0).
proof.
move => /> Hat.
case: (at<sz) => C1.
 move => ?.
 have ?: at+size l <= sz by smt(size_ge0).
 case: (at + size l = sz) => C2 ?.
  have ->: tb=0 by smt(size_ge0).
  rewrite addstate_atE 1:/#.
  split; last smt().
  rewrite take_cat' size_cat size_nseq ler_maxr 1:/# C2 /= take_oversize.
   by rewrite size_cat size_nseq ler_maxr /#.
  by rewrite catA -nseq1 bytes2state_zext.
 rewrite take_oversize.
  by rewrite !size_cat size_nseq /= /#.
 by rewrite addstate_atE 1:/# catA; smt(size_ge0).
rewrite eq_sym => /size_eq0 -> /=.
rewrite C1 /= => <-; split; last smt(size_ge0).
rewrite addstate_atE 1:/# cats0 take_cat' size_nseq ifT 1:/# take_nseq -nseq1 bytes2state_zext.
by rewrite -cat0s bytes2state_zext bytes2state0 -cat0s bytes2state_zext bytes2state0.
qed.

lemma bytes2state_nthE l1 l2:
 (forall i, 0 <= i < 200 => nth W8.zero l1 i = nth W8.zero l2 i) =>
 bytes2state l1 = bytes2state l2.
proof.
move=> H; rewrite -!bytes2stbytesP; apply stbytes_inj; rewrite !stwordsK tP => i Hi.
by rewrite !get_of_list 1..2:// H.
qed.

(* While data remains, the absorbed position plus the remaining length is the end of the input. *)
lemma addstate_spec_fit st at l tb sz c0 c st' at' len' tb':
 at <= sz => 0 < len' =>
 addstate_spec st at l tb sz c0 c st' at' len' tb' =>
 at' + len' = at + size l.
proof. by move=> Hsz Hl; rewrite /addstate_spec => [#] _ _ El Ea _ _; smt(size_ge0). qed.

(* The trailing byte is absorbed only when non-zero (a zero byte is a no-op). *)
lemma addstate_at_trail st at l tb:
 0 <= at =>
 addstate_at st at (l ++ [W8.of_int tb])
 = addstate_at st at (l ++ if tb <> 0 then [W8.of_int tb] else []).
proof.
move=> Hat; case: (tb <> 0) => // /= ->.
by rewrite cats0 !addstate_atE // catA -nseq1 bytes2state_zext.
qed.

(* The addstate_at postcondition in additive form, with the trailing byte explicit. *)
lemma addstate_at_bytes st at l tb:
 0 <= at =>
 addstate_at st at (l ++ if tb <> 0 then [W8.of_int tb] else [])
 = addstate st (bytes2state (u8zeros at ++ l ++ [W8.of_int tb])).
proof. by move=> Hat; rewrite -addstate_at_trail // addstate_atE // catA. qed.

(* Nothing left to read: the stream (and the trailing byte) is already absorbed. *)
lemma addstate_spec_done (l: W8.t list) n sz st at tb stc c0 c at0 tb0:
 size l = n => 0 <= at => 0 <= tb < 256 => tb0 %% 256 = 0 =>
 addstate_spec st at l tb sz c0 c stc at0 0 tb0 =>
 stc = addstate_at st at (l ++ if tb <> 0 then [W8.of_int tb] else [])
 /\ at0 = at + n + b2i (tb <> 0) /\ c = c0 + n.
proof.
move=> <- Hat Htb Hm H.
have Ht: tb0 = 0 by move: H; rewrite /addstate_spec => [#] _ _ _ _ Etb _; smt().
have [Hst Hat1] := addstate_spec_finished _ _ _ _ _ _ _ _ _ _ _ (eq_refl 0) Ht H.
have Hc := addstate_spec_cur _ _ _ _ _ _ _ _ _ _ _ H.
by rewrite Hst addstate_at_trail // Hat1 Hc.
qed.

(* ------------------------------------------------------------------------ *)
(* Partial absorb of an input list: the predicate and its block algebra      *)
(* (list-generic: the input is an abstract list M of which the first k bytes *)
(* are already absorbed; used by the memory and the array absorbs).          *)
(* ------------------------------------------------------------------------ *)

(* The state after absorbing the whole blocks of l and XORing in its (short)
   remainder; the variants wrap it with their state representation
   (pabsorb_spec_ref, pabsorb_spec_avx2). *)
op PABSORB1600 r8 m =
 stateabsorb (stateabsorb_iblocks (chunk r8 m) st0) (chunkremains r8 m).

op pabsorb_spec r8 (l: W8.t list) (st: state): bool =
 0 < r8 <= 200 /\
 st = addstate (stateabsorb_iblocks (chunk r8 l) st0) (bytes2state (chunkremains r8 l)).

(* Complete the current block: absorb the r8 - a bytes that follow (a is the
   position in the block) and permute.  Covers the first (partial) block
   (k = 0) and every full block (a = 0). *)
lemma pabsorb_fill r8 (l M: W8.t list) k st:
 0 <= k => k + (r8 - (size l + k) %% r8) <= size M =>
 pabsorb_spec r8 (l ++ take k M) st =>
 pabsorb_spec r8 (l ++ take (k + (r8 - (size l + k) %% r8)) M)
   (keccak_f1600_op
     (addstate st (bytes2state (u8zeros ((size l + k) %% r8)
                                ++ take (r8 - (size l + k) %% r8) (drop k M) ++ [W8.zero])))).
proof.
move=> Hk Hfit; rewrite /pabsorb_spec => [[Hr8 Est]]; split => //.
have Ha0: 0 <= (size l + k) %% r8 < r8 by smt(modz_ge0 ltz_pmod).
have HsL: size (l ++ take k M) = size l + k by rewrite size_cat size_take //; smt().
have HsB: size (take (r8 - (size l + k) %% r8) (drop k M)) = r8 - (size l + k) %% r8.
 by rewrite size_take 1:/# size_drop //; smt().
rewrite (takeD M k (r8 - (size l + k) %% r8)) 1,2:/# catA.
pose L := l ++ take k M.
pose B := take (r8 - (size l + k) %% r8) (drop k M).
rewrite (chunk_cat' L) 1:/# (chunk_size _ (chunkremains r8 L ++ B)) 1:/#.
 by rewrite size_cat size_chunkremains HsL HsB; smt().
rewrite (chunkremains_nil r8 (L ++ B)) 1:/#.
 rewrite size_cat HsL HsB; apply dvdzP; exists ((size l + k) %/ r8 + 1).
  have E:= (divz_eq (size l+k) r8); rewrite mulrSl /#.
rewrite (cats1 (chunk r8 L)) stateabsorb_iblocks_rcons bytes2state0 (addstateC _ st0) addstate_st0 /stateabsorb Est.
congr; rewrite -addstateA; congr; first by rewrite /L.
by rewrite /L -nseq1 bytes2state_zext (bytes2state_cat (chunkremains r8 (l ++ take k M))) size_chunkremains HsL.
qed.

(* The final partial block (shorter than a block, so it fits with the trailing
   byte): closes the absorb (tb <> 0) or extends the partial absorb (tb = 0). *)
lemma pabsorb_last r8 (l M: W8.t list) k st tb:
 0 <= k <= size M =>
 (size l + k) %% r8 + (size M - k) < r8 =>
 pabsorb_spec r8 (l ++ take k M) st =>
 (tb <> 0 =>
  addratebit r8 (addstate st (bytes2state (u8zeros ((size l + k) %% r8) ++ drop k M ++ [W8.of_int tb])))
  = ABSORB1600 (W8.of_int tb) r8 (l ++ M))
 /\ (tb = 0 =>
  pabsorb_spec r8 (l ++ M)
    (addstate st (bytes2state (u8zeros ((size l + k) %% r8) ++ drop k M ++ [W8.of_int tb])))).
proof.
move=> Hk Hfit; rewrite /pabsorb_spec => [[Hr8 Est]].
have HsL: size (l ++ take k M) = size l + k by rewrite size_cat size_take //; smt().
have HsR: size (drop k M) = size M - k by rewrite size_drop //; smt().
have EM: l ++ M = (l ++ take k M) ++ drop k M by rewrite -catA cat_take_drop.
have Hsm: size (chunkremains r8 (l ++ take k M) ++ drop k M) < r8.
 by rewrite size_cat size_chunkremains HsL HsR.
have Hch: chunk r8 (l ++ M) = chunk r8 (l ++ take k M).
 by rewrite EM (chunk_cat' (l ++ take k M)) 1:/# (chunk0 r8 (chunkremains r8 (l ++ take k M) ++ drop k M)) // cats0.
have Hcr: chunkremains r8 (l ++ M) = chunkremains r8 (l ++ take k M) ++ drop k M.
 by rewrite EM (chunkremains_cat (l ++ take k M)) 1:/# chunkremains_small.
have Hcat: forall x, bytes2state (chunkremains r8 (l ++ take k M) ++ drop k M ++ [x])
          = addstate (bytes2state (chunkremains r8 (l ++ take k M)))
                     (bytes2state (u8zeros ((size l + k) %% r8) ++ drop k M ++ [x])).
 by move=> x; rewrite -catA bytes2state_cat size_chunkremains HsL catA.
split => Htb.
 rewrite /ABSORB1600 /stateabsorb_last /stateabsorb Hch Hcr -cats1 Hcat Est -addstateA; congr.
split => //; rewrite Hch Hcr Est -addstateA; congr.
by rewrite Htb /= -nseq1 bytes2state_zext (bytes2state_cat (chunkremains r8 (l ++ take k M))) size_chunkremains HsL.
qed.

(* ------------------------------------------------------------------------ *)
(* Squeeze algebra: the bytes a dump writes are chunks [sub (stbytes st) o n] *)
(* of the state's byte view, and SQUEEZE1600 is whole blocks ++ remainder.   *)
(* ------------------------------------------------------------------------ *)

lemma sub_cat (t: WArray200.t) o n1 n2:
 0 <= n1 => 0 <= n2 =>
 sub t o (n1 + n2) = sub t o n1 ++ sub t (o + n1) n2.
proof.
move=> H1 H2; apply (eq_from_nth W8.zero).
 by rewrite size_cat !size_sub /#.
move=> i; rewrite size_sub 1:/# => Hi.
rewrite nth_sub // nth_cat size_sub //.
case: (i < n1) => C; first by rewrite nth_sub /#.
by rewrite nth_sub /#.
qed.

lemma take_sub200 (t: WArray200.t) o n m:
 0 <= n <= m => take n (sub t o m) = sub t o n.
proof.
move=> Hn; apply (eq_from_nth W8.zero).
 by rewrite size_take' 1:/# !size_sub /#.
move=> i; rewrite size_take' 1:/# size_sub 1:/# => Hi.
by rewrite nth_take 1..2:/# !nth_sub /#.
qed.

lemma u256bytes_get256 (t: WArray200.t) o:
 u256bytes (get256_direct t o) = sub t o 32.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u256bytes size_to_list size_sub.
rewrite /u256bytes size_to_list => i Hi.
by rewrite nth_to_list // get256_bits8 // nth_sub.
qed.

lemma u128bytes_get128 (t: WArray200.t) o:
 u128bytes (get128_direct t o) = sub t o 16.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u128bytes size_to_list size_sub.
rewrite /u128bytes size_to_list => i Hi.
by rewrite nth_to_list // get128_bits8 // nth_sub.
qed.

lemma u64bytes_get64 (t: WArray200.t) o:
 u64bytes (get64_direct t o) = sub t o 8.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u64bytes size_to_list size_sub.
rewrite /u64bytes size_to_list => i Hi.
by rewrite nth_to_list // get64_bits8 // nth_sub.
qed.

lemma u64bytes_stword (st: state) i:
 0 <= i < 25 => u64bytes st.[i] = sub (stbytes st) (8*i) 8.
proof.
move=> Hi; rewrite -u64bytes_get64; congr.
by rewrite -{1}(stbytesK st) initiE.
qed.

lemma take_state2bytes st n:
 0 <= n <= 200 => take n (state2bytes st) = sub (stbytes st) 0 n.
proof.
move=> Hn; apply (eq_from_nth W8.zero).
 by rewrite size_take' 1:/# size_state2bytes size_sub /#.
move=> i; rewrite size_take' 1:/# size_state2bytes => Hi.
by rewrite nth_take 1..2:/# state2bytesE nth_sub /#.
qed.

lemma sub_stbytes_4lanes (st: state) k:
 0 <= k => k + 4 <= 25 =>
 sub (stbytes st) (8*k) 32
 = u64bytes st.[k] ++ u64bytes st.[k+1] ++ u64bytes st.[k+2] ++ u64bytes st.[k+3].
proof.
move=> H0 H1; rewrite !u64bytes_stword 1..4:/#.
rewrite (_: 32 = 8 + 24) 1:// sub_cat // (_: 24 = 8 + 16) 1:// sub_cat //.
rewrite (_: 16 = 8 + 8) 1:// sub_cat // !catA.
by rewrite (_: 8*k+8+8+8 = 8*(k+3)) 1:/# (_: 8*k+8+8 = 8*(k+2)) 1:/# (_: 8*k+8 = 8*(k+1)) 1:/#.
qed.

(* Absorbing from [s] bytes: completing the current block and [i] more full
   blocks reaches a block boundary. Used by every fixed-size absorb proof. *)
lemma modz_fill_blocks (s r8 i: int):
 (s + (r8 - s %% r8 + i * r8)) %% r8 = 0.
proof.
rewrite {1}(divz_eq s r8).
have ->: s %/ r8 * r8 + s %% r8 + (r8 - s %% r8 + i * r8) = (s %/ r8 + i + 1) * r8 by ring.
by rewrite modzMl.
qed.

lemma mul_divz_le (r8 len i: int):
 0 < r8 => i <= len %/ r8 => r8 * i <= len.
proof.
move=> Hr Hi; have H1: r8 * i <= r8 * (len %/ r8) by rewrite ler_pmul2l.
by have := lez_floor len r8 _; smt().
qed.

(* number of squeezed blocks: [(len-1)%/r8 + 1] = [len%/r8 + b2i (0 < len%%r8)] *)
lemma divz_pred_pos (r8 len: int):
 0 < r8 => 0 < len %% r8 => (len - 1) %/ r8 = len %/ r8.
proof.
move=> Hr Hm; have Hlt := ltz_pmod len r8 Hr.
have ->: len - 1 = len %/ r8 * r8 + (len %% r8 - 1).
 by rewrite {1}(divz_eq len r8); ring.
by rewrite divzMDl 1:/# (divz_small (len %% r8 - 1) r8) /#.
qed.

lemma divz_pred_zero (r8 len: int):
 0 < r8 => !(0 < len %% r8) => (len - 1) %/ r8 + 1 = len %/ r8.
proof.
move=> Hr Hm; have Hz: len %% r8 = 0 by have := modz_ge0 len r8 _; smt().
have ->: len - 1 = (len %/ r8 - 1) * r8 + (r8 - 1).
 by rewrite {1}(divz_eq len r8) Hz; ring.
by rewrite divzMDl 1:/# (divz_small (r8 - 1) r8) /#.
qed.

lemma squeezeblocks_step r8 st i:
 0 < r8 <= 200 => 0 <= i =>
 squeezeblocks r8 st (i+1)
 = squeezeblocks r8 st i ++ sub (stbytes (st_i st (i+1))) 0 r8.
proof.
move=> Hr Hi; rewrite squeezeblocksS //; congr.
rewrite /= /squeezestate_i /squeezestate take_state2bytes 1:/#.
by rewrite /st_i iter1 iterS.
qed.

lemma SQUEEZE1600_split r8 len st:
 0 < r8 <= 200 => 0 <= len =>
 SQUEEZE1600 r8 len st
 = squeezeblocks r8 st (len %/ r8)
   ++ (if 0 < len %% r8
       then sub (stbytes (st_i st (len %/ r8 + 1))) 0 (len %% r8)
       else []).
proof.
move=> Hr Hlen; rewrite /SQUEEZE1600.
case: (0 < len %% r8) => C.
 rewrite divz_pred_pos 1,2:/#.
 rewrite squeezeblocks_step 1:/# 1:divz_ge0 1:/# 1:/#.
 rewrite take_cat size_squeezeblocks 1:/# 1:divz_ge0 1:/# 1:/#.
 by rewrite ifF 1:/# take_sub200 1:/#; congr; congr; smt().
rewrite cats0 divz_pred_zero 1,2:/#.
rewrite take_oversize // size_squeezeblocks 1:/#; first smt(divz_ge0).
smt().
qed.

(* The i-th output byte is byte (i mod r8) of the state after i/r8+1 permutations. *)
lemma nth_SQUEEZE1600 r8 len st i:
 0 < r8 <= 200 =>
 0 <= i < len =>
 (SQUEEZE1600 r8 len st).[i]
 = (stbytes (st_i st (i %/ r8 + 1))).[i %% r8].
proof.
move=> Hr8 Hi; rewrite /SQUEEZE1600 nth_take 1..2:/# /squeezeblocks.
rewrite (BitEncoding.BitChunking.nth_flatten W8.zero r8).
 apply/List.allP => x /mapP [y [Hy ->]] /=.
 by rewrite size_squeezestate_i /#.
rewrite (nth_map 0).
 rewrite size_iota; split; first smt().
 move=> _; rewrite ltzE lez_maxr 1:/#.
 rewrite StdOrder.IntOrder.ler_add2r.
 smt(leq_div2r).
rewrite /squeezestate_i /squeezestate nth_take 1..2:/#
 state2bytesE; congr; congr; congr; congr.
rewrite nth_iota; split; first smt().
move=> _; rewrite ltzE; smt(leq_div2r).
qed.
