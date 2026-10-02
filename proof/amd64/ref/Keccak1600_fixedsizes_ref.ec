(******************************************************************************
   Keccak1600_fixedsizes_ref.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  REF implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.

from JazzEC require import WArray200.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec.


require import Keccak1600_ref Keccakf1600_ref.
require import Keccakf1600.
require import Keccak1600_subreadwrite.

require import StdOrder.
import IntOrder.

require import BitEncoding.
import BitEncoding.BitChunking.

(* ------------------------------------------------------------------------ *)
(* Generic spec / memread helpers.                                          *)
(* Copied verbatim from amd64/avx2/Keccak1600_fixedsizes_avx2.ec (these are *)
(* representation-agnostic: no AVX2 types appear).  `memread_split` is NOT   *)
(* copied — CryptoSpecs JWordList already provides the same statement.       *)
(* ------------------------------------------------------------------------ *)

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

lemma srspecP lw at l len tb:
 srpre 0 at l len tb =>
 at + len + b2i (tb<>0) <= size lw =>
 srspec lw 0 at l len tb =>
 bytes2state (u8zeros at ++ l ++ [W8.of_int tb])
 = bytes2state lw.
proof.
move=> Hpre Hat H.
move: (H Hpre) => {H}[_ H].
rewrite -!bytes2stbytesP; apply stbytes_inj; rewrite !stwordsK tP => i Hi.
rewrite !get_of_list 1..2:// H ler_maxr 1:/# /=.
rewrite -catA nth_cat size_nseq nth_u8zeros ler_maxr 1:/#.
case: (i<at) => ?; first smt(nth_out).
rewrite nth_cat nth_rcons.
case: (i-at < size l) => ?.
 by rewrite ifT 1:/#.
case: (i - at = size l) => ?; first smt().
rewrite ifF /#.
qed.

lemma srspecP0 lw at l len tb:
 len=0 /\ tb=0 =>
 srpre 0 at l len tb =>
 srspec lw 0 at l len tb =>
 bytes2state (u8zeros at ++ l ++ [W8.of_int tb])
 = bytes2state lw.
proof.
move=> [-> ->] /> Hat Hsz.
have ->: l=[] by smt(size_eq0).
move=> H; move: (H _); first smt().
move => {H}[_ H].
rewrite cats0 /= cats1 -nseqSr 1:/#.
have ->: lw = u8zeros (size lw).
apply (u8prefAt0 _ 0 at [] 0); first 2 smt(nseq0).
by rewrite -cat0s bytes2state_zext eq_sym -cat0s bytes2state_zext.
qed.

op msubread_pre (cur at buf len tb: int): bool =
 0<=cur /\ 0<=at /\ 0<=buf /\ 0<=len /\ 0<=tb<256 /\
 at + len + b2i(tb<>0) <= 200.

lemma msubreadP m lw at buf len tb at1 buf1 len1 tb1:
 msubread_pre 0 at buf len tb =>
 (at+len+b2i(tb<>0) <= size lw) \/ len1=0 /\ tb1=0 =>
 msubread m lw 0 at buf len tb at1 buf1 len1 tb1 =>
 bytes2state (u8zeros at ++ memread m buf len ++ [of_int tb])
 = bytes2state lw
 /\ at1 = at + len + b2i (tb<>0)
 /\ buf1 = buf + len
 /\ len1 = 0
 /\ tb1 = 0.
proof.
move => /> ?????? Hlw H; split; last smt().
case: (at <= size lw) => C; last first.
 have Elen: len=0 by smt().
 have Etb: tb=0 by smt().
 apply (srspecP0 _ _ _ _ _ _ _ H); first smt().
 by move=> />; rewrite Elen size_memread /#.
have HHlw: at + len + b2i (tb <> 0) <= size lw by smt().
apply (srspecP _ _ _ _ _ _ _ H) => //.
by rewrite /srpre size_memread 1:/# /#.
qed.

lemma memread0' mem buf len:
 len <= 0 =>
 memread mem buf len = [].
proof. by move=> ?; rewrite /memread mkseq0_le. qed.

lemma chunk_cat_memread mem r8 l buf len:
 let at = size l %% r8 in
 let lastpos = (at + len) %/ r8 * r8 - at in
 0 < r8 =>
 0 <= len =>
 chunk r8 (l ++ memread mem buf len)
 = chunk r8 (l ++ memread mem buf lastpos).
proof.
move=> /= Hr8 Hlen.
rewrite !(chunk_cat' l) /= 1..2:/# /=; congr.
rewrite chunk_take_eq 1:/# size_cat size_chunkremains size_memread 1:/#.
rewrite take_cat' !size_chunkremains.
case: (r8 <= size l %% r8 + len) => C.
 rewrite ifF 1:/#; congr; congr.
 by rewrite take_memread /#.
rewrite divz_small /=; first smt(size_ge0).
rewrite ifT; first smt(size_ge0).
rewrite take0 /memread mkseq0_le 1:/# cats0.
by rewrite eq_sym chunk_take_eq 1:/# size_chunkremains divz_small 1:/# take0.
qed.

lemma chunkremains_cat_memread mem r8 l buf len tb:
 let at = size l %% r8 in
 let lastpos = (at + len) %/ r8 * r8 - at in
 let lastlen = if r8 <= at + len then (at + len) %% r8 else len in
 0 < r8 =>
 0 <= len =>
 bytes2state (chunkremains r8 (l ++ memread mem buf len) ++ [tb])
 = addstate
    (bytes2state (chunkremains r8 (l ++ memread mem buf lastpos)))
    (bytes2state (u8zeros (if r8 <= size l %% r8 + len then 0 else size l %% r8)
                 ++ memread mem (buf+len-lastlen) lastlen ++ [tb])).
proof.
move=> at lastpos lastlen Hr8 Hlen.
case: (r8 <= at + len) => C.
 rewrite eq_sym chunkremains_cat 1:/# eq_sym chunkremains_cat 1:/#.
 rewrite /chunkremains !drop_cat !size_cat !size_memread 1..2:/#.
 rewrite !size_drop; first smt(size_ge0).
 rewrite ifF 1:/# ifF 1:/#.
 have ->: (size l - size l %/ r8 * r8) = size l %% r8 by smt().
 rewrite eq_sym drop_oversize 1:size_memread 1..2:/#.
 rewrite nseq0_le 1:/# /=.
 rewrite drop_memread 1:/# bytes2state0 addstate_st0; congr; congr.
 by rewrite /lastlen C /= ler_maxr /#.
rewrite {2}/memread mkseq0_le 1:/# cats0.
rewrite chunkremains_cat 1:// chunkremains_small.
 by rewrite size_cat size_chunkremains size_memread /#.
rewrite -!catA bytes2state_cat; congr; congr; congr.
 by rewrite size_chunkremains /#.
rewrite /memread /=; congr; smt().
qed.

(* ------------------------------------------------------------------------ *)
(* Bridges between the extracted WArray200 word-stores and the abstract       *)
(* addstate_at / addstate operations.  These are what let the memory-based    *)
(* `__addstate_m` proof reason at the byte-list level.                        *)
(* ------------------------------------------------------------------------ *)

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

(*
op addstate_at_pred st0 at0 l0 tb0 sz st1 at1 tb1 =
 st1 = addstate_at st0 at0 (take sz (l0++[of_int tb0]))
 /\ at1 = srat sz 0 at0 (size l0) tb0
 /\ tb1 = srtb sz 0 at0 (size l0) tb0.

print msubread.
(*
lemma m_addstate_at_cat m st0 at0 sz0 off0 len0 tb0 sz0 st1 at1 tb1 sz1 st2 at2 tb2:
 addstate_at_pred st0 at0 (memread m off0 len0) tb0 sz0 st1 at1 tb1 =>
 msubread m (memread m (off0+sz0) sz1 =>
 st2 <- stxxx =>
 addstate_at_pred st0 at0 (memread m off0 len0) tb0 (sz0+sz1) st2 (at1+sz1) 
*)
*)
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

(* Append/decomposition of addstate_at: XORing (l1 ++ l2) at offset `at` is
   XORing l1 at `at` then l2 at `at + size l1`.  Drives the loop invariants in
   `addstate_m_h`.  ADMIT — STRATEGY: rewrite all three occurrences with
   `addstate_atE`, then `bytes2state_cat` + `addstateA`; the position bookkeeping
   `u8zeros at ++ l1 ++ l2` vs `u8zeros (at+size l1) ++ l2` matches after
   `size_cat`/`size_nseq`.  (Alternatively prove directly by WArray200.filliE
   byte-wise, three-way split i<at / window / after.) *)
lemma addstate_at_cat st at l1 l2:
 0 <= at =>
(* at + size l1 + size l2 <= 200 =>*)
 addstate_at st at (l1 ++ l2)
 = addstate_at (addstate_at st at l1) (at + size l1) l2.
proof.
move=> H0 (*H1*); rewrite !addstate_atE; 1..3:smt(size_cat size_ge0).
rewrite catA bytes2state_cat addstateA; congr.
by rewrite size_cat size_nseq; congr; congr; congr; congr; smt().
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_m_ll: islossless M.__addstate_m.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc.
swap 1 1.
seq 1: true => />; 1:auto; 1:islossless; last by hoare; auto.
seq 1: #pre => //; first inline*; auto.
if => //.
 seq 3: true => />; 1,4:auto; 2: islossless.
 while true (_LEN %/ 32 - i).
  by move=> z; auto; smt().
 by auto; smt().
seq 2: true => />; 1,4:auto; 2: islossless.
while true (aT + _LEN %/ 8 *8 - at).
 by move=> z; auto; smt().
by auto => /> /#.
qed.

lemma mullR: 
forall (x y z: int), (x + y) * z = x * z + y * z by smt().

print msubread.
(*
at' = max (cur+sz) (at+size l+b2i (tb<>0))
len' = if cur+sz <= at+size l then cur+sz else at+size l
tb' = (u8pref at ++ l ++ [tb]).[at+size l]

msubread _mem (u64bytes w) (8 * (_at %/ 8)) _at _buf _len _tb buf _LEN aT _TRAILB
*)

op addstate_spec st at l tb sz st' at' len' tb' =
 0 <= at
 /\ st' = addstate st (bytes2state (take sz (u8zeros at ++ l ++[of_int tb])))
 /\ len' = (if at < sz then max 0 (at + size l - sz) else size l)
 /\ at' = max at (min sz (at + size l + b2i (tb<>0)))
 /\ tb' = if at+size l < sz then 0 else tb.


(*
H: msubread _mem (u64bytes w0) (8 * (_at %/ 8)) _at _buf _len _tb at0 buf0
     len0 tb0
------------------------------------------------------------------------
addstate_AT base (8 * b2i true) _st _at (memread _mem _buf _len) _tb
  (stwords
     (set64 (stbytes _st) (_at %/ 8) (get64 (stbytes _st) (_at %/ 8) `^` w0)))
  at0 len0 tb0
*)

lemma addstate_spec_init st at l tb sz st1 at1 len1 tb1:
 0 <= sz <= at =>
 st1=st => at1=at => len1=size l => tb1=tb =>
 addstate_spec st at l tb sz st1 at1 len1 tb1.
proof.
move => Hsz />; split; first smt().
split.
 rewrite -catA take_cat' size_nseq ifT 1:/# take_nseq -cat0s bytes2state_zext bytes2state0.
 by rewrite addstateC addstate_st0.
smt(size_ge0).
qed.
 
lemma addstate_spec_len st at l tb sz st1 at1 len1 tb1:
 addstate_spec st at l tb sz st1 at1 len1 tb1 =>
 0 <= len1 <= size l.
proof. move=> />; smt(size_ge0). qed.

lemma addstate_spec_sz st at l tb sz st1 at1 len1 tb1:
 at <= sz =>
 (0 < len1 \/ tb1<>0) =>
 addstate_spec st at l tb sz st1 at1 len1 tb1 =>
 at1 = sz.
proof. by move => />* /#. qed.

lemma addstate_spec_finished st at l tb sz st1 at1 len1 tb1:
 len1=0 => tb1=0 =>
 addstate_spec st at l tb sz st1 at1 len1 tb1 =>
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

lemma addstate_msubread_u64 mem w cur st at buf len tb at0 buf0 len0 tb0 cur1 at1 buf1 len1 tb1:
 0 <= at => 0 <= len =>
 0 <= cur <= at0 < cur+8 => 
 buf0 = buf + len - len0 =>
 cur1 = cur + 8 =>
 addstate_spec st at (memread mem buf len) tb cur st0 at0 len0 tb0 =>
 msubread mem (u64bytes w) cur at0 buf0 len0 tb0 at1 buf1 len1 tb1 =>
 addstate_spec st at (memread mem buf len) tb cur1 (addstate_at st cur (u64bytes w)) at1 len1 tb1.
proof.
move => |> Hat Hlen Hcur Hat0_1 Hat0_2; rewrite /addstate_spec addstate_atE // Hat /= => [#].
move => Hst0 -> -> ->; rewrite size_memread 1:// => Hsub.
split.
 admit.
split.
 admit.
split.
 admit.
admit.
qed.



hoare addstate_m_h _mem _st _at _buf _len _tb:
 M.__addstate_m
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 /\ 0 <= _tb < 256
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
     in Glob.mem=_mem
        /\ res.`1 = addstate_at _st _at l
        /\ res.`2 = _at + _len + b2i (_tb<>0)
        /\ res.`3 = _buf + _len.
proof.
(* STRATEGY (memory absorb-into-state; both hAS_AVX2 branches).

   The postcondition `res.`1 = addstate_at _st _at l` is established in the
   equivalent additive form
      res.`1 = addstate _st (bytes2state (u8zeros _at ++ l))
   (they agree by `addstate_atE`, valid since _at + size l <= 200), because the
   additive form composes over successive word reads via `bytes2state_cat` +
   `addstateA` / `addstate_at_cat`.

   Invariant threaded through every read segment (k = bytes consumed so far):
      st  = addstate _st (bytes2state (u8zeros _at ++ memread _mem _buf k))
      buf = _buf + k
   with the running (aT,_LEN) bookkeeping supplied by the msubread contracts.

   proc; generalise hAS_AVX2 (seq 1 off the __HAS_FEATURE call, do NOT let auto
   fold it to a constant), then:
   1. Alignment prefix  `if (aT %% 8 <> 0)`:
        ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB (8*(aT%%8`s block)) aT);
      the returned word is shifted into place; the store
        stwords (set64_direct (stbytes st) aT8 (get64_direct .. ^ w))
      re-establishes the invariant by `set64_addstate_at` (the msubread fact
      identifies `u64bytes w` with the leading `8-aT%%8` bytes of memread laid at
      offset aT via the `srspec`/shift, discharged with `msubread`/`srspecP`).
   2. `if hAS_AVX2` — prove BOTH branches (feature-independent):
        * AVX2 branch: 32-byte `while` with the invariant above; each iteration
          uses `loadW256_memread` + `set256_addstate_at` + `addstate_atE` +
          `bytes2state_cat`/`memread_split` to append 32 bytes; then the
          `16 <= _LEN%%32` tail (`set128_addstate_at`) and the `8 <= _LEN%%16`
          tail (`set64_addstate_at`).
        * scalar branch: 8-byte `while`, each iteration `loadW64_memread` +
          `set64_addstate_at`, appending 8 bytes.
   3. `aT += 8*(_LEN/8); _LEN %%= 8`  — pure bookkeeping.
   4. Final partial word `if (0 < _LEN%%8 \/ _TRAILB%%256 <> 0)`:
        ecall (m_ilen_read_upto8_at_h ..); store via `set64_addstate_at`; here the
      `msubreadP` finaliser turns the completed msubread chain into
        bytes2state (u8zeros _at ++ memread _mem _buf _len ++ [tb]) = ..
      and `bytes2state_zext` drops the trailing byte when _tb = 0.
   5. Conclude by `addstate_atE` back to the `addstate_at` postcondition.

   Depends on: set64/128/256_addstate_at, addstate_atE, addstate_at_cat,
   bytes2state_cat, memread_split, m_ilen_read_upto8_at_h, msubread{,_u64,_cat},
   msubreadP, loadW{64,128,256}_memread.  Mechanical but long; deferred. *)
proc; simplify.
(* Invariant threaded through the reads (k = bytes of input consumed so far):
     st  = addstate_at _st _at (memread _mem _buf k)
     buf = _buf + k ;  aT = _at + k
   Here `k = _len - _LEN` at the phase boundaries (after the prefix, stmt 2, and
   after the bookkeeping, stmts 4-5).  The hAS_AVX2 loops (stmt 3) keep _LEN fixed
   while advancing buf, so their exit uses the explicit count `8*(_LEN%/8)`. *)

(* stmts 1-2 : __HAS_FEATURE (hAS_AVX2 kept symbolic) + the alignment prefix. *)
pose base:= 8 * (_at %/ 8).
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 2: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb nbase st aT _LEN _TRAILB).
(*
seq 2: (Glob.mem=_mem /\ _TRAILB=_tb /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ st = addstate_at _st _at (memread _mem _buf (_len - _LEN))
       /\ buf = _buf + (_len - _LEN) /\ aT = _at + (_len - _LEN)
       /\ 0 <= _LEN <= _len /\ (aT %% 8 = 0 \/ _LEN = 0)).
*)
+ seq 1: (#pre); first by inline*; auto.
  if => //.
   wp; ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB aT8 aT); auto => |> &m ???????.
   move=> [buf0 len0 tb0 at0 w0] /=.
   move => H; rewrite set64_addstate_at 1:/#.
admit(* w0: W64.t
H: msubread _mem (u64bytes w0) (8 * (_at %/ 8)) _at _buf _len _tb at0 buf0
     len0 tb0
------------------------------------------------------------------------
addstate_spec _st _at (memread _mem _buf _len) _tb nbase
  (addstate_at _st (8 * (_at %/ 8)) (u64bytes w0)) at0 len0 tb0
*).
  auto => |> *.
  have ->@/base: nbase = base by smt().
  by apply addstate_spec_init; smt(size_memread).
(* stmt 3 : if hAS_AVX2 — both branches consume `8*(_LEN%/8)` further aligned bytes. *)
seq 3: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+8*(_LEN%/8)) st (aT+8*(_LEN%/8)) (_LEN-8*(_LEN%/8)) _TRAILB).
 wp; if => //.
 - seq 3: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+32*(_LEN%/32)) st (aT+32*(_LEN%/32)) (_LEN-32*(_LEN%/32)) _TRAILB).
   while (#[/1:8]pre /\ inc = _LEN%/32 /\
          0 <= i <= _LEN%/32 /\ 
          addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+32*i) st (aT+32*i) (_LEN-32*i) _TRAILB).
    auto => |> &m ????????? IH Hb; split; first smt().
    rewrite xorwC set256_addstate_at 1:/#.
    admit (*
IH: addstate_spec _st _at (memread _mem _buf _len) _tb (nbase + 32 * i{m})
      st{m} (aT{m} + 32 * i{m}) (_LEN{m} - 32 * i{m}) _TRAILB{m}
Hb: i{m} < _LEN{m} %/ 32
------------------------------------------------------------------------
addstate_spec _st _at (memread _mem _buf _len) _tb (nbase + 32 * (i{m} + 1))
  (addstate_at st{m} (aT{m} + 32 * i{m}) (u256bytes (loadW256 _mem buf{m})))
  (aT{m} + 32 * (i{m} + 1)) (_LEN{m} - 32 * (i{m} + 1)) _TRAILB{m}
*).
   auto => |> &m ??????? H ?; split. 
have ?: 0<= _LEN{m}.
 move: H; rewrite /addstate_spec => />. smt(size_ge0).
    smt().
   by move => i st1 ???; have ->: i=_LEN{m} %/ 32 by smt().
   seq 1: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_AT nbase (16 * (len0 %/ 16)) _st _at (memread _mem _buf _len) _tb st aT _LEN _TRAILB).
   if => //.
     auto => |> &m ??????? IH Hb.
     admit (*
IH: addstate_AT nbase (32 * (len0 %/ 32)) _st _at (memread _mem _buf _len)
      _tb st1 at1 len1 tb1
H: 16 <= len1 %% 32
------------------------------------------------------------------------
addstate_AT nbase (16 * (len0 %/ 16)) _st _at (memread _mem _buf _len) _tb
  (stwords
     (set128_direct (stbytes st1) (at1 + len1 %/ 32 * 32)
        (truncateu128 (loadW256 _mem buf{m}) `^`
         get128_direct (stbytes st1) (at1 + len1 %/ 32 * 32)))) at1 len1 tb1
*).
    auto => |> ??????? H Hb.
    admit (*
H: addstate_AT nbase (32 * (len0 %/ 32)) _st _at (memread _mem _buf _len) _tb
     st1 at1 len1 tb1
Hb: ! 16 <= len1 %% 32
------------------------------------------------------------------------
addstate_AT nbase (16 * (len0 %/ 16)) _st _at (memread _mem _buf _len) _tb
  st1 at1 len1 tb1
*).
   if => //.
     auto => |> ???????? H Hb.
     admit (*
H: addstate_AT nbase (16 * (len0 %/ 16)) _st _at (memread _mem _buf _len) _tb
     st{`&hr} aT{`&hr} _LEN{`&hr} _TRAILB{`&hr}
Hb: 8 <= _LEN{`&hr} %% 16
------------------------------------------------------------------------
addstate_AT nbase (8 * (len0 %/ 8)) _st _at (memread _mem _buf _len) _tb
  (stwords
     (set64_direct (stbytes st{`&hr}) (aT{`&hr} + _LEN{`&hr} %/ 16 * 16)
        (get64_direct (stbytes st{`&hr}) (aT{`&hr} + _LEN{`&hr} %/ 16 * 16) `^`
         loadW64 _mem buf{`&hr}))) aT{`&hr} _LEN{`&hr} _TRAILB{`&hr}
*).
    auto => |> ???????? H Hb.
    admit (*
H: addstate_AT nbase (16 * (len0 %/ 16)) _st _at (memread _mem _buf _len) _tb
     st{`&hr} aT{`&hr} _LEN{`&hr} _TRAILB{`&hr}
Hb: ! 8 <= _LEN{`&hr} %% 16
------------------------------------------------------------------------
addstate_AT nbase (8 * (len0 %/ 8)) _st _at (memread _mem _buf _len) _tb
  st{`&hr} aT{`&hr} _LEN{`&hr} _TRAILB{`&hr}
*).
 - 
sp; if => //.
 admit.
admit.
qed.

 + (* AVX2 branch : 32-byte `while` then the 16- and 8-byte tails.
       while-invariant (iteration i, consumed c_i = (_len-_LEN)+32*i):
         st = addstate_at _st _at (memread _mem _buf c_i) /\ buf = _buf + c_i
         /\ 0 <= i <= _LEN%/32.
       body: `loadW256_memread` + `set256_addstate_at` + `addstate_at_cat`
             + `memread_split` (append 32 bytes); tails: `set128_addstate_at`
             (16 <= _LEN%%32) and `set64_addstate_at` (8 <= _LEN%%16). *)
    admit.
  (* scalar branch : 8-byte `while`.
     while-invariant (iteration i, consumed (_len-_LEN)+8*i):
       st = addstate_at _st _at (memread _mem _buf ((_len-_LEN)+8*i))
       /\ buf = _buf + (_len-_LEN)+8*i /\ at = aT + 8*i /\ 0 <= i <= _LEN%/8.
     body: `loadW64_memread` + `set64_addstate_at` + `addstate_at_cat`. *)
  admit.
(* stmts 4-5 : aT += 8*(_LEN/8); _LEN %%= 8 — bookkeeping; restores the invariant
   since (_len-_LEN)+8*(_LEN%/8) = _len - _LEN%%8. *)
seq 2: (Glob.mem=_mem /\ _TRAILB=_tb /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ st = addstate_at _st _at (memread _mem _buf (_len - _LEN))
       /\ buf = _buf + (_len - _LEN) /\ aT = _at + (_len - _LEN)
       /\ 0 <= _LEN < 8).
+ auto => /> &m *.
  have E: (_len - _LEN{m}) + 8 * (_LEN{m} %/ 8) = _len - _LEN{m} %% 8 by smt().
  rewrite !E; smt(modz_ge0 ltz_pmod).
(* stmt 6 : final partial word + trailing byte. *)
if.
+ wp; ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB aT aT); auto => /> &m ????????? Hlast.
  move => [buf0 len0 tb0 at0 w0] /= ? Eat0 Ebuf0 ? Etb0; split.
   admit.
  (* ADMIT: the last (shifted) word stored via `set64_addstate_at`, combined with
     the running invariant, gives st = addstate_at _st _at (memread _mem _buf _len
     ++ [tb]); `msubreadP` finalises the msubread chain and `bytes2state_zext`
     drops the trailing byte when _tb = 0.  aT = _at + _len + b2i(_tb<>0). *)
  by rewrite Eat0 Ebuf0 /srincr size_to_list /srfnsh size_cat size_memread /#. 
(* guard false: _LEN = 0 /\ _tb = 0, so l = memread _mem _buf _len and the running
   invariant already gives the postcondition. *)
auto => /> &m *.
have HL: _LEN{m} = 0 by smt().
have HT: _tb = 0 by smt().
rewrite HL HT /= cats0; smt(size_memread).
qed.

phoare addstate_m_ph _mem _st _at _buf _len _tb:
 [ M.__addstate_m
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 /\ 0 <= _tb < 256 
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
     in Glob.mem=_mem
        /\ res.`1 = addstate_at _st _at l
        /\ res.`2 = _at + size l
        /\ res.`3 = _buf + _len
 ] = 1%r.
proof.
by conseq addstate_m_ll (addstate_m_h _mem _st _at _buf _len _tb).
qed.

lemma absorb_m_ll: islossless M.__absorb_m.
proof.
proc; simplify.
seq 2: true => //.
 call addstate_m_ll.
 if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ll.
  call addstate_m_ll.
  by auto => /#.
 wp; call keccakf1600_ll.
 wp; call addstate_m_ll.
 by auto => /#.
if => //.
by call addratebit_ll.
qed.

hoare absorb_m_h _l _mem _buf _len _tb _r8:
 M.__absorb_m
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem _buf _len)
       /\ res.`3 = _buf + _len
     else pabsorb_spec_ref _r8 (_l ++ memread _mem _buf _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + _len.
proof.
(* STRATEGY: direct port of `absorb_m_avx2_h`
   (amd64/avx2/Keccak1600_fixedsizes_avx2.ec:534-699).  The ref state is already
   the logical 25-lane state, so every `stavx2_to_st25` / `stavx2_from_st25` /
   `stavx2INV*` step of that proof is DROPPED and `pabsorb_spec_avx2` becomes
   `pabsorb_spec_ref` (= PABSORB1600 with no packing wrapper), `addstate_avx2`
   becomes `addstate`, `keccakf1600_avx2_h` becomes `keccakf1600_h`,
   `addratebit_avx2_h` becomes `addratebit_h`, and `addstate_m_avx2_h` becomes
   `addstate_m_h` (whose `addstate_at` postcondition is turned into the additive
   `addstate ∘ bytes2state` form via `addstate_atE`).  Skeleton below; the
   spec-arithmetic leaves are the only admits. *)
proc => /=.
pose _at := size _l %% _r8.
pose niters := (_at + _len) %/ _r8.
pose lastlen := if _r8 <= _at + _len then (_at + _len) %% _r8 else _len.
pose lastpos := niters * _r8 - _at.
(* After the multi-block prefix, `st` has absorbed the first `lastpos` bytes and
   `lastlen` bytes remain for the final (partial) block. *)
seq 1: (Glob.mem=_mem /\ _RATE8=_r8 /\ _TRAILB=_tb /\ 0 <= _len /\ 0 <= _buf
       /\ 0 <= _tb < 256
       /\ pabsorb_spec_ref _r8 (_l ++ memread _mem _buf lastpos) st
       /\ buf = _buf + lastpos /\ _LEN = lastlen
       /\ aT = if _r8 <= _at + _len then 0 else _at).
+ (* STRATEGY (multi-block prefix, `if (_RATE8 <= aT+_LEN)`): mirror avx2 552-645.
     `sp; if => //` — the empty case rewrites `lastpos <= 0` with `memread0'`;
     the non-empty case runs the first partial `addstate_m_h` + `keccakf1600_h`,
     then the `while` with invariant
       pabsorb_spec_ref _r8 (_l ++ memread _mem _buf ((i+1)*_r8 - _at)) st
     each iteration `ecall (addstate_m_h ..)` (rewritten to additive form via
     addstate_atE) then `ecall (keccakf1600_h ..)`, closed with `chunkremains_nil`
     (rate-boundary ⇒ empty remainder, discharged by `dvdzP; exists ..`),
     `stateabsorb_iblocks_rcons`, `chunk_cat`/`chunk_size`, `memread_split`. *)
  admit.
(* final partial block + trailing byte *)
case: (_tb <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_h _RATE8 st).
  ecall (addstate_m_h Glob.mem st aT buf _LEN _TRAILB).
  (* STRATEGY: avx2 647-671.  addstate_m_h gives the last block XORed in;
     addratebit_h adds the rate/padding bit; reconcile to
     `ABSORB1600 (of_int _tb) _r8 (_l ++ memread _mem _buf _len)` via
     `chunk_cat_memread` + `chunkremains_cat_memread` (extend buffer from
     `lastpos` to `_len`), `addstate_atE`, `-addstateA` and unfolding
     `ABSORB1600`/`PABSORB1600`/`stateabsorb_last`. *)
  auto => />; admit.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_m_h Glob.mem st aT buf _LEN _TRAILB).
(* STRATEGY: avx2 672-698.  Same chunk_cat_memread / chunkremains_cat_memread
   reconciliation to `pabsorb_spec_ref _r8 (_l ++ memread _mem _buf _len)`, plus
   `bytes2state_zext` for the (absent) trailing byte, and
   `res.`2 = (size _l + _len) %% _r8` by `modzDml`/`modz_small`. *)
auto => />; admit.
qed.

phoare absorb_m_ph _l _mem _buf _len _tb _r8:
 [ M.__absorb_m
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem _buf _len)
       /\ res.`3 = _buf + (max 0 _len)
     else pabsorb_spec_ref _r8 (_l ++ memread _mem _buf _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + _len
 ] = 1%r.
proof.
by conseq absorb_m_ll (absorb_m_h _l _mem _buf _len _tb _r8) => /> /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_m_ll: islossless M.__dumpstate_m.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc => /=.
seq 1: #pre => //; first by inline*; auto.
if => //.
 seq 3: true => //.
  wp; while true (inc - j).
   by move=> z; auto => /#.
  by auto => /#.
 by islossless.
seq 2: true => //.
 while true (_LEN %/ 8 - i).
  by move=> z; auto => /#.
 by auto => /#.
by islossless.
qed.

hoare dumpstate_m_h _mem _buf _len _st:
 M.__dumpstate_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len.
proof.
proc => /=.
admitted.

phoare dumpstate_m_ph _mem _buf _len _st:
 [ M.__dumpstate_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len
 ] = 1%r.
proof.
by conseq dumpstate_m_ll (dumpstate_m_h _mem _buf _len _st).
qed.

lemma squeeze_m_ll: islossless M.__squeeze_m.
proof.
proc; simplify.
seq 2: true => //.
 while true (_LEN %/ _RATE8 - i).
  move => z; auto => />.
  call dumpstate_m_ll.
  call keccakf1600_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_m_ll.
call keccakf1600_ll.
by auto => /#.
qed.

hoare squeeze_m_h _mem _buf _len _st _r8:
 M.__squeeze_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len.
proof.
proc.
admitted.

phoare squeeze_m_ph _mem _buf _len _st _r8:
 [ M.__squeeze_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len
 ] = 1%r.
proof.
by conseq squeeze_m_ll (squeeze_m_h _mem _buf _len _st _r8).
qed.



abstract theory KeccakArrayRef.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

(*
module type MParam = {
  proc keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t
  proc state_init_ref (st:W64.t Array25.t) : W64.t Array25.t
  proc addratebit_ref (st:W64.t Array25.t, _RATE8:int) : W64.t Array25.t
}.
*)

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


module MM = {
  proc __addstate (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                   offset:int, _LEN:int, _TRAILB:int) : W64.t Array25.t *
                                                        int * int = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var t256:W256.t;
    var i:int;
    var t128:W128.t;
    var at:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, 1+2+4);
    dELTA <- 0;
    if (((aT %% 8) <> 0)) {
      aT8 <- (8 * (aT %/ 8));
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, offset,
      dELTA, _LEN, _TRAILB, aT8, aT);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
      aT8 ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0])) aT8) `^` w)
      )));
    } else {

    }
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      i <- 0;
      while ((i < inc)) {
        t256 <-
        (get256_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 32);
        t256 <-
        (t256 `^`
        (get256_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + (32 * i))));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set256_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + (32 * i)) t256)));
        i <- (i + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        t128 <-
        (get128_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 16);
        t128 <-
        (t128 `^`
        (get128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 32) * 32))));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 32) * 32)) t128)));
      } else {

      }
      if ((8 <= (_LEN %% 16))) {
        w <-
        (get64_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 8);
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 16) * 16))
        ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
         (aT + ((_LEN %/ 16) * 16))) `^`
        w))));
      } else {

      }
    } else {
      at <- (aT %/ 8);
      offset <- (offset + dELTA);
      dELTA <- 0;
      while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
        w <- (get64_direct (WA.init8 (fun i_0 => buf.[i_0])) offset);
        offset <- (offset + 8);
        st.[at] <- (st.[at] `^` w);
        at <- (at + 1);
      }
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      aT8 <- aT;
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, offset,
      dELTA, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
      aT8 ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0])) aT8) `^` w)
      )));
    } else {

    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc __absorb (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                 _TRAILB:int, _RATE8:int) : W64.t Array25.t * int = {
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
      (st,  _0, offset) <@ __addstate (st, aT, buf, offset, (_RATE8 - aT),
      0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate (st, 0, buf, offset, _RATE8, 0);
        (* Erased call to spill *)
        st <@ M._keccakf1600 (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {

    }
    (st, aT,  _2) <@ __addstate (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit (st, _RATE8);
    } else {

    }
    return (st, aT);
  }
  proc __dumpstate (buf:W8.t A.t, offset:int, _LEN:int,
                    st:W64.t Array25.t) : W8.t A.t * int = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var t:W64.t;
    var j:int;
    var t256:W256.t;
    var t128:W128.t;
    var i:int;
    var  _0:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, 1+2+4);
    dELTA <- 0;
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      j <- 0;
      while ((j < inc)) {
        t256 <-
        (get256_direct (WArray200.init64 (fun i_0 => st.[i_0])) (32 * j));
        buf <-
        (A.init
        (WA.get8
        (WA.set256_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t256)));
        dELTA <- (dELTA + 32);
        j <- (j + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        t128 <-
        (get128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        ((_LEN %/ 32) * 32));
        buf <-
        (A.init
        (WA.get8
        (WA.set128_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t128)));
        dELTA <- (dELTA + 16);
      } else {

      }
      if ((8 <= (_LEN %% 16))) {
        t <-
        (get64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        ((_LEN %/ 16) * 16));
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t)));
        dELTA <- (dELTA + 8);
      } else {

      }
    } else {
      i <- 0;
      while ((i < (_LEN %/ 8))) {
        t <- st.[i];
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i_0 => buf.[i_0]))
        offset t)));
        offset <- (offset + 8);
        i <- (i + 1);
      }
    }
    if ((0 < (_LEN %% 8))) {
      t <- st.[(_LEN %/ 8)];
      (buf, dELTA,  _0) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA,
      (_LEN %% 8), t);
    } else {

    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc __squeeze (st:W64.t Array25.t, buf:W8.t A.t, _RATE8:int) :
  W64.t Array25.t * W8.t A.t = {
    var offset:int;
    var i:int;
    offset <- 0;
    i <- 0;
    while ((i < (_ASIZE %/ _RATE8))) {
      i <- (i + 1);
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate (buf, offset, _RATE8, st);
    }
    if ((0 < (_ASIZE %% _RATE8))) {
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate (buf, offset, (_ASIZE %% _RATE8), st);
    } else {

    }
    return (st, buf);
  }
}.

lemma addstate_ll: islossless MM.__addstate.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc.
seq 4: true => //; last by islossless.
seq 2: true => //; first by inline*; auto.
seq 1: true => //; first by islossless.
if => //.
 seq 3: true => //; last by islossless.
 wp; while true (inc - i).
  by move=> z; auto => /#.
 by auto => /#.
while true ((aT %/ 8) + (_LEN %/ 8) - at).
 by move=> z; auto => /#.
by auto => /#.
qed.

hoare addstate_h _st _at _buf _off _len _tb:
 MM.__addstate
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ offset + _len <= _ASIZE
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_at _st _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + _len.
proof.
proc => /=.
admitted.

phoare addstate_ph _st _at _buf _off _len _tb:
 [ MM.__addstate
   : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
   /\ 0 <= _at <= 200
   /\ 0 <= _len
   /\ _at + _len <= 200 - b2i (_tb<>0)
   /\ offset + _len <= _ASIZE
   ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
       in res.`1 = addstate_at _st _at l
       /\ res.`2 = _at + size l
       /\ res.`3 = _off + _len] = 1%r.
proof.
by conseq addstate_ll (addstate_h _st _at _buf _off _len _tb).
qed.

lemma absorb_ll: islossless MM.__absorb.
proof.
proc; simplify.
seq 4: true => //.
 call addstate_ll.
 sp 2; if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ll.
  call addstate_ll.
  by auto => /#.
 wp; call keccakf1600_ll.
 wp; call addstate_ll.
 by auto => /#.
if => //.
by call addratebit_ll.
qed.

hoare absorb_h _l _buf _tb _r8:
 MM.__absorb
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8.
proof.
proc.
admitted.

phoare absorb_ph _l _buf _tb _r8:
 [ MM.__absorb
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8
 ] = 1%r.
proof.
by conseq absorb_ll (absorb_h _l _buf _tb _r8); smt(ge0_size).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_ll: islossless MM.__dumpstate.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc => /=.
seq 2: true => //; first by inline*; auto.
if => //.
 seq 3: true => //; last by islossless.
 wp; while true (inc - j).
  by move=> z; auto => /#.
 by auto => /#.
seq 2: true => //; last by islossless.
while true (_LEN %/ 8 - i).
 by move=> z; auto => /#.
by auto => /#.
qed.

hoare dumpstate_h _buf _off _len _st:
 MM.__dumpstate
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len.
proof.
proc.
admitted.

phoare dumpstate_ph _buf _off _len _st:
 [ MM.__dumpstate
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len
 ] = 1%r.
proof.
by conseq dumpstate_ll (dumpstate_h _buf _off _len _st).
qed.

lemma squeeze_ll: islossless MM.__squeeze.
proof.
proc; simplify.
seq 3: true => //.
 while true (_ASIZE %/ _RATE8 - i).
  move => z.
  call dumpstate_ll.
  call keccakf1600_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_ll.
call keccakf1600_ll.
by auto => /#.
qed.

hoare squeeze_h _buf _st _r8:
 MM.__squeeze
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st).
proof.
proc.
admitted.

phoare squeeze_ph _buf _st _r8:
 [ MM.__squeeze
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st)
 ] = 1%r.
proof.
by conseq squeeze_ll (squeeze_h _buf _st _r8).
qed.

end KeccakArrayRef.
