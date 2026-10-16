(******************************************************************************
   Keccak1600_barrays.ec:

   Views from the jasmin2ec `barray` representation (monomorphic byte arrays
   BArrayN) to the word arrays used by the specification (and by the
   array-level lemmas shared with the old extraction model), and the bridge
   lemmas relating the barray operations to the spec-level byte view of the
   state (stbytes / addstate_at / sub).

   Contracts over extracted procedures are stated through these views:
     st25 st = _st ==> st25 res = f _st

   No dependency on the extracted code (Keccak1600_Jazz).
******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86 JByte_array.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

from JazzEC require import WArray200.
from JazzEC require import Array5 Array7 Array25.
from JazzEC require import BArray40 BArray200 BArray208 BArray224
                           BArray800 BArray808 SBArray208_200 SBArray808_800.

require import Keccak1600_statebytes.


(* ========================================================================= *)
(* Views                                                                     *)
(* ========================================================================= *)

(* 25-lane state: BArray200 <-> W64.t Array25.t (= state) *)
op st25 (a: BArray200.t) : state = Array25.init (BArray200.get64 a).
op st200 (s: state) : BArray200.t =
 BArray200.init (fun i => s.[i %/ 8] \bits8 (i %% 8)).

(* 5-lane column buffer (ref permutation): BArray40 <-> W64.t Array5.t *)
op st5 (c: BArray40.t) : W64.t Array5.t = Array5.init (BArray40.get64 c).

(* AVX2 (1-way) packed state: BArray224 <-> W256.t Array7.t *)
op stavx2 (a: BArray224.t) : W256.t Array7.t = Array7.init (BArray224.get256 a).

(* AVX2 4-way interleaved state: BArray800 <-> W256.t Array25.t (state4x) *)
op st4x (a: BArray800.t) : W256.t Array25.t = Array25.init (BArray800.get256 a).
(* lane [k] (0<=k<4) of the 4-way state, as a 25-lane state *)
op st4x_get (a: BArray800.t) (k: int) : state =
 Array25.init (fun i => BArray800.get64 a (4*i + k)).

(* updstate (ref): u64[26] = state ++ status word *)
op ust_state (st: BArray208.t) : state = Array25.init (BArray208.get64 st).
abbrev ust_status (st: BArray208.t) = BArray208.get64 st 25.

(* updstate (4-way): u64[101] = state4x ++ status word *)
op ust_st4x (st: BArray808.t) : W256.t Array25.t =
 Array25.init (BArray808.get256 st).
abbrev ust4x_status (st: BArray808.t) = BArray808.get64 st 100.


(* ========================================================================= *)
(* A. Word slicing                                                           *)
(* ========================================================================= *)

lemma bits64_bits8 (w: W256.t) k j:
 0 <= k < 4 => 0 <= j < 8 =>
 (w \bits64 k) \bits8 j = w \bits8 (8*k + j).
proof.
move=> Hk Hj; apply W8.wordP => b Hb.
rewrite W8u8.bits8iE // W4u64.bits64iE 1:/# W32u8.bits8iE //; congr; ring.
qed.


(* ========================================================================= *)
(* B. Generic byte-array facts (instantiated per size below, and inside the  *)
(*    ReadWriteArray-based theories for the abstract buffer)                 *)
(* ========================================================================= *)

abstract theory BAExtra.

op n : int.
axiom ge0_n : 0 <= n.

clone import ByteArray as B with op size <- n proof ge0_size by exact ge0_n.

(* reading a word = the bytes it covers *)
lemma u64bytes_get64d (a: B.t) o : u64bytes (B.get64d a o) = B.sub a o 8.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u64bytes size_to_list B.size_sub.
rewrite /u64bytes size_to_list => i Hi.
by rewrite nth_to_list // B.get64d_byte // B.nth_sub.
qed.

lemma u128bytes_get128d (a: B.t) o : u128bytes (B.get128d a o) = B.sub a o 16.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u128bytes size_to_list B.size_sub.
rewrite /u128bytes size_to_list => i Hi.
by rewrite nth_to_list // B.get128d_byte // B.nth_sub.
qed.

lemma u256bytes_get256d (a: B.t) o : u256bytes (B.get256d a o) = B.sub a o 32.
proof.
apply (eq_from_nth W8.zero); first by rewrite /u256bytes size_to_list B.size_sub.
rewrite /u256bytes size_to_list => i Hi.
by rewrite nth_to_list // B.get256d_byte // B.nth_sub.
qed.

(* writing a word = filling its bytes *)
lemma set64d_fill (a: B.t) q (x: W64.t):
 B.set64d a q x = B.fill (fun i => (u64bytes x).[i-q]) q 8 a.
proof. by rewrite B.set64dE; congr; apply fun_ext => i; rewrite get_u64bytes. qed.

lemma set128d_fill (a: B.t) q (x: W128.t):
 B.set128d a q x = B.fill (fun i => (u128bytes x).[i-q]) q 16 a.
proof. by rewrite B.set128dE; congr; apply fun_ext => i; rewrite get_u128bytes. qed.

lemma set256d_fill (a: B.t) q (x: W256.t):
 B.set256d a q x = B.fill (fun i => (u256bytes x).[i-q]) q 32 a.
proof. by rewrite B.set256dE; congr; apply fun_ext => i; rewrite get_u256bytes. qed.

(* writing back what was read *)
lemma set64d_get64d (a: B.t) o: B.set64d a o (B.get64d a o) = a.
proof.
apply B.ext_eq => i Hi; rewrite B.get8_set64dE.
by case: (o <= i < o + 8 /\ 0 <= i < n) => C //; rewrite B.get64d_byte 1:/# (_: o + (i - o) = i) 1:/#.
qed.

lemma set128d_get128d (a: B.t) o: B.set128d a o (B.get128d a o) = a.
proof.
apply B.ext_eq => i Hi; rewrite B.get8_set128dE.
by case: (o <= i < o + 16 /\ 0 <= i < n) => C //; rewrite B.get128d_byte 1:/# (_: o + (i - o) = i) 1:/#.
qed.

lemma set256d_get256d (a: B.t) o: B.set256d a o (B.get256d a o) = a.
proof.
apply B.ext_eq => i Hi; rewrite B.get8_set256dE.
by case: (o <= i < o + 32 /\ 0 <= i < n) => C //; rewrite B.get256d_byte 1:/# (_: o + (i - o) = i) 1:/#.
qed.

(* a 64-bit read inside a 256-bit word *)
lemma get64d_get256d (a: B.t) o k:
 0 <= k < 4 => B.get64d a (o + 8*k) = B.get256d a o \bits64 k.
proof.
move=> Hk; apply W8u8.wordP => j Hj.
by rewrite B.get64d_byte // bits64_bits8 // B.get256d_byte 1:/# addzA.
qed.

end BAExtra.

clone BAExtra as BX40  with op n <- 40,  theory B <- BArray40  proof ge0_n by done.
clone BAExtra as BX200 with op n <- 200, theory B <- BArray200 proof ge0_n by done.
clone BAExtra as BX208 with op n <- 208, theory B <- BArray208 proof ge0_n by done.
clone BAExtra as BX224 with op n <- 224, theory B <- BArray224 proof ge0_n by done.
clone BAExtra as BX800 with op n <- 800, theory B <- BArray800 proof ge0_n by done.
clone BAExtra as BX808 with op n <- 808, theory B <- BArray808 proof ge0_n by done.


(* ========================================================================= *)
(* C. BArray200 <-> state                                                    *)
(* ========================================================================= *)

lemma st25E a i: 0 <= i < 25 => (st25 a).[i] = BArray200.get64 a i.
proof. by move=> Hi; rewrite /st25 Array25.initiE. qed.

(* the pivot: the bytes of st200 are those of the spec byte view *)
lemma get8_st200 s i: (st200 s).[i] = (stbytes s).[i].
proof.
case: (0 <= i < 200) => Hi.
 by rewrite /st200 BArray200.initiE 1:// /WArray200.init64 WArray200.initiE.
by rewrite BArray200.get_out 1:// WArray200.get_out.
qed.

lemma stbytes_st25 a i: (stbytes (st25 a)).[i] = a.[i].
proof.
case: (0 <= i < 200) => Hi; last by rewrite WArray200.get_out 1:// BArray200.get_out.
rewrite /WArray200.init64 WArray200.initiE 1:// /= st25E 1:/#.
by rewrite BArray200.get64d_byte 1:/# (_: 8 * (i %/ 8) + i %% 8 = i) 1:/#.
qed.

lemma st200K s: st25 (st200 s) = s.
proof. by apply stbytes_inj; rewrite WArray200.tP => i Hi; rewrite stbytes_st25 get8_st200. qed.

lemma st25K a: st200 (st25 a) = a.
proof. by rewrite BArray200.tP => i Hi; rewrite get8_st200 stbytes_st25. qed.

lemma st25_inj a b: st25 a = st25 b => a = b.
proof. by move=> E; rewrite -(st25K a) E st25K. qed.

lemma st200_inj s t: st200 s = st200 t => s = t.
proof. by move=> E; rewrite -(st200K s) E st200K. qed.

lemma st25_set64d a o w:
 0 <= o < 200 => o %% 8 = 0 =>
 st25 (BArray200.set64d a o w) = (st25 a).[o %/ 8 <- w].
proof.
move=> Ho H8; rewrite Array25.tP => j Hj.
rewrite Array25.get_setE 1:/# !st25E 1,2://.
case: (j = o %/ 8) => C.
 by rewrite BArray200.get_set64dE_eq 1..3:/#.
by rewrite BArray200.get_set64dE_neq 1:/#.
qed.

lemma st25_set64 a i w:
 0 <= i < 25 => st25 (BArray200.set64 a i w) = (st25 a).[i <- w].
proof. by move=> Hi; rewrite st25_set64d 1,2:/# mulzC mulzK. qed.

(* the iota step (XOR into lane 0) *)
lemma st25_xor0 a w:
 st25 (BArray200.set64d a 0 (BArray200.get64d a 0 `^` w)) = (st25 a).[0 <- (st25 a).[0] `^` w].
proof. by rewrite st25_set64d // st25E. qed.

lemma bytes2state_to_list a: bytes2state (BArray200.to_list a) = st25 a.
proof.
rewrite -bytes2stbytesP; apply stbytes_inj; rewrite stwordsK WArray200.tP => i Hi.
by rewrite WArray200.get_of_list 1:// BArray200.get_to_list stbytes_st25.
qed.

lemma sub_st25 a o n:
 BArray200.sub a o n = WArray200.sub (stbytes (st25 a)) o n.
proof. by rewrite /BArray200.sub /WArray200.sub; congr; apply fun_ext => i; rewrite stbytes_st25. qed.


(* ========================================================================= *)
(* D. State stores and loads as spec-level byte operations                   *)
(*    (byte-offset `d` forms, so that they match the goals however the       *)
(*     [-printing] abbreviations getN/setN are displayed)                    *)
(* ========================================================================= *)

lemma set64d_addstate_at a o w:
 0 <= o =>
 st25 (BArray200.set64d a o (BArray200.get64d a o `^` w))
 = addstate_at (st25 a) o (u64bytes w).
proof.
move=> Ho; apply stbytes_inj; rewrite /addstate_at stwordsK WArray200.tP => i Hi.
have Hsz: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
rewrite stbytes_st25 BArray200.get8_set64dE WArray200.filliE 1:// Hsz stbytes_st25.
case: (o <= i < o + 8) => C; last by smt().
rewrite ifT 1:/# get_u64bytes u64bits8_xor BArray200.get64d_byte 1:/#.
by rewrite (_: o + (i - o) = i) 1:/# stbytes_st25.
qed.

lemma set128d_addstate_at a o w:
 0 <= o =>
 st25 (BArray200.set128d a o (BArray200.get128d a o `^` w))
 = addstate_at (st25 a) o (u128bytes w).
proof.
move=> Ho; apply stbytes_inj; rewrite /addstate_at stwordsK WArray200.tP => i Hi.
have Hsz: size (u128bytes w) = 16 by rewrite /u128bytes size_to_list.
rewrite stbytes_st25 BArray200.get8_set128dE WArray200.filliE 1:// Hsz stbytes_st25.
case: (o <= i < o + 16) => C; last by smt().
rewrite ifT 1:/# get_u128bytes u128bits8_xor BArray200.get128d_byte 1:/#.
by rewrite (_: o + (i - o) = i) 1:/# stbytes_st25.
qed.

lemma set256d_addstate_at a o w:
 0 <= o =>
 st25 (BArray200.set256d a o (BArray200.get256d a o `^` w))
 = addstate_at (st25 a) o (u256bytes w).
proof.
move=> Ho; apply stbytes_inj; rewrite /addstate_at stwordsK WArray200.tP => i Hi.
have Hsz: size (u256bytes w) = 32 by rewrite /u256bytes size_to_list.
rewrite stbytes_st25 BArray200.get8_set256dE WArray200.filliE 1:// Hsz stbytes_st25.
case: (o <= i < o + 32) => C; last by smt().
rewrite ifT 1:/# get_u256bytes u256bits8_xor BArray200.get256d_byte 1:/#.
by rewrite (_: o + (i - o) = i) 1:/# stbytes_st25.
qed.

(* the extracted code XORs in the order `t `^` get` for 128/256-bit stores *)
lemma set128d_addstate_at' a o w:
 0 <= o =>
 st25 (BArray200.set128d a o (w `^` BArray200.get128d a o))
 = addstate_at (st25 a) o (u128bytes w).
proof. by move=> Ho; rewrite W128.xorwC set128d_addstate_at. qed.

lemma set256d_addstate_at' a o w:
 0 <= o =>
 st25 (BArray200.set256d a o (w `^` BArray200.get256d a o))
 = addstate_at (st25 a) o (u256bytes w).
proof. by move=> Ho; rewrite W256.xorwC set256d_addstate_at. qed.

(* a 256-bit store over four whole lanes *)
lemma st25_set256d a o w:
 0 <= o => o %% 8 = 0 => o + 32 <= 200 =>
 st25 (BArray200.set256d a o w)
 = Array25.init (fun k => if o <= 8*k < o + 32 then w \bits64 (k - o %/ 8) else (st25 a).[k]).
proof.
move=> H0 H8 H32; rewrite Array25.tP => k Hk.
rewrite st25E 1:// Array25.initiE 1:// /=; apply W8u8.wordP => j Hj.
rewrite BArray200.get64d_byte 1:// BArray200.get8_set256dE.
case: (o <= 8*k < o + 32) => C.
 rewrite ifT 1:/# bits64_bits8 1,2:/#; congr; smt().
by rewrite ifF 1:/# st25E 1:// BArray200.get64d_byte.
qed.

(* `st.[:u8 r8-1] ^= 0x80` *)
lemma set8d_addratebit a r8:
 st25 (BArray200.set8d a (r8 - 1) (BArray200.get8d a (r8 - 1) `^` W8.of_int 128))
 = addratebit r8 (st25 a).
proof.
apply stbytes_inj; rewrite /addratebit /addratebit8 stwordsK WArray200.tP => i Hi.
rewrite stbytes_st25 BArray200.get_set_if WArray200.get_set_if !stbytes_st25.
by rewrite /BArray200.size.
qed.

(* dump side: the bytes read from the state *)
lemma u64bytes_get64d_st25 a o:
 u64bytes (BArray200.get64d a o) = WArray200.sub (stbytes (st25 a)) o 8.
proof. by rewrite BX200.u64bytes_get64d sub_st25. qed.

lemma u128bytes_get128d_st25 a o:
 u128bytes (BArray200.get128d a o) = WArray200.sub (stbytes (st25 a)) o 16.
proof. by rewrite BX200.u128bytes_get128d sub_st25. qed.

lemma u256bytes_get256d_st25 a o:
 u256bytes (BArray200.get256d a o) = WArray200.sub (stbytes (st25 a)) o 32.
proof. by rewrite BX200.u256bytes_get256d sub_st25. qed.

(* reads from the barray image of a spec state = the spec byte-view reads *)
lemma get64d_st200 s o:
 BArray200.get64d (st200 s) o = WArray200.get64_direct (stbytes s) o.
proof. by apply W8u8.wordP => j Hj; rewrite BArray200.get64d_byte // get64_bits8 // get8_st200. qed.

lemma get128d_st200 s o:
 BArray200.get128d (st200 s) o = WArray200.get128_direct (stbytes s) o.
proof. by apply W16u8.wordP => j Hj; rewrite BArray200.get128d_byte // get128_bits8 // get8_st200. qed.

lemma get256d_st200 s o:
 BArray200.get256d (st200 s) o = WArray200.get256_direct (stbytes s) o.
proof. by apply W32u8.wordP => j Hj; rewrite BArray200.get256d_byte // get256_bits8 // get8_st200. qed.

lemma to_list_st25 a: BArray200.to_list a = state2bytes (st25 a).
proof.
apply (eq_from_nth W8.zero); first by rewrite BArray200.size_to_list size_state2bytes.
move=> i; rewrite BArray200.size_to_list => Hi.
by rewrite BArray200.get_to_list state2bytesE stbytes_st25.
qed.


(* ========================================================================= *)
(* E. BArray40 <-> W64.t Array5.t (ref permutation)                          *)
(* ========================================================================= *)

lemma st5E c i: 0 <= i < 5 => (st5 c).[i] = BArray40.get64 c i.
proof. by move=> Hi; rewrite /st5 Array5.initiE. qed.

lemma st5_set64d c o w:
 0 <= o < 40 => o %% 8 = 0 =>
 st5 (BArray40.set64d c o w) = (st5 c).[o %/ 8 <- w].
proof.
move=> Ho H8; rewrite Array5.tP => j Hj.
rewrite Array5.get_setE 1:/# !st5E 1,2://.
case: (j = o %/ 8) => C.
 by rewrite BArray40.get_set64dE_eq 1..3:/#.
by rewrite BArray40.get_set64dE_neq 1:/#.
qed.

lemma st5_set64 c i w:
 0 <= i < 5 => st5 (BArray40.set64 c i w) = (st5 c).[i <- w].
proof. by move=> Hi; rewrite st5_set64d 1,2:/# mulzC mulzK. qed.


(* ========================================================================= *)
(* F. BArray224 <-> W256.t Array7.t (AVX2 1-way)                             *)
(* ========================================================================= *)

lemma stavx2E a i: 0 <= i < 7 => (stavx2 a).[i] = BArray224.get256 a i.
proof. by move=> Hi; rewrite /stavx2 Array7.initiE. qed.

lemma stavx2_set256d a o w:
 0 <= o < 224 => o %% 32 = 0 =>
 stavx2 (BArray224.set256d a o w) = (stavx2 a).[o %/ 32 <- w].
proof.
move=> Ho H32; rewrite Array7.tP => j Hj.
rewrite Array7.get_setE 1:/# !stavx2E 1,2://.
case: (j = o %/ 32) => C.
 by rewrite BArray224.get_set256dE_eq 1..3:/#.
by rewrite BArray224.get_set256dE_neq 1:/#.
qed.

lemma stavx2_set256 a i w:
 0 <= i < 7 => stavx2 (BArray224.set256 a i w) = (stavx2 a).[i <- w].
proof. by move=> Hi; rewrite stavx2_set256d 1,2:/# mulzC mulzK. qed.

(* XOR of a 256-bit word into register r of the AVX2 state *)
lemma stavx2_xor256 a r w:
 0 <= r < 7 =>
 stavx2 (BArray224.set256d a (32 * r) (BArray224.get256d a (32 * r) `^` w))
 = (stavx2 a).[r <- (stavx2 a).[r] `^` w].
proof. by move=> Hr; rewrite stavx2_set256d 1,2:/# stavx2E 1:/# (_: 32 * r %/ 32 = r) 1:/#. qed.

(* the same at a byte offset (literal offsets after simplification) *)
lemma stavx2_xor256d a o w:
 0 <= o < 224 => o %% 32 = 0 =>
 stavx2 (BArray224.set256d a o (BArray224.get256d a o `^` w))
 = (stavx2 a).[o %/ 32 <- (stavx2 a).[o %/ 32] `^` w].
proof. by move=> Ho H32; rewrite (_: o = 32 * (o %/ 32)) 1:/# stavx2_xor256 1:/# mulzC mulzK. qed.

lemma stavx2_xor0 a w:
 stavx2 (BArray224.set256d a 0 (BArray224.get256d a 0 `^` w))
 = (stavx2 a).[0 <- (stavx2 a).[0] `^` w].
proof. by have /= := stavx2_xor256 a 0 w. qed.

lemma stavx2_inj a b: stavx2 a = stavx2 b => a = b.
proof.
move=> E; apply BArray224.ext_eq256 => x Hx.
by rewrite -!stavx2E 1,2:/# E.
qed.

(* the barray image of an AVX2 spec state *)
op stavx2_of (s: W256.t Array7.t) : BArray224.t = BArray224.of_list256 (Array7.to_list s).

lemma get256d_stavx2_of s o:
 0 <= o < 224 => o %% 32 = 0 =>
 BArray224.get256d (stavx2_of s) o = s.[o %/ 32].
proof.
move=> Ho H32; rewrite (_: o = 32 * (o %/ 32)) 1:/# /stavx2_of BArray224.get256_of_list256.
+ by rewrite Array7.size_to_list.
by rewrite (_: 32 * (o %/ 32) %/ 32 = o %/ 32) 1:/# (nth_change_dfl witness) 1:Array7.size_to_list 1:/# Array7.get_to_list.
qed.
hint simplify get256d_stavx2_of.

lemma stavx2_ofK s: stavx2 (stavx2_of s) = s.
proof. by rewrite Array7.tP => i Hi; rewrite stavx2E // get256d_stavx2_of 1,2:/# mulzC mulzK. qed.

lemma stavx2K a: stavx2_of (stavx2 a) = a.
proof. by apply stavx2_inj; rewrite stavx2_ofK. qed.



(* ========================================================================= *)
(* G. BArray800 <-> W256.t Array25.t (AVX2 4-way)                            *)
(* ========================================================================= *)

lemma st4xE a i: 0 <= i < 25 => (st4x a).[i] = BArray800.get256 a i.
proof. by move=> Hi; rewrite /st4x Array25.initiE. qed.

lemma st4x_set256d a o w:
 0 <= o < 800 => o %% 32 = 0 =>
 st4x (BArray800.set256d a o w) = (st4x a).[o %/ 32 <- w].
proof.
move=> Ho H32; rewrite Array25.tP => j Hj.
rewrite Array25.get_setE 1:/# !st4xE 1,2://.
case: (j = o %/ 32) => C.
 by rewrite BArray800.get_set256dE_eq 1..3:/#.
by rewrite BArray800.get_set256dE_neq 1:/#.
qed.

lemma st4x_set256 a i w:
 0 <= i < 25 => st4x (BArray800.set256 a i w) = (st4x a).[i <- w].
proof. by move=> Hi; rewrite st4x_set256d 1,2:/# mulzC mulzK. qed.

lemma st4x_inj a b: st4x a = st4x b => a = b.
proof.
move=> E; apply BArray800.ext_eq256 => x Hx.
by rewrite -!st4xE 1,2:/# E.
qed.

(* lane k of the 4-way state, word i *)
lemma st4x_getE a k i:
 0 <= k < 4 => 0 <= i < 25 => (st4x_get a k).[i] = (st4x a).[i] \bits64 k.
proof.
move=> Hk Hi; rewrite /st4x_get Array25.initiE 1:// /= st4xE 1://.
by rewrite (_: 8 * (4 * i + k) = 32 * i + 8 * k) 1:/# BX800.get64d_get256d.
qed.


(* a 64-bit store at byte offset o touches lane (o/8) mod 4, word o/32 *)
lemma st4x_get_set64d a o v k:
 0 <= o < 800 => o %% 8 = 0 => 0 <= k < 4 =>
 st4x_get (BArray800.set64d a o v) k
 = if (o %/ 8) %% 4 = k then (st4x_get a k).[o %/ 32 <- v] else st4x_get a k.
proof.
move=> Ho H8 Hk; rewrite Array25.tP => i Hi.
case: ((o %/ 8) %% 4 = k) => C.
 rewrite Array25.get_setE 1:/# /st4x_get !Array25.initiE 1,2:// /=.
 case: (i = o %/ 32) => Ci.
  by rewrite BArray800.get_set64dE_eq 1..3:/#.
 by rewrite BArray800.get_set64dE_neq 1:/#.
by rewrite /st4x_get !Array25.initiE 1,2:// /= BArray800.get_set64dE_neq 1:/#.
qed.

lemma st4x_get_xor64d a o t k:
 0 <= o < 800 => o %% 8 = 0 => 0 <= k < 4 =>
 st4x_get (BArray800.set64d a o (BArray800.get64d a o `^` t)) k
 = if (o %/ 8) %% 4 = k
   then addstate_at (st4x_get a k) (8 * (o %/ 32)) (u64bytes t)
   else st4x_get a k.
proof.
move=> Ho H8 Hk; rewrite st4x_get_set64d 1..3://.
case: ((o %/ 8) %% 4 = k) => C //.
have E: (st4x_get a k).[o %/ 32] = BArray800.get64d a o.
 by rewrite /st4x_get Array25.initiE 1:/# /=; congr; smt().
by rewrite -setw_addstate_at 1:/# E.
qed.

(* the barray image of a 4-way spec state (inverse of st4x) *)
op st4x_of (s: W256.t Array25.t) : BArray800.t = BArray800.of_list256 (Array25.to_list s).

lemma get256d_st4x_of s o:
 0 <= o < 800 => o %% 32 = 0 =>
 BArray800.get256d (st4x_of s) o = s.[o %/ 32].
proof.
move=> Ho H32; rewrite (_: o = 32 * (o %/ 32)) 1:/# /st4x_of BArray800.get256_of_list256.
+ by rewrite Array25.size_to_list.
by rewrite (_: 32 * (o %/ 32) %/ 32 = o %/ 32) 1:/# (nth_change_dfl witness) 1:Array25.size_to_list 1:/# Array25.get_to_list.
qed.
hint simplify get256d_st4x_of.

lemma get64d_st4x_of s o:
 0 <= o < 800 => o %% 8 = 0 =>
 BArray800.get64d (st4x_of s) o = s.[o %/ 32] \bits64 (o %% 32 %/ 8).
proof.
move=> Ho H8; rewrite {1}(_: o = 32 * (o %/ 32) + 8 * (o %% 32 %/ 8)) 1:/# BX800.get64d_get256d 1:/#.
by rewrite get256d_st4x_of 1,2:/# (_: 32 * (o %/ 32) %/ 32 = o %/ 32) 1:/#.
qed.
hint simplify get64d_st4x_of.

lemma st4x_ofK s: st4x (st4x_of s) = s.
proof. by rewrite Array25.tP => i Hi; rewrite st4xE // get256d_st4x_of 1,2:/# mulzC mulzK. qed.
hint simplify st4x_ofK.

lemma st4xK a: st4x_of (st4x a) = a.
proof. by apply st4x_inj; rewrite st4x_ofK. qed.


(* ========================================================================= *)
(* H. updstate: BArray208 = state ++ status, BArray808 = state4x ++ status   *)
(* ========================================================================= *)

lemma ust_stateE st i: 0 <= i < 25 => (ust_state st).[i] = BArray208.get64 st i.
proof. by move=> Hi; rewrite /ust_state Array25.initiE. qed.

(* `kst = st[0:25]` *)
lemma st25_get_sub64_0 st o:
 o = 0 => st25 (SBArray208_200.get_sub st o) = ust_state st.
proof.
move=> ->; rewrite Array25.tP => i Hi; rewrite st25E 1:// ust_stateE 1://.
by rewrite SBArray208_200.get64d_get_sub 1:/#.
qed.

(* `st[0:25] = kst` *)
lemma ust_state_set_sub64_0 st o k:
 o = 0 => ust_state (SBArray208_200.set_sub st o k) = st25 k.
proof.
move=> ->; rewrite Array25.tP => i Hi; rewrite ust_stateE 1:// st25E 1://.
by rewrite SBArray208_200.get64d_set_sub_in 1:/#.
qed.

lemma ust_status_set_sub64_0 st o k p:
 o = 0 => 200 <= p =>
 BArray208.get64d (SBArray208_200.set_sub st o k) p = BArray208.get64d st p.
proof. by move=> -> Hp; rewrite SBArray208_200.get64d_set_sub_out 1:/#. qed.

(* `st.[:u8 200] = b` *)
lemma ust_state_set8_200 st (b: W8.t):
 ust_state (st.[200 <- b]) = ust_state st.
proof.
rewrite Array25.tP => i Hi; rewrite !ust_stateE 1,2://.
apply W8u8.wordP => j Hj; rewrite !BArray208.get64d_byte 1,2://.
by rewrite BArray208.get_setE 1:// ifF 1:/#.
qed.

lemma ust_status_set8_200 st (b: W8.t) j:
 0 <= j < 8 =>
 ust_status (st.[200 <- b]) \bits8 j = if j = 0 then b else ust_status st \bits8 j.
proof.
move=> Hj; rewrite !BArray208.get64d_byte 1,2://.
by rewrite BArray208.get_setE 1:// /#.
qed.

(* `st.[u64 25] = w` (offset normalised to 200, as in the goals) *)
lemma ust_state_set64d_200 st w:
 ust_state (BArray208.set64d st 200 w) = ust_state st.
proof.
rewrite Array25.tP => i Hi; rewrite !ust_stateE 1,2://.
by rewrite BArray208.get_set64dE_neq 1:/#.
qed.

lemma ust_status_set64d_200 st w:
 BArray208.get64d (BArray208.set64d st 200 w) 200 = w.
proof. by rewrite BArray208.get_set64dE_eq. qed.

lemma ust_st4xE st i: 0 <= i < 25 => (ust_st4x st).[i] = BArray808.get256 st i.
proof. by move=> Hi; rewrite /ust_st4x Array25.initiE. qed.

(* `kst = st[0:25]` (u256) *)
lemma st4x_get_sub256_0 st o:
 o = 0 => st4x (SBArray808_800.get_sub st o) = ust_st4x st.
proof.
move=> ->; rewrite Array25.tP => i Hi; rewrite st4xE 1:// ust_st4xE 1://.
by rewrite SBArray808_800.get256d_get_sub 1:/#.
qed.

(* `st[0:25] = kst` (u256) *)
lemma ust_st4x_set_sub256_0 st o k:
 o = 0 => ust_st4x (SBArray808_800.set_sub st o k) = st4x k.
proof.
move=> ->; rewrite Array25.tP => i Hi; rewrite ust_st4xE 1:// st4xE 1://.
by rewrite SBArray808_800.get256d_set_sub_in 1:/#.
qed.

lemma ust4x_status_set_sub256_0 st o k p:
 o = 0 => 800 <= p =>
 BArray808.get64d (SBArray808_800.set_sub st o k) p = BArray808.get64d st p.
proof. by move=> -> Hp; rewrite SBArray808_800.get64d_set_sub_out 1:/#. qed.
