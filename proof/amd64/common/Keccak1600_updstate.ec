(******************************************************************************
   Keccak1600_updstate.ec:

   Shared substrate for the "updstate" (streaming init/absorb/finish/squeeze)
   Keccak1600 proofs (single-lane ref and 4-way avx2x4 variants; memory and
   array buffers). It mirrors the role Keccak1600_statebytes.ec plays for the
   fixed-size proofs:
   - the status word that the updstate code appends to the state
     (byte 0 = cursor `at`, byte 1 = r64-1, byte 2 = trail byte), its decoder
     `_ststatus_data` (single-lane code) and the stores to it;
   - the streaming predicates `absorbing_spec` / `squeezing_spec` used by
     every updstate contract, and the output window `sqstream`;
   - the pure "driver" lemmas that the absorb/finish/squeeze loops of all
     variants instantiate (memory and array alike).
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.
import IntOrder.
require import BitEncoding.
import BitEncoding.BitChunking.

from Jasmin require import JModel_x86.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray208.
from JazzEC require import Array25 Array26.

require import Keccak1600_statebytes Keccak1600_subreadwrite.


(* ========================================================================= *)
(* A. The status word                                                        *)
(* ========================================================================= *)

op ststatus_r8 (s: W64.t) : int =
 let r64 = W64.to_uint ((s `>>` W8.of_int 8) `&` W64.of_int 255) in
 if 200 < 8 * (r64 + 1) then 200 else 8 * (r64 + 1).

op ststatus_at (s: W64.t) : int =
 W64.to_uint (s `&` W64.of_int 255).

op ststatus_trailb (s: W64.t) : W8.t =
 truncateu8 (s `>>` W8.of_int 16).

(* the cursor as normalised by _ststatus_data (0 when r8 <= at) *)
op ststatus_at_norm (s: W64.t) : int =
 let r8 = ststatus_r8 s in
 let at = ststatus_at s in
 if r8 <= at then 0 else at.

op status_spec (w: W64.t) (r8: int) (tb: W8.t) (at: int) =
 ststatus_r8 w = r8 /\ ststatus_trailb w = tb /\ ststatus_at_norm w = at.

lemma ststatus_r8_bounds s:
 8 %| ststatus_r8 s /\ 8 <= ststatus_r8 s <= 200.
proof.
rewrite /ststatus_r8 /=.
have := W64.to_uint_cmp ((s `>>` W8.of_int 8) `&` W64.of_int 255).
case: (200 < 8 * (to_uint ((s `>>` W8.of_int 8) `&` W64.of_int 255) + 1)) => C H.
 by rewrite (: 200 = 8 * 25) 1:// dvdz_mulr //.
by split; [apply dvdz_mulr | smt()].
qed.

lemma ststatus_at_norm_bounds s:
 0 <= ststatus_at_norm s < ststatus_r8 s.
proof.
have := ststatus_r8_bounds s.
rewrite /ststatus_at_norm /ststatus_at /=; smt(W64.to_uint_cmp).
qed.

(* the packing done by the init procedures *)
op encode_ststatus (at r8m1 trailb : int) : W64.t =
 W64.of_int (at + 256 * r8m1 + 65536 * trailb).

lemma encode_ststatusE r64 (tb: W8.t):
 0 < r64 <= 25 =>
 status_spec (encode_ststatus 0 (r64 - 1) (W8.to_uint tb)) (8 * r64) tb 0.
proof.
move=> Hr; pose s := encode_ststatus 0 (r64 - 1) (W8.to_uint tb).
have Ht' : 0 <= to_uint tb < 256 by smt(W8.to_uint_cmp pow2_8).
have Us : W64.to_uint s = 256 * (r64 - 1) + 65536 * to_uint tb.
 by rewrite /s /encode_ststatus of_uintK pmod_small; smt(pow2_64).
have R8 : W64.to_uint ((s `>>` W8.of_int 8) `&` W64.of_int 255) = r64 - 1.
+ rewrite (W64.to_uint_and_mod 8) //.
  rewrite W64.shr_div_le // Us /= (: 256 * (r64 - 1) + 65536 * to_uint tb = (r64 - 1 + 256 * to_uint tb) * 256) 1:/#.
  by rewrite mulzK // (: r64 - 1 + 256 * to_uint tb = (r64 - 1) + to_uint tb * 256) 1:/# modzMDr modz_small /#.
have AT : W64.to_uint (s `&` W64.of_int 255) = 0.
 by rewrite (W64.to_uint_and_mod 8) // Us (: 256 * (r64 - 1) + 65536 * to_uint tb = (r64 - 1 + 256 * to_uint tb) * 256) 1:/# /= modzMl.
have TB : truncateu8 (s `>>` W8.of_int 16) = tb.
+ rewrite /truncateu8 W64.shr_div_le // Us (: 256 * (r64 - 1) + 65536 * to_uint tb = 256 * (r64 - 1) + to_uint tb * 65536) 1:/# /= divzMDr // divz_small 1:/# /=.
  done.
have Er8 : ststatus_r8 s = 8 * r64 by rewrite /ststatus_r8 /= R8; smt().
by rewrite /status_spec Er8 /ststatus_at_norm /ststatus_at /= AT Er8 /ststatus_trailb TB /#.
qed.

(* the init packing (shared by the three init procedures; the extracted
   `W8.to_uint (W8.of_int r64 - W8.of_int 1)` simplifies to `(r64 - 1) %% 256`) *)
lemma init_status r64 (tb: W8.t):
 0 < r64 <= 25 =>
 (zeroextu64 tb `<<` W8.of_int 8) + zeroextu64 (W8.of_int (r64 - 1)) `<<` W8.of_int 8
 = encode_ststatus 0 (r64 - 1) (W8.to_uint tb).
proof.
move=> Hr; have Ht : 0 <= to_uint tb < 256 by smt(W8.to_uint_cmp pow2_8).
rewrite /zeroextu64 /encode_ststatus W8.of_uintK pmod_small 1:/#.
rewrite !W64.shl_shlw // !W64.shlMP //=.
rewrite W64.shlMP //=.
rewrite -W64.of_intM'.
smt().
qed.

(* the stores of the absorb/squeeze epilogues: the 25 lanes, then byte 200 *)
lemma st26_set8_bits8 (s: W64.t Array26.t) (b: W8.t) i j:
 0 <= i < 26 => 0 <= j < 8 =>
 WArray208.get64 (WArray208.init64 (fun i0 => s.[i0])).[200 <- b] i \bits8 j
 = if 8 * i + j = 200 then b else s.[i] \bits8 j.
proof.
move=> Hi Hj; rewrite WArray208.get64E W8u8.pack8bE // W8u8.Pack.initiE //= WArray208.get_setE 1:/#.
by case: (8 * i + j = 200) => C //; rewrite /init64 WArray208.initiE 1:/# /=; congr; smt().
qed.

lemma ststatus_byte0 (w' w: W64.t) (b: W8.t):
 (forall j, 0 <= j < 8 => w' \bits8 j = if j = 0 then b else w \bits8 j) =>
 ststatus_at w' = W8.to_uint b /\ ststatus_r8 w' = ststatus_r8 w /\ ststatus_trailb w' = ststatus_trailb w.
proof.
move=> H; have Hb : forall k, 0 <= k < 64 => w'.[k] = if k < 8 then b.[k] else w.[k].
+ move=> k Hk; rewrite (W8u8.get_bits8 w' k) // (W8u8.get_bits8 w k) // H 1:/#.
  by case: (k < 8) => C; [rewrite ifT 1:/# (: k %% 8 = k) 1:/# | rewrite ifF 1:/#].
have S : forall n, 8 <= n < 64 => w' `>>` W8.of_int n = w `>>` W8.of_int n.
+ move=> n Hn; apply W64.wordP => k Hk; rewrite !W64.shr_shrw 1,2:/# /=.
  by rewrite Hk /=; case: (k + n < 64) => C; [rewrite Hb /# | rewrite !W64.get_out /#].
rewrite /ststatus_r8 /ststatus_trailb (S 8) // (S 16) //=.
rewrite /ststatus_at -W8u8.to_uint_zeroextu64; congr; apply W64.wordP => k Hk.
by rewrite W64.andwE W8u8.zeroextu64_bit (: 255 = 2^8 - 1) 1:// W64.of_int_powm1 // Hb //; case: (k < 8) => C /=; smt().
qed.

abbrev ust_state (st: W64.t Array26.t) : state = Array25.init (fun i => st.[i]).

(* `st[0:25] = stk; st.[:u8 200] = (8u) at` *)
op st26_store (stk: state) (st: W64.t Array26.t) (at: int) : W64.t Array26.t =
 Array26.init
  (WArray208.get64
   (WArray208.init64
     (fun i => (Array26.init (fun i => if 0 <= i < 25 then stk.[i] else st.[i])).[i])).[200
      <- truncateu8 (W64.of_int at)]).

lemma st26_storeE stk st at:
 Array26.init
  (WArray208.get64
   (WArray208.init64
     (fun i => (Array26.init (fun i => if 0 <= i < 0 + 25 then stk.[i - 0] else st.[i])).[i])).[8 * 25
      <- truncateu8 (W64.of_int at)])
 = st26_store stk st at.
proof. by rewrite /st26_store /=. qed.

lemma st26_store_lanes stk st at:
 ust_state (st26_store stk st at) = stk.
proof.
apply Array25.tP => i Hi; rewrite Array25.initiE //= /st26_store Array26.initiE 1:/# /=.
apply W8u8.wordP => j Hj; rewrite st26_set8_bits8 1,2:/# ifF 1:/#.
by rewrite Array26.initiE 1:/# /= ifT 1:/#.
qed.

lemma st26_store_status stk st at:
 0 <= at < 256 =>
 ststatus_at (st26_store stk st at).[25] = at
 /\ ststatus_r8 (st26_store stk st at).[25] = ststatus_r8 st.[25]
 /\ ststatus_trailb (st26_store stk st at).[25] = ststatus_trailb st.[25].
proof.
move=> Hat.
have [] := ststatus_byte0 (st26_store stk st at).[25] st.[25] (truncateu8 (W64.of_int at)) _.
+ move=> j Hj; rewrite /st26_store Array26.initiE // st26_set8_bits8 //.
  by case: (j = 0) => C; [rewrite ifT 1:/# | rewrite ifF 1:/# Array26.initiE].
move=> -> ->; split => //.
by rewrite /truncateu8 W8.of_uintK W64.of_uintK; smt(modz_small pow2_64).
qed.


(* ========================================================================= *)
(* B. The decoder _ststatus_data of the single-lane updstate code           *)
(* ========================================================================= *)

op ststatus_data_spec (s : W64.t) : W8.t * int * int =
 let raw_at  = W64.to_uint s %% 256 in
 let raw_r8  = (((W64.to_uint s %/ 256) %% 256) + 1) * 8 in
 let r8      = if 200 < raw_r8 then 200 else raw_r8 in
 let at      = if r8 <= raw_at then 0 else raw_at in
 let trailb  = W8.of_int ((W64.to_uint s %/ 65536) %% 256) in
 (trailb, r8, at).

lemma ststatus_data_specE s:
 ststatus_data_spec s = (ststatus_trailb s, ststatus_r8 s, ststatus_at_norm s).
proof.
rewrite /ststatus_data_spec /ststatus_trailb /ststatus_r8 /ststatus_at_norm /ststatus_r8 /ststatus_at /= (W64.to_uint_and_mod 8) // (W64.to_uint_and_mod 8) // !W64.shr_div_le // /truncateu8 W64.shr_div_le //=.
rewrite (mulzC _ 8) /=.
by rewrite -(W8.of_int_mod (to_uint s %/ 65536)).
qed.

lemma ststatus_data_ll: islossless M._ststatus_data by islossless.

hoare ststatus_data_h _s:
 M._ststatus_data : ststatus = _s ==> res = ststatus_data_spec _s.
proof.
proc; auto => />; rewrite /ststatus_data_spec /=; do split.
+ by rewrite /truncateu8 !to_uint_shr ..2:/# of_uintK pmod_small 1:/# of_int_mod /#.
+ rewrite /(\ult) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/# (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small.
  + by rewrite to_uint1 of_uintK to_uint_shr /#.
  rewrite of_uintK to_uint_shr 1:/# to_uint1 !(pmod_small _ W64.modulus) ..3:/# -of_intD shlMP 1:/# /=.
  by case: (200 < (to_uint _s %/ 256 %% 256 + 1) * 8) => C; rewrite of_uintK ?(pmod_small _ W64.modulus) /#.
rewrite /(\ult) /(\ule) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/# (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small.
+ by rewrite to_uint1 of_uintK to_uint_shr /#.
rewrite of_uintK to_uint_shr 1:/# to_uint1 (W64.and_mod 8) 1:/# of_uintK !(pmod_small _ W64.modulus) ..4:/# -of_intD shlMP 1:/# /=.
case: (200 < (to_uint _s %/ 256 %% 256 + 1) * 8) => C; rewrite of_uintK (pmod_small _ W64.modulus) 1:/#.
+ by case: (200 <= to_uint _s %% 256) => *; rewrite of_uintK /#.
by case: ((to_uint _s %/ 256 %% 256 + 1) * 8 <= to_uint _s %% 256) => *; rewrite of_uintK /#.
qed.

hoare ststatus_data_bnd_h:
 M._ststatus_data : true ==> 8 <= res.`2 <= 200 /\ 0 <= res.`3 < res.`2.
proof.
proc*; ecall (ststatus_data_h ststatus); skip => /> &hr.
rewrite ststatus_data_specE /=.
by have := ststatus_r8_bounds ststatus{hr}; have := ststatus_at_norm_bounds ststatus{hr}.
qed.

phoare ststatus_data_bnd_ph:
 [ M._ststatus_data : true ==> 8 <= res.`2 <= 200 /\ 0 <= res.`3 < res.`2 ] = 1%r.
proof. by conseq ststatus_data_ll ststatus_data_bnd_h. qed.

phoare ststatus_data_ph _s:
 [ M._ststatus_data : ststatus = _s ==> res = ststatus_data_spec _s ] = 1%r.
proof. by conseq ststatus_data_ll (ststatus_data_h _s). qed.


(* ========================================================================= *)
(* C. Streaming predicates                                                   *)
(* ========================================================================= *)

(* after init and any number of absorbs of l (in total) *)
op absorbing_spec (r8: int) (tb: W8.t) (l: W8.t list) (st: W64.t Array26.t) =
 pabsorb_spec r8 l (ust_state st) /\ status_spec st.[25] r8 tb (size l %% r8).

(* after finish and squeezes of k bytes (in total) from the absorbed state st0 *)
op squeezing_spec (r8: int) (st0: state) (k: int) (st: W64.t Array26.t) =
 0 < r8 <= 200 /\ 0 <= k
 /\ ust_state st = st_i st0 ((k - 1) %/ r8 + 1)
 /\ ststatus_r8 st.[25] = r8 /\ ststatus_at_norm st.[25] = k %% r8.

(* bytes k .. k+n-1 of the squeeze stream *)
op sqstream (r8: int) (st0: state) (k n: int) : W8.t list =
 drop k (SQUEEZE1600 r8 (k + n) st0).

lemma absorbing_spec_r8 r8 tb l st:
 absorbing_spec r8 tb l st =>
 8 %| r8 /\ 8 <= r8 <= 200 /\ ststatus_at_norm st.[25] = size l %% r8 /\ 0 <= size l %% r8 < r8.
proof.
rewrite /absorbing_spec /status_spec => [#] _ <- _ <-.
by have := ststatus_r8_bounds st.[25]; have := ststatus_at_norm_bounds st.[25].
qed.


(* ========================================================================= *)
(* D. Init and finish                                                        *)
(* ========================================================================= *)

lemma pabsorb_spec_nil r8:
 0 < r8 <= 200 => pabsorb_spec r8 [] st0.
proof.
move=> Hr; rewrite /pabsorb_spec => />.
rewrite chunk0 /= 1:/# /stateabsorb_iblocks /= /chunkremains /=.
by rewrite addstate_st0 bytes2state0.
qed.

op init_updstate_spec (r64 : int) (tb : W8.t) : W64.t Array26.t =
 Array26.init (fun i =>
   if i < 25 then W64.zero
   else encode_ststatus 0 (r64 - 1) (W8.to_uint tb)).

lemma init_spec_absorbing r64 tb:
 0 < r64 <= 25 =>
 absorbing_spec (8 * r64) tb [] (init_updstate_spec r64 tb).
proof.
move=> Hr; rewrite /absorbing_spec /=.
have -> : ust_state (init_updstate_spec r64 tb) = st0.
 apply Array25.tP => i Hi; rewrite Array25.initiE //= /init_updstate_spec Array26.initiE 1:/# /=.
 by rewrite ifT 1:/# /st0 Array25.initiE.
split; first by apply pabsorb_spec_nil => /#.
rewrite /init_updstate_spec Array26.initiE //=.
by apply encode_ststatusE.
qed.

lemma stbytes_get (s: state) j:
 0 <= j < 200 => (stbytes s).[j] = s.[j %/ 8] \bits8 (j %% 8).
proof. by move=> Hj; rewrite /WArray200.init64 WArray200.initiE. qed.

lemma zext_bits8 (b: W8.t) j:
 0 <= j < 8 => W64.of_int (W8.to_uint b) \bits8 j = if j = 0 then b else W8.zero.
proof.
move=> Hj; have Hb := W8.to_uint_cmp b; rewrite W8u8.bits8_div 1:/# of_uintK (pmod_small (to_uint b)); first smt(pow2_8 pow2_64).
case: (j = 0) => C; first by rewrite C /=.
have P : 256 <= 2 ^ (8 * j) by rewrite (: 8 * j = 8 + 8 * (j - 1)) 1:/# exprD_nneg 1,2:/#; smt(expr_gt0).
by rewrite divz_small //; smt(pow2_8).
qed.

(* XOR of byte b at byte position pos of the 25-word state *)
op xor_byte_at_st25 (stk : W64.t Array25.t) (pos : int) (b : W8.t) : W64.t Array25.t =
 let w = pos %/ 8 in
 let m = W64.of_int (W8.to_uint b) `<<` W8.of_int (8 * (pos %% 8)) in
 stk.[w <- stk.[w] `^` m].

lemma xor_byte_at_st25E stk pos b:
 0 <= pos < 200 =>
 xor_byte_at_st25 stk pos b = stwords ((stbytes stk).[pos <- (stbytes stk).[pos] `^` b]).
proof.
move=> Hp; apply stbytes_inj; rewrite stwordsK; apply WArray200.tP => i Hi; rewrite /xor_byte_at_st25 /= stbytes_get // WArray200.get_setE // Array25.get_setE 1:/#.
rewrite !stbytes_get //; case: (i %/ 8 = pos %/ 8) => C; last by rewrite ifF 1:/#.
rewrite W8u8.xorb8E shl_shlw 1:/# bits8_u64_shl8 1:/# -C.
case: (i = pos) => E; first by rewrite -E /= zext_bits8.
by case: (i %% 8 < pos %% 8) => C2; [ | rewrite zext_bits8 1:/# ifF 1:/#]; rewrite W8.xorw0.
qed.

(* `st.[:u32 200] &= 0xFF00FF00`: clears the cursor and the trail byte *)
op clear_at_trailb (s : W64.t) : W64.t =
 s `&` W64.of_int 18446744073692839680. (* 0xFFFFFFFFFF00FF00 *)

lemma clear_at_trailb_r8w s:
 (clear_at_trailb s `>>` W8.of_int 8) `&` W64.of_int 255 = (s `>>` W8.of_int 8) `&` W64.of_int 255.
proof.
apply W64.wordP => k Hk; rewrite /clear_at_trailb !shr_shrw // !W64.andwE !W64.shrwE (: 255 = 2^8 - 1) 1:// W64.of_int_powm1 //=.
case: (k < 8) => C //=; have : k \in iota_ 0 8 by rewrite mem_iota /#.
move: k Hk C; rewrite -iotaredE /= => k _ _; rewrite W64.of_intwE /int_bit.
by do 7! (case => [-> //= |]); move=> -> //=.
qed.

lemma clear_at_trailb_r8 s:
 ststatus_r8 (clear_at_trailb s) = ststatus_r8 s.
proof. by rewrite /ststatus_r8 /= clear_at_trailb_r8w. qed.

lemma clear_at_trailb_at s:
 ststatus_at_norm (clear_at_trailb s) = 0.
proof.
rewrite /ststatus_at_norm /ststatus_at /=.
have -> : clear_at_trailb s `&` W64.of_int 255 = W64.zero.
+ apply W64.wordP => k Hk; rewrite /clear_at_trailb !W64.andwE (: 255 = 2^8 - 1) 1:// W64.of_int_powm1 //=.
  case: (k < 8) => C //=; have : k \in iota_ 0 8 by rewrite mem_iota /#.
  move: k Hk C; rewrite -iotaredE /= => k _ _; rewrite W64.of_intwE /int_bit.
  by do 7! (case => [-> //= |]); move=> -> //=.
by rewrite W64.to_uint0.
qed.

(* finish: XOR the trail byte at `at`, 0x80 at r8-1, clear cursor and trail byte *)
op finish_updstate_spec (st : W64.t Array26.t) : W64.t Array26.t =
 let (trailb, r8, at) = ststatus_data_spec st.[25] in
 let stk0 = Array25.init (fun i => st.[i]) in
 let stk1 = xor_byte_at_st25 stk0 at trailb in
 let stk2 = xor_byte_at_st25 stk1 (r8 - 1) (W8.of_int 128) in
 Array26.init (fun i => if i < 25 then stk2.[i] else clear_at_trailb st.[25]).

lemma finish_spec_absorbing r8 tb l st:
 absorbing_spec r8 tb l st =>
 squeezing_spec r8 (ABSORB1600 tb r8 l) 0 (finish_updstate_spec st).
proof.
move=> Habs; have [_ [Hr8 [Hat Hat2]]] := absorbing_spec_r8 _ _ _ _ Habs.
move: Habs; rewrite /absorbing_spec /status_spec => [#] [_ Est] Er8 Etb _.
rewrite /squeezing_spec /= (: (-1) %/ r8 + 1 = 0) 1:/# /st_i iter0 //.
rewrite /finish_updstate_spec ststatus_data_specE /= clear_at_trailb_r8 clear_at_trailb_at Er8 Etb Hat /=.
split; first smt().
pose I := stateabsorb_iblocks (BitEncoding.BitChunking.chunk r8 l) st0; pose CR := chunkremains r8 l.
pose at := size l %% r8.
have Hsz : size CR = at by rewrite /CR size_chunkremains.
have E : xor_byte_at_st25 (xor_byte_at_st25 (ust_state st) at tb) (r8 - 1) (W8.of_int 128) = ABSORB1600 tb r8 l; last first.
+ by apply Array25.tP => i Hi; rewrite Array25.initiE // Array26.initiE 1:/# /= ifT 1:/# E.
rewrite xor_byte_at_st25E 1:/# xor_byte_at_st25E 1:/# stwordsK /ABSORB1600 /stateabsorb_last /addratebit /addratebit8 /stateabsorb.
have K : (stbytes (ust_state st)).[at <- (stbytes (ust_state st)).[at] `^` tb] = stbytes (addstate I (bytes2state (rcons CR tb))); last by rewrite K.
rewrite Est; apply WArray200.tP => i Hi; rewrite WArray200.get_setE 1:/# !stbytes_addstate /addstbytes !WArray200.map2iE //.
+ smt().
rewrite -(bytes2stbytesP (chunkremains r8 l)) -(bytes2stbytesP (rcons CR tb)) !stwordsK.
rewrite !WArray200.get_of_list 1..3:/# nth_rcons -/CR -/I Hsz; case: (i = at) => C.
+ by rewrite C /= (nth_out _ CR) 1:/# W8.xorw0.
by case: (i < at) => C2 //; rewrite (nth_out _ CR) 1:/#.
qed.


(* ========================================================================= *)
(* E. Absorb drivers (the `while (r8 <= len)` body and the epilogue)         *)
(* ========================================================================= *)

lemma addstate_at_nil st at:
 0 <= at => addstate_at st at [] = st.
proof.
move=> Hat; rewrite addstate_atE // cats0 -(cat0s (u8zeros at)) bytes2state_zext bytes2state0.
by rewrite addstateC addstate_st0.
qed.

(* complete the current block (cursor a) with the next r8-a input bytes and permute *)
lemma pabsorb_fill_at r8 (l M: W8.t list) k st a:
 0 <= k => a = (size l + k) %% r8 => k + (r8 - a) <= size M =>
 pabsorb_spec r8 (l ++ take k M) st =>
 pabsorb_spec r8 (l ++ take (k + (r8 - a)) M)
   (keccak_f1600_op (addstate_at st a (take (r8 - a) (drop k M)))).
proof.
move=> Hk -> Hfit H; have [Hr _] := H.
have := pabsorb_fill r8 l M k st Hk Hfit H.
by rewrite addstate_atE 1:/# -nseq1 bytes2state_zext.
qed.

(* the last, partial, block: absorbed without permuting *)
lemma pabsorb_last_at r8 (l M: W8.t list) k st a:
 0 <= k <= size M => a = (size l + k) %% r8 => a + (size M - k) < r8 =>
 pabsorb_spec r8 (l ++ take k M) st =>
 pabsorb_spec r8 (l ++ M) (addstate_at st a (drop k M)).
proof.
move=> Hk -> Hfit H; have [Hr _] := H.
have [_ /(_ (eq_refl 0))] := pabsorb_last r8 l M k st 0 Hk Hfit H.
by rewrite addstate_atE 1:/# -nseq1 bytes2state_zext.
qed.

lemma absorb_block_arith s k r8 a:
 0 < r8 => a = (s + k) %% r8 => (s + (k + (r8 - a))) %% r8 = 0.
proof.
move=> Hr ->.
have E: s + (k + (r8 - (s + k) %% r8)) = ((s + k) %/ r8 + 1) * r8.
 by have := divz_eq (s + k) r8; smt().
by rewrite E modzMl.
qed.

lemma absorb_last_arith s k r8 a n:
 0 < r8 => a = (s + k) %% r8 => 0 <= n => a + n < r8 => (s + (k + n)) %% r8 = a + n.
proof.
move=> Hr -> Hn Hlt; rewrite addzA -modzDml modz_small //; smt(modz_ge0).
qed.


(* ========================================================================= *)
(* F. Squeeze drivers                                                        *)
(* ========================================================================= *)

lemma sqstream0 r8 st0 n: sqstream r8 st0 0 n = SQUEEZE1600 r8 n st0.
proof. by rewrite /sqstream drop0. qed.

lemma size_sqstream r8 st0 k n:
 0 < r8 <= 200 => 0 <= k => 0 <= n => size (sqstream r8 st0 k n) = n.
proof. by move=> Hr Hk Hn; rewrite /sqstream size_drop // size_SQUEEZE1600 /#. qed.

lemma sqstream_cat r8 st0 k n1 n2:
 0 < r8 <= 200 => 0 <= k => 0 <= n1 => 0 <= n2 =>
 sqstream r8 st0 k (n1 + n2) = sqstream r8 st0 k n1 ++ sqstream r8 st0 (k + n1) n2.
proof.
move=> Hr Hk H1 H2; rewrite /sqstream.
pose S := SQUEEZE1600 r8 (k + (n1 + n2)) st0.
have Hs: size S = k + (n1 + n2) by rewrite size_SQUEEZE1600 /#.
rewrite (SQUEEZE1600_ext r8 st0 (k + n1) (k + (n1 + n2))) 1,2:/#.
rewrite (: k + n1 + n2 = k + (n1 + n2)) 1:/# -/S.
case: (n1 = 0) => [E0|Hn1].
+ by rewrite E0 /= (drop_oversize _ (take k S)) 2:// size_take; smt().
by rewrite -{1}(cat_take_drop (k + n1) S) drop_cat size_take 1:/# ifT 1:/#.
qed.

lemma sqstream_block r8 st0 k n:
 0 < r8 <= 200 => 0 <= k => 0 <= n => k %% r8 + n <= r8 =>
 sqstream r8 st0 k n = sub (stbytes (st_i st0 (k %/ r8 + 1))) (k %% r8) n.
proof.
move=> Hr Hk Hn Hfit; apply (eq_from_nth W8.zero).
 by rewrite size_sqstream // size_sub.
move=> i; rewrite size_sqstream // => Hi.
rewrite /sqstream nth_drop 1,2:/# nth_SQUEEZE1600 1,2:/# nth_sub //.
have Hq: (k + i) %/ r8 = k %/ r8.
 by rewrite {1}(divz_eq k r8) -addzA divzMDl 1:/# (divz_small (k %% r8 + i) r8) //; smt(modz_ge0).
have Hm: (k + i) %% r8 = k %% r8 + i.
 by rewrite -modzDml modz_small; smt(modz_ge0).
by rewrite Hq Hm.
qed.

lemma squeeze_entry0 r8 k:
 0 < r8 => k %% r8 = 0 => (k - 1) %/ r8 + 1 + 1 = k %/ r8 + 1.
proof.
move=> Hr Hm; have Hq : k = k %/ r8 * r8 by have := divz_eq k r8; smt().
rewrite {1}Hq (: k %/ r8 * r8 - 1 = (k %/ r8 - 1) * r8 + (r8 - 1)) 1:/#.
by rewrite divzMDl 1:/# (divz_small (r8 - 1) r8) 1:/#.
qed.

lemma squeeze_entry1 r8 k:
 0 < r8 => k %% r8 <> 0 => (k - 1) %/ r8 + 1 = k %/ r8 + 1.
proof.
move=> Hr Hm; rewrite {1}(divz_eq k r8) (: k %/ r8 * r8 + k %% r8 - 1 = k %/ r8 * r8 + (k %% r8 - 1)) 1:/#.
by rewrite divzMDl 1:/# (divz_small (k %% r8 - 1) r8) //; smt(modz_ge0 ltz_pmod).
qed.

lemma squeeze_entry_ge0 r8 k:
 0 < r8 => 0 <= k => 0 <= (k - 1) %/ r8 + 1.
proof.
move=> Hr Hk; case: (k = 0) => [->|Hk0] /=.
+ by rewrite (: -1 = (-1) * r8 + (r8 - 1)) 1:/# divzMDl 1:/# (divz_small (r8 - 1) r8) 1:/#.
by have := divz_ge0 (k - 1) r8 Hr; smt().
qed.

lemma squeeze_pos_arith r8 p a:
 0 < r8 => a = p %% r8 =>
 (p + (r8 - a)) %% r8 = 0 /\ (p + (r8 - a)) %/ r8 = p %/ r8 + 1.
proof.
move=> Hr ->; rewrite {1 3}(divz_eq p r8) (: p %/ r8 * r8 + p %% r8 + (r8 - p %% r8) = (p %/ r8 + 1) * r8) 1:/#.
by rewrite modzMl mulzK 1:/#.
qed.

lemma squeeze_fin_arith r8 p a n:
 0 < r8 => a = p %% r8 => 0 < n => a + n <= r8 =>
 (p + n - 1) %/ r8 + 1 = p %/ r8 + 1
 /\ (p + n) %% r8 = (if r8 <= a + n then 0 else a + n).
proof.
move=> Hr -> Hn Hfit; split.
+ rewrite {1}(divz_eq p r8) (: p %/ r8 * r8 + p %% r8 + n - 1 = p %/ r8 * r8 + (p %% r8 + n - 1)) 1:/#.
  by rewrite divzMDl 1:/# (divz_small (p %% r8 + n - 1) r8) //; smt(modz_ge0).
rewrite -modzDml; case: (r8 <= p %% r8 + n) => C.
+ by rewrite (: p %% r8 + n = r8) 1:/# modzz.
by rewrite (modz_small (p %% r8 + n) r8) //; smt(modz_ge0).
qed.


(* ========================================================================= *)
(* G. Word and index helpers of the add/dump procedures                      *)
(* ========================================================================= *)

lemma shr3_shl3 (x: int): (x `|>>` 3) `<<` 3 = 8 * (x %/ 8).
proof. by rewrite /(`|>>`) /(`<<`) /= /#. qed.

lemma trunc_shl3_and63 k:
 0 <= k < 8 =>
 (truncateu8 (W64.of_int k) `<<` W8.of_int 3) `&` W8.of_int 63 = W8.of_int (8 * k).
proof.
move=> Hk0; rewrite /truncateu8 W64.of_uintK /W8.(`<<`) W8.of_uintK /= -(W8.to_uintK (W8.of_int (k %% W64.modulus))).
by rewrite W8.shlMP // (W8.and_mod 6) // !W8.of_uintK; smt(modz_small pow2_64).
qed.

lemma and7_mod8 (x: int):
 0 <= x < W64.modulus => W64.to_uint (W64.of_int x `&` W64.of_int 7) = x %% 8.
proof. by move=> Hx; rewrite (W64.to_uint_and_mod 3) // W64.of_uintK; smt(modz_small pow2_64). qed.

lemma drop_sub200 (t: WArray200.t) o n k:
 0 <= k <= n => drop k (sub t o n) = sub t (o + k) (n - k).
proof.
move=> Hk; apply (eq_from_nth W8.zero).
 by rewrite size_drop 1:/# !size_sub /#.
move=> i; rewrite size_drop 1:/# size_sub 1:/# => Hi.
by rewrite nth_drop 1,2:/# !nth_sub /#.
qed.

lemma u64bytes_get64_shr (t: WArray200.t) o k:
 0 <= k <= 8 =>
 u64bytes (get64_direct t o `>>` W8.of_int (8 * k)) = sub t (o + k) (8 - k) ++ u8zeros k.
proof. by move=> Hk; rewrite u64bytes_shr8 // u64bytes_get64 drop_sub200. qed.

lemma sub200_nil (t: WArray200.t) o: sub t o 0 = [].
proof. by rewrite -size_eq0 size_sub. qed.
