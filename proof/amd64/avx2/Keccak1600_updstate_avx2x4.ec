(******************************************************************************
   Keccak1600_updstate_avx2x4.ec:

   Correctness of the 4-way AVX2 "updstate" (streaming) Keccak1600 procedures
   (src/fips202/avx2/keccak1600x4_updstate{,_ASIZE}.jinc).  The 4-way state
   is W64.t Array101.t: words 0..99 hold the packed 4-way Keccak state
   (state4x, read through A101u64toA25u256) and word 100 the status word,
   with the encoding of the single-lane code (common/Keccak1600_updstate.ec).
   The contracts lift those of ref/Keccak1600_updstate_ref.ec lane by lane:
     init      ==> absorbing_spec4 r8 tb [] [] [] [] res
     absorb    absorbing_spec4 r8 tb l0..l3 st ==> absorbing_spec4 r8 tb (l0 ++ in0) .. (l3 ++ in3) res
     finish    absorbing_spec4 r8 tb l0..l3 st
               ==> squeezing_spec4 r8 (st4x_pack (ABSORB1600 tb r8 l0, ..)) 0 res
     squeeze   squeezing_spec4 r8 s0 k st ==> out_i = sqstream r8 (st4x_get s0 i) k len
                                            /\ squeezing_spec4 r8 s0 (k+len) res
   Memory buffers are proved at top level against Keccak1600_Jazz.M, array
   buffers in the abstract theory KeccakUpdstateAvx2x4; the two share the
   lane lemmas of Keccak1600_fixedsizes_avx2x4.ec (addstate_spec4 /
   addstate_spec4m, pabsorb4, stores4) and the helpers below.
   The lane steps reuse the 4-way layer of Keccak1600_fixedsizes_avx2x4.ec
   (addstate_spec4, addstate_lanes, pabsorb4_fill/_last, st4x_get_xor64x4).
   The init/finish/status proofs are those of the ci-mldsa-sct branch.
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray800 WArray808.
from JazzEC require import Array3 Array25 Array26 Array101.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Keccak1600_statebytes Keccak1600_subreadwrite Keccak1600_updstate.
require import Keccak1600_fixedsizes_avx2x4.

import IntOrder.


(* ========================================================================= *)
(* The 4-way updstate state                                                  *)
(* ========================================================================= *)

op A101u64toA25u256 (st: W64.t Array101.t): state4x =
 Array25.init (fun i => WArray808.get256 (WArray808.init64 (fun j => st.[j])) i).

op A25u256toA101u64 (stk: state4x) (s: W64.t): W64.t Array101.t =
 Array101.init (fun i => if i < 100 then stk.[i %/ 4] \bits64 (i %% 4) else s).

(* after init and absorbs of l0..l3 (in total) *)
op absorbing_spec4 (r8: int) (tb: W8.t) (l0 l1 l2 l3: W8.t list) (st: W64.t Array101.t) =
 pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st)
 /\ status_spec st.[100] r8 tb (size l0 %% r8).

(* after finish and squeezes of k bytes (in total, per lane) from s0 *)
op squeezing_spec4 (r8: int) (s0: state4x) (k: int) (st: W64.t Array101.t) =
 0 < r8 <= 200 /\ 0 <= k
 /\ A101u64toA25u256 st = iter ((k - 1) %/ r8 + 1) keccak_f1600_x4 s0
 /\ ststatus_r8 st.[100] = r8 /\ ststatus_at_norm st.[100] = k %% r8.

op init_updstate_avx2x4_spec (r64 : int) (trailb : W8.t) : W64.t Array101.t =
 A25u256toA101u64 st4x0 (encode_ststatus 0 (r64 - 1) (W8.to_uint trailb)).

op finish_updstate_avx2x4_spec (st : W64.t Array101.t) : W64.t Array101.t =
 let (trailb, r8, at) = ststatus_data_spec st.[100] in
 A25u256toA101u64
  (st4x_map (fun s => xor_byte_at_st25 (xor_byte_at_st25 s at trailb) (r8 - 1) (W8.of_int 128))
            (A101u64toA25u256 st))
  (clear_at_trailb st.[100]).

lemma st4x_get_bcast (st: state4x) j w k:
 0 <= j < 25 => 0 <= k < 4 =>
 st4x_get (st.[j <- VPBROADCAST_4u64 w `^` st.[j]]) k = (st4x_get st k).[j <- (st4x_get st k).[j] `^` w].
proof.
move=> Hj Hk; apply Array25.ext_eq => i Hi; rewrite !st4x_getiE // !get_setE //; case: (i = j) => C //.
+ by rewrite W4u64.xorb64E VPBROADCAST_4u64_bits64 // xorwC.
by rewrite st4x_getiE.
qed.

lemma st4x_get64_direct (st: state4x) m k:
 0 <= m < 25 => 0 <= k < 4 =>
 WArray800.get64_direct (WArray800.init256 (fun i => st.[i])) (32*m + 8*k) = st.[m] \bits64 k.
proof.
move=> Hm Hk; apply W64.wordP => b Hb; rewrite /WArray800.get64_direct pack8E initiE 1:/# /= initiE 1:/# /=.
by rewrite /WArray800.init256 WArray800.initiE 1:/# /= bits8iE 1:/# bits64iE 1:/#; congr; smt().
qed.

lemma stbytes_st4x (st: state4x) l j:
 0 <= l < 4 => 0 <= j < 200 =>
 (stbytes (st4x_get st l)).[j] = st.[j %/ 8] \bits64 l \bits8 (j %% 8).
proof. by move=> Hl Hj; rewrite /WArray200.init64 WArray200.initiE //= st4x_getiE // /#. qed.

lemma A101u64toA25u256K (stk: state4x) s:
  A101u64toA25u256 (A25u256toA101u64 stk s) = stk.
proof.
apply Array25.tP => i Hi; rewrite /A101u64toA25u256 Array25.initiE //= WArray808.get256E; apply W256.wordP => b Hb.
rewrite W32u8.pack32wE 1:// W32u8.Pack.initiE 1:/# /= /WArray808.init64 WArray808.initiE 1:/# /= /A25u256toA101u64 Array101.initiE 1:/# /= ifT 1:/#.
by rewrite W8u8.bits8iE 1:/# W4u64.bits64iE 1:/# (: (32 * i + b %/ 8) %/ 8 %/ 4 = i) 1:/#; congr; smt().
qed.

lemma A25u256toA101u64E (stk: state4x) (st: W64.t Array101.t):
  Array101.init (fun i => WArray808.get64 (WArray808.init8 (fun j => if 0 <= j < 800 then WArray800.get8 (WArray800.init256 (fun k => stk.[k])) j else WArray808.get8 (WArray808.init64 (fun k => st.[k])) j)) i)
  = A25u256toA101u64 stk st.[100].
proof.
apply Array101.tP => i Hi; rewrite /A25u256toA101u64 !Array101.initiE //= WArray808.get64E; apply W64.wordP => b Hb.
rewrite W8u8.pack8wE 1:// W8u8.Pack.initiE 1:/# /= WArray808.initiE 1:/# /=.
case: (i < 100) => C; [rewrite ifT 1:/# | rewrite ifF 1:/#].
+ rewrite /WArray800.get8 /WArray800.init256 WArray800.initiE 1:/# /=.
  by rewrite W32u8.bits8iE 1:/# W4u64.bits64iE 1:/# (: (8 * i + b %/ 8) %/ 32 = i %/ 4) 1:/#; congr; smt().
by rewrite /WArray808.get8 /WArray808.init64 WArray808.initiE 1:/# /= W8u8.bits8iE 1:/# (: (8 * i + b %/ 8) %/ 8 = 100) 1:/#; congr; smt().
qed.

lemma A101_xor256 (st: W64.t Array101.t) j (v: W256.t):
  0 <= j < 25 =>
  Array101.init (WArray808.get64 (WArray808.set256_direct (WArray808.init64 (fun i => st.[i])) (32*j) (v `^` WArray808.get256_direct (WArray808.init64 (fun i => st.[i])) (32*j))))
  = A25u256toA101u64 ((A101u64toA25u256 st).[j <- v `^` (A101u64toA25u256 st).[j]]) st.[100].
proof.
move=> Hj; have G : forall (t: WArray808.t) k, t.[k] = WArray808.get8 t k by done.
apply Array101.tP => i Hi; rewrite /A25u256toA101u64 !Array101.initiE //= WArray808.get64E; apply W64.wordP => b Hb.
rewrite W8u8.pack8wE 1:// W8u8.Pack.initiE 1:/# /= G WArray808.get8_set256E 1,2:/#.
have B8 : forall k r, 0 <= k < 808 => 0 <= r < 8 => (WArray808.get8 (WArray808.init64 (fun i => st.[i])) k).[r] = st.[k %/ 8].[k %% 8 * 8 + r].
+ by move=> k r Hk Hr; rewrite /WArray808.get8 /WArray808.init64 WArray808.initiE //= W8u8.bits8iE.
have B256 : forall m c, 0 <= m < 25 => 0 <= c < 256 => (WArray808.get256 (WArray808.init64 (fun i => st.[i])) m).[c] = st.[4 * m + c %/ 64].[c %% 64].
+ by move=> m c Hm Hc; rewrite WArray808.get256E W32u8.pack32wE // W32u8.Pack.initiE 1:/# /= G B8 1,2:/#; congr; smt().
case: (32 * j <= 8 * i + b %/ 8 < 32 * (j + 1)) => C.
+ by rewrite ifT 1:/# Array25.get_setE 1:/# ifT 1:/# W32u8.bits8iE 1:/# W4u64.bits64iE 1:/# /A101u64toA25u256 Array25.initiE 1:/# /=; congr; smt().
rewrite B8 1,2:/# (: (8 * i + b %/ 8) %/ 8 = i) 1:/# (: (8 * i + b %/ 8) %% 8 = b %/ 8) 1:/# -divz_eq; case: (i < 100) => Ci /=; last by rewrite (: i = 100) /#.
by rewrite Array25.get_setE 1:/# ifF 1:/# W4u64.bits64iE 1:/# /A101u64toA25u256 Array25.initiE 1:/# /= B256 1,2:/#; congr; smt().
qed.

lemma A101_clear (X: state4x) s:
  Array101.init (WArray808.get64 (WArray808.set32_direct (WArray808.init64 (fun i => (A25u256toA101u64 X s).[i])) 800 (WArray808.get32_direct (WArray808.init64 (fun i => (A25u256toA101u64 X s).[i])) 800 `&` W32.of_int 4278255360)))
  = A25u256toA101u64 X (clear_at_trailb s).
proof.
apply Array101.tP => i Hi; rewrite Array101.initiE //= WArray808.get64E; apply W64.wordP => b Hb.
rewrite W8u8.pack8wE 1:// W8u8.Pack.initiE 1:/# /= /WArray808.set32_direct WArray808.initiE 1:/# /=.
case: (800 <= 8 * i + b %/ 8 < 804) => C /=; [rewrite /WArray808.get32_direct W4u8.pack4bE 1:/# W4u8.Pack.initiE 1:/# /= | ]; rewrite /WArray808.init64 WArray808.initiE 1:/# /=.
+ have -> /= : i = 100 by smt().
  rewrite (: (800 + b %/ 8) %/ 8 = 100) 1:/# (: (800 + b %/ 8) %% 8 = b %/ 8) 1:/# /A25u256toA101u64 !Array101.initiE //= W8u8.bits8iE 1:/# W4u8.bits8iE 1:/# -divz_eq /clear_at_trailb W64.andwE.
  congr; have : b \in iota_ 0 32 by rewrite mem_iota /#.
  move: b Hb C; rewrite -iotaredE /= => b _ _; rewrite W32.of_intwE W64.of_intwE /int_bit; by do 31! (case => [-> //= |]); move=> -> //=.
rewrite (: (8 * i + b %/ 8) %/ 8 = i) 1:/# (: (8 * i + b %/ 8) %% 8 = b %/ 8) 1:/# W8u8.bits8iE 1:/# -divz_eq /A25u256toA101u64 !Array101.initiE //=; case: (i < 100) => Ci //=.
rewrite /clear_at_trailb W64.andwE; have : b \in iota_ 32 32 by rewrite mem_iota /#.
move: b Hb C; rewrite -iotaredE /= => b _ _; rewrite W64.of_intwE /int_bit; by do 31! (case => [-> //= |]); move=> -> //=.
qed.

lemma A101_set800 (stk: state4x) s (b: W8.t):
  Array101.init (WArray808.get64 (WArray808.init64 (fun i => (A25u256toA101u64 stk s).[i])).[800 <- b])
  = A25u256toA101u64 stk (W8u8.pack8_t (W8u8.Pack.init (fun j => if j = 0 then b else s \bits8 j))).
proof.
apply Array101.tP => i Hi; rewrite Array101.initiE //= WArray808.get64E; apply W64.wordP => c Hc.
rewrite W8u8.pack8wE 1:// W8u8.Pack.initiE 1:/# /= WArray808.get_setE 1:/#.
rewrite /A25u256toA101u64 Array101.initiE //=; case: (i < 100) => Ci /=.
+ rewrite ifF 1:/# /WArray808.init64 WArray808.initiE 1:/# /= Array101.initiE 1:/# /= (: (8 * i + c %/ 8) %/ 8 = i) 1:/# ifT 1:/# W8u8.bits8iE 1:/#.
  by congr; smt().
have Ei : i = 100 by smt().
rewrite Ei /= W8u8.pack8wE 1:// W8u8.Pack.initiE 1:/# /=; case: (c %/ 8 = 0) => C; first by rewrite C.
rewrite ifF 1:/# /WArray808.init64 WArray808.initiE 1:/# /= Array101.initiE 1:/# /= (: (800 + c %/ 8) %/ 8 = 100) 1:/# /= W8u8.bits8iE 1:/# W8u8.bits8iE 1:/#.
by congr; smt().
qed.

lemma ststatus_data_avx2x4P (s: W64.t):
  (s `>>` W8.of_int 8 `>>` W8.of_int 8) `&` W64.of_int 255 = zeroextu64 (ststatus_trailb s)
  /\ to_uint (if W64.of_int 200 \ult (s `>>` W8.of_int 8) `&` W64.of_int 255 + W64.one `<<` W8.of_int 3 then W64.of_int 200
              else (s `>>` W8.of_int 8) `&` W64.of_int 255 + W64.one `<<` W8.of_int 3) = ststatus_r8 s
  /\ to_uint (if (if W64.of_int 200 \ult (s `>>` W8.of_int 8) `&` W64.of_int 255 + W64.one `<<` W8.of_int 3 then W64.of_int 200
                  else (s `>>` W8.of_int 8) `&` W64.of_int 255 + W64.one `<<` W8.of_int 3) \ule s `&` W64.of_int 255 then W64.zero
              else s `&` W64.of_int 255) = ststatus_at_norm s.
proof.
have := ststatus_data_specE s; rewrite /ststatus_data_spec /= => [#] Et Er Ea; rewrite -Er -Ea.
split; first by rewrite -Et; apply W64.to_uint_eq; rewrite (W64.to_uint_and_mod 8) // !W64.shr_div_le // W8u8.to_uint_zeroextu64 W8.of_uintK /= -divzMr // modz_mod.
split; first rewrite /(\ult) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/# (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small.
+ by rewrite to_uint1 of_uintK to_uint_shr /#.
+ rewrite of_uintK to_uint_shr 1:/# to_uint1 !(pmod_small _ W64.modulus) ..3:/# -of_intD shlMP 1:/# /=.
  by case: (200 < (to_uint s %/ 256 %% 256 + 1) * 8) => C; rewrite of_uintK ?(pmod_small _ W64.modulus) /#.
rewrite /(\ult) /(\ule) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/# (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small; first by rewrite to_uint1 of_uintK to_uint_shr /#.
rewrite of_uintK to_uint_shr 1:/# to_uint1 (W64.and_mod 8) 1:/# of_uintK !(pmod_small _ W64.modulus) ..4:/# -of_intD shlMP 1:/# /=.
case: (200 < (to_uint s %/ 256 %% 256 + 1) * 8) => C; rewrite of_uintK (pmod_small _ W64.modulus) 1:/#.
+ by case: (200 <= to_uint s %% 256) => *; rewrite of_uintK /#.
by case: ((to_uint s %/ 256 %% 256 + 1) * 8 <= to_uint s %% 256) => *; rewrite of_uintK /#.
qed.

lemma truncateu64_VMOV_64 (x: W64.t): truncateu64 (VMOV_64 x) = x.
proof. by have := W2u64.bits64_div (VMOV_64 x) 0 _ => //=; rewrite /truncateu64 => <-; rewrite /VMOV_64 W2u64.pack2bE. qed.

lemma init_spec_absorbing4 r64 tb:
 0 < r64 <= 25 =>
 absorbing_spec4 (8 * r64) tb [] [] [] [] (init_updstate_avx2x4_spec r64 tb).
proof.
move=> Hr; rewrite /absorbing_spec4 /init_updstate_avx2x4_spec A101u64toA25u256K.
split; first by apply pabsorb_spec_avx2x4_nil => /#.
by rewrite /A25u256toA101u64 Array101.initiE //= (: size<:W8.t> [] %% (8 * r64) = 0) 1:/#; apply encode_ststatusE.
qed.

(* finish, lane by lane, from the single-lane finish_spec_absorbing *)
lemma finish_lane (s: state) (w: W64.t) (l: W8.t list):
  ststatus_at_norm w = size l %% ststatus_r8 w =>
  pabsorb_spec (ststatus_r8 w) l s =>
  xor_byte_at_st25 (xor_byte_at_st25 s (ststatus_at_norm w) (ststatus_trailb w)) (ststatus_r8 w - 1) (W8.of_int 128)
  = ABSORB1600 (ststatus_trailb w) (ststatus_r8 w) l.
proof.
move=> Ha Hp; pose S := Array26.init (fun i => if i < 25 then s.[i] else w).
have E25 : S.[25] = w by rewrite /S Array26.initiE.
have Es : Array25.init (fun i => S.[i]) = s by apply Array25.tP => i Hi; rewrite Array25.initiE //= /S Array26.initiE 1:/# /= ifT 1:/#.
have := finish_spec_absorbing (ststatus_r8 w) (ststatus_trailb w) l S _.
+ by rewrite /absorbing_spec Es E25 /status_spec Ha.
have [Hr8 _] := Hp.
have Em1 : (-1) %/ ststatus_r8 w = -1.
+ by have /= := squeeze_entry0 (ststatus_r8 w) 0 _ _; smt(div0z).
rewrite /squeezing_spec /= Em1 /st_i iter0 // => [#] _ _ <- _ _.
rewrite /finish_updstate_spec ststatus_data_specE /= E25 Es.
by apply Array25.tP => i Hi; rewrite Array25.initiE // Array26.initiE 1:/# /= ifT 1:/#.
qed.

lemma finish_spec_absorbing4 r8 tb l0 l1 l2 l3 st:
 absorbing_spec4 r8 tb l0 l1 l2 l3 st =>
 squeezing_spec4 r8 (st4x_pack (ABSORB1600 tb r8 l0, ABSORB1600 tb r8 l1, ABSORB1600 tb r8 l2, ABSORB1600 tb r8 l3)) 0
   (finish_updstate_avx2x4_spec st).
proof.
rewrite /absorbing_spec4 /status_spec => [#] Hp Er8 Etb Hat.
have [Hr _] := Hp.
have := Hp; rewrite pabsorb_spec_avx2x4E => [#] S1 S2 S3 HL.
have E100 : forall X s, (A25u256toA101u64 X s).[100] = s by move=> X s; rewrite /A25u256toA101u64 Array101.initiE.
have Em1 : (-1) %/ r8 = -1 by have /= := squeeze_entry0 r8 0 _ _; smt(div0z).
rewrite /squeezing_spec4 /= Em1 /= /finish_updstate_avx2x4_spec ststatus_data_specE /= E100 clear_at_trailb_r8 clear_at_trailb_at Er8 Etb.
split; first smt().
rewrite A101u64toA25u256K iter0 //= st4x_mapE /=.
have F0 : xor_byte_at_st25 (xor_byte_at_st25 (st4x_get (A101u64toA25u256 st) 0) (ststatus_at_norm st.[100]) tb) (r8 - 1) (W8.of_int 128) = ABSORB1600 tb r8 l0.
+ have := finish_lane (st4x_get (A101u64toA25u256 st) 0) st.[100] l0 _ _.
  + by rewrite Hat Er8.
  + by rewrite Er8; apply (HL 0).
  by rewrite Er8 Etb.
have F1 : xor_byte_at_st25 (xor_byte_at_st25 (st4x_get (A101u64toA25u256 st) 1) (ststatus_at_norm st.[100]) tb) (r8 - 1) (W8.of_int 128) = ABSORB1600 tb r8 l1.
+ have := finish_lane (st4x_get (A101u64toA25u256 st) 1) st.[100] l1 _ _.
  + by rewrite Hat Er8 S1.
  + by rewrite Er8; apply (HL 1).
  by rewrite Er8 Etb.
have F2 : xor_byte_at_st25 (xor_byte_at_st25 (st4x_get (A101u64toA25u256 st) 2) (ststatus_at_norm st.[100]) tb) (r8 - 1) (W8.of_int 128) = ABSORB1600 tb r8 l2.
+ have := finish_lane (st4x_get (A101u64toA25u256 st) 2) st.[100] l2 _ _.
  + by rewrite Hat Er8 S2.
  + by rewrite Er8; apply (HL 2).
  by rewrite Er8 Etb.
have F3 : xor_byte_at_st25 (xor_byte_at_st25 (st4x_get (A101u64toA25u256 st) 3) (ststatus_at_norm st.[100]) tb) (r8 - 1) (W8.of_int 128) = ABSORB1600 tb r8 l3.
+ have := finish_lane (st4x_get (A101u64toA25u256 st) 3) st.[100] l3 _ _.
  + by rewrite Hat Er8 S3.
  + by rewrite Er8; apply (HL 3).
  by rewrite Er8 Etb.
by rewrite F0 F1 F2 F3.
qed.


(* ========================================================================= *)
(* Init, finish and the status export                                        *)
(* ========================================================================= *)

lemma init_updstate_avx2x4_ll: islossless M._init_updstate_avx2x4.
proof. by proc; wp; call state_init_avx2x4_ll; auto. qed.

hoare init_updstate_avx2x4_spec_h _r64 _tb:
 M._init_updstate_avx2x4
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> res = init_updstate_avx2x4_spec _r64 _tb.
proof.
proc; wp; ecall (state_init_avx2x4_h'); wp; skip => &hr [#] -> -> Hr0 Hr1 /= _ ->.
rewrite A25u256toA101u64E (: (_r64 - 1) %% 256 = _r64 - 1) 1:/# init_status 1:/# /init_updstate_avx2x4_spec.
by apply Array101.tP => i Hi; rewrite Array101.get_setE // /A25u256toA101u64 !Array101.initiE //; smt().
qed.

hoare init_updstate_avx2x4_h _r64 _tb:
 M._init_updstate_avx2x4
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec4 (8 * _r64) _tb [] [] [] [] res.
proof.
conseq (init_updstate_avx2x4_spec_h _r64 _tb).
by move=> &hr [#] _ _ H1 H2 r ->; apply init_spec_absorbing4.
qed.

phoare init_updstate_avx2x4_ph _r64 _tb:
 [ M._init_updstate_avx2x4
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec4 (8 * _r64) _tb [] [] [] [] res
 ] = 1%r.
proof. by conseq init_updstate_avx2x4_ll (init_updstate_avx2x4_h _r64 _tb). qed.

lemma finish_updstate_avx2x4_ll: islossless M._finish_updstate_avx2x4.
proof. islossless. qed.

hoare finish_updstate_avx2x4_spec_h _st:
  M._finish_updstate_avx2x4
  : st = _st
  ==> res = finish_updstate_avx2x4_spec _st.
proof.
proc; seq 2 : (st = _st /\ trailb = zeroextu64 (ststatus_trailb _st.[100]) /\ r8 = ststatus_r8 _st.[100] /\ at = ststatus_at_norm _st.[100]).
+ by inline *; auto => />; exact (ststatus_data_avx2x4P _st.[100]).
wp; skip => &hr [#] -> -> -> -> /=.
have S5 : forall x, (x `|>>` 3) `<<` 5 = 32 * (x %/ 8) by move=> x; rewrite /(`|>>`) /(`<<`) /= /#.
have E100 : forall X s, (A25u256toA101u64 X s).[100] = s by move=> X s; rewrite /A25u256toA101u64 Array101.initiE.
have [HA0 [HA1 [HR0 [HR1 HR8]]]] : 0 <= ststatus_at_norm _st.[100] /\ ststatus_at_norm _st.[100] < ststatus_r8 _st.[100]
                                   /\ 8 <= ststatus_r8 _st.[100] /\ ststatus_r8 _st.[100] <= 200 /\ ststatus_r8 _st.[100] %% 8 = 0.
+ by rewrite /ststatus_at_norm /ststatus_r8 /ststatus_at /=; smt(W64.to_uint_cmp).
rewrite !S5 (A101_xor256 _st (ststatus_at_norm _st.[100] %/ 8)) 1:/#.
rewrite (A101_xor256 _ ((ststatus_r8 _st.[100] - 1) %/ 8)) 1:/# A101u64toA25u256K E100 A101_clear /finish_updstate_avx2x4_spec ststatus_data_specE /=.
have T7 : truncateu8 (W64.of_int (ststatus_at_norm _st.[100])) `&` W8.of_int 7 = truncateu8 (W64.of_int (ststatus_at_norm _st.[100] %% 8)).
+ apply W8.to_uint_eq; rewrite (W8.to_uint_and_mod 3) // !to_uint_truncateu8 !W64.of_uintK.
  by rewrite !(modz_small _ ptr_modulus) 1,2:/# !(modz_small _ W8.modulus) 1,2:/#.
have W2 : W64.one `<<` W8.of_int 63 = W64.of_int (W8.to_uint (W8.of_int 128)) `<<` W8.of_int (8 * ((ststatus_r8 _st.[100] - 1) %% 8)).
+ by rewrite (: (ststatus_r8 _st.[100] - 1) %% 8 = 7) 1:/#; apply W64.to_uint_eq; rewrite !W64.to_uint_shl //=.
rewrite !truncateu64_VMOV_64 T7 trunc_shl3_and63 1:/# W2; congr; rewrite st4x_mapE -{1}st4x_unpackK /st4x_unpack /=; congr.
by rewrite !st4x_get_bcast 1..16:/# /xor_byte_at_st25 /zeroextu64.
qed.

hoare finish_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3:
 M._finish_updstate_avx2x4
 : absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st
 ==> squeezing_spec4 _r8 (st4x_pack (ABSORB1600 _tb _r8 _l0, ABSORB1600 _tb _r8 _l1, ABSORB1600 _tb _r8 _l2, ABSORB1600 _tb _r8 _l3)) 0 res.
proof.
exlim st => _st.
conseq (finish_updstate_avx2x4_spec_h _st); first by move=> />.
by move=> &hr [#] <- Habs r ->; apply finish_spec_absorbing4.
qed.

phoare finish_updstate_avx2x4_ph _r8 _tb _l0 _l1 _l2 _l3:
 [ M._finish_updstate_avx2x4
 : absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st
 ==> squeezing_spec4 _r8 (st4x_pack (ABSORB1600 _tb _r8 _l0, ABSORB1600 _tb _r8 _l1, ABSORB1600 _tb _r8 _l2, ABSORB1600 _tb _r8 _l3)) 0 res
 ] = 1%r.
proof. by conseq finish_updstate_avx2x4_ll (finish_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3). qed.

lemma ststatus_updstate_avx2x4_ll: islossless M.ststatus_updstate_avx2x4.
proof. islossless. qed.

hoare ststatus_updstate_avx2x4_h _st:
  M.ststatus_updstate_avx2x4
  : st = _st
  ==> W8.to_uint res.[0] = ststatus_r8 _st.[100]
   /\ W8.to_uint res.[1] = ststatus_at_norm _st.[100]
   /\ res.[2] = ststatus_trailb _st.[100].
proof.
proc; inline M._ststatus_data_avx2x4; wp; skip => &hr -> /=.
have [_ [Er Ea]] := ststatus_data_avx2x4P _st.[100]; rewrite /truncateu8 !W8.of_uintK Er Ea.
have [Hr0 Hr1] : 0 <= ststatus_r8 _st.[100] <= 200 by rewrite /ststatus_r8 /=; smt(W64.to_uint_cmp).
have [Ha0 Ha1] : 0 <= ststatus_at_norm _st.[100] <= 200 by rewrite /ststatus_at_norm /ststatus_r8 /ststatus_at /=; smt(W64.to_uint_cmp).
split; first smt(pow2_8).
split; first smt(pow2_8).
by rewrite /WArray808.get8 /WArray808.init64 WArray808.initiE //= /ststatus_trailb W8u8.bits8_div // /truncateu8 W64.shr_div_le //=.
qed.

phoare ststatus_updstate_avx2x4_ph _st:
  [ M.ststatus_updstate_avx2x4
  : st = _st
  ==> W8.to_uint res.[0] = ststatus_r8 _st.[100]
   /\ W8.to_uint res.[1] = ststatus_at_norm _st.[100]
   /\ res.[2] = ststatus_trailb _st.[100]
  ] = 1%r.
proof. by conseq ststatus_updstate_avx2x4_ll (ststatus_updstate_avx2x4_h _st). qed.

(* ------------------------------------------------------------------------- *)
(* The exported wrappers                                                     *)
(* ------------------------------------------------------------------------- *)

lemma init_updstate_avx2x4_export_ll: islossless M.init_updstate_avx2x4.
proof. by proc; call init_updstate_avx2x4_ll; auto. qed.

hoare init_updstate_avx2x4_export_h _r64 _tb:
 M.init_updstate_avx2x4
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec4 (8 * _r64) _tb [] [] [] [] res.
proof. by proc; ecall (init_updstate_avx2x4_h _r64 _tb); auto. qed.

lemma finish_updstate_avx2x4_export_ll: islossless M.finish_updstate_avx2x4.
proof. by proc; call finish_updstate_avx2x4_ll; auto. qed.

hoare finish_updstate_avx2x4_export_h _r8 _tb _l0 _l1 _l2 _l3:
 M.finish_updstate_avx2x4
 : absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st
 ==> squeezing_spec4 _r8 (st4x_pack (ABSORB1600 _tb _r8 _l0, ABSORB1600 _tb _r8 _l1, ABSORB1600 _tb _r8 _l2, ABSORB1600 _tb _r8 _l3)) 0 res.
proof. by proc; ecall (finish_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3); auto. qed.


(* ========================================================================= *)
(* Helpers shared by the memory and array procedures                         *)
(* ========================================================================= *)

(* the status decoder *)
lemma ststatus_data_avx2x4_ll: islossless M._ststatus_data_avx2x4.
proof. islossless. qed.

hoare ststatus_data_avx2x4_h _s:
 M._ststatus_data_avx2x4
 : ststatus = _s
 ==> res.`2 = ststatus_r8 _s /\ res.`3 = ststatus_at_norm _s.
proof.
proc; auto => />.
by have [_ [-> ->]] := ststatus_data_avx2x4P _s.
qed.

phoare ststatus_data_avx2x4_ph _s:
 [ M._ststatus_data_avx2x4
 : ststatus = _s
 ==> res.`2 = ststatus_r8 _s /\ res.`3 = ststatus_at_norm _s
 ] = 1%r.
proof. by conseq ststatus_data_avx2x4_ll (ststatus_data_avx2x4_h _s). qed.

hoare ststatus_data_avx2x4_bnd_h: M._ststatus_data_avx2x4 : true ==> 8 <= res.`2.
proof.
proc*; ecall (ststatus_data_avx2x4_h ststatus); skip => /> &hr r -> _.
smt(ststatus_r8_bounds).
qed.

phoare ststatus_data_avx2x4_bnd_ph: [ M._ststatus_data_avx2x4 : true ==> 8 <= res.`2 ] = 1%r.
proof. by conseq ststatus_data_avx2x4_ll ststatus_data_avx2x4_bnd_h. qed.

(* the status word after the store of the cursor byte (st.[:u8 800] = at) *)
abbrev ststatus_set_at (w: W64.t) (at: int) : W64.t =
 W8u8.pack8_t (W8u8.Pack.init (fun j => if j = 0 then truncateu8 (W64.of_int at) else w \bits8 j)).

lemma ststatus_set_atP (w: W64.t) at:
 0 <= at < 256 =>
 ststatus_at (ststatus_set_at w at) = at
 /\ ststatus_r8 (ststatus_set_at w at) = ststatus_r8 w
 /\ ststatus_trailb (ststatus_set_at w at) = ststatus_trailb w.
proof.
move=> Hat.
have [-> [-> ->]] := ststatus_byte0 (ststatus_set_at w at) w (truncateu8 (W64.of_int at)) _.
+ by move=> j Hj; rewrite W8u8.pack8bE // W8u8.Pack.initiE.
by rewrite to_uint_truncateu8 W64.of_uintK; smt(modz_small pow2_64).
qed.

lemma A25u256toA101u64_100 (X: state4x) s: (A25u256toA101u64 X s).[100] = s.
proof. by rewrite /A25u256toA101u64 Array101.initiE. qed.

lemma absorbing_spec4_sizes r8 tb (l0 l1 l2 l3: W8.t list) st:
 absorbing_spec4 r8 tb l0 l1 l2 l3 st =>
 forall k, 0 <= k < 4 => size (nth [] [l0; l1; l2; l3] k) = size l0.
proof.
rewrite /absorbing_spec4 pabsorb_spec_avx2x4E => [#] S1 S2 S3 _ _ k Hk.
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /=.
qed.

(* the 4-lane 64-bit xor of the updstate code: byte offset 4*a + 8*k of the
   WArray800 view is lane k of the state word a (a multiple of 8) *)
lemma st4x_get_xor64x4_at (st: state4x) a o0 o1 o2 o3 (t0 t1 t2 t3: W64.t) k:
 0 <= a < 200 => a %% 8 = 0 => o0 = 4 * a => o1 = 4 * a + 8 => o2 = 4 * a + 16 => o3 = 4 * a + 24 => 0 <= k < 4 =>
 st4x_get (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 `^` t1)))))) o2 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 `^` t1)))))) o2 `^` t2)))))) o3 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 `^` t1)))))) o2 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 (get64_direct (WArray800.init256 ("_.[_]" (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) o0 (get64_direct (WArray800.init256 ("_.[_]" st)) o0 `^` t0)))))) o1 `^` t1)))))) o2 `^` t2)))))) o3 `^` t3)))) k
 = addstate_at (st4x_get st k) a (u64bytes (nth W64.zero [t0; t1; t2; t3] k)).
proof.
move=> Ha Hm -> -> -> -> Hk.
rewrite (: 4 * a + 24 = 8 * (4 * (a %/ 8) + 3)) 1:/# (: 4 * a + 16 = 8 * (4 * (a %/ 8) + 2)) 1:/# (: 4 * a + 8 = 8 * (4 * (a %/ 8) + 1)) 1:/# (: 4 * a = 8 * (4 * (a %/ 8))) 1:/#.
rewrite (st4x_get_xor64x4 st (a %/ 8) (4 * (a %/ 8)) (4 * (a %/ 8) + 1) (4 * (a %/ 8) + 2) (4 * (a %/ 8) + 3)) 1..6:/#.
by rewrite (: 8 * (a %/ 8) = a) 1:/#.
qed.

(* the 4-lane 64-bit load of the updstate dump *)
lemma st4x_get64_at (st: state4x) a k o:
 0 <= a < 200 => a %% 8 = 0 => 0 <= k < 4 => o = 4 * a + 8 * k =>
 get64_direct (WArray800.init256 ("_.[_]" st)) o = get64_direct (stbytes (st4x_get st k)) a.
proof.
move=> Ha Hm Hk ->; rewrite (get64_init256_at st (4 * a + 8 * k) a k) //.
apply W64.wordP => b Hb; rewrite /WArray200.get64_direct pack8E initiE 1:/# /= W8u8.Pack.initiE 1:/# /= stbytes_st4x 1,2:/# W8u8.bits8iE 1:/#.
congr; smt().
qed.


(* ========================================================================= *)
(* Memory-buffer absorb and squeeze                                          *)
(* ========================================================================= *)

(* ---- lane helpers (memory twins of the array ones in the theory below) ---- *)

(* the first (misaligned) dumped word of a lane, as a byte list: shared by the
   memory dump (stores) and the array dump (afill) *)
lemma dump_first_take (S: WArray200.t) at n:
 0 <= at => at %% 8 <> 0 => 0 <= n => at + n <= 200 =>
 take n (u64bytes (get64_direct S (8 * (at %/ 8)) `>>` W8.of_int (8 * (at %% 8))))
 = sub S at (min n (8 - at %% 8)) ++ u8zeros (min (n - min n (8 - at %% 8)) (at %% 8)).
proof.
move=> H0 Hm Hn Hfit.
rewrite (u64bytes_get64_shr S (8 * (at %/ 8)) (at %% 8)) 1:/# (: 8 * (at %/ 8) + at %% 8 = at) 1:/#.
rewrite take_cat size_sub 1:/#.
case: (n < 8 - at %% 8) => C.
+ by rewrite take_sub200 1:/# (: min n (8 - at %% 8) = n) 1:/# (: min (n - n) (at %% 8) = 0) 1:/# nseq0 cats0.
by rewrite (: min n (8 - at %% 8) = 8 - at %% 8) 1:/# take_nseq.
qed.

(* the four lanes write past their prefixes, over at most q junk bytes *)
lemma stores4_overwrite m b0 b1 b2 b3 (L0 L1 L2 L3 Z0 Z1 Z2 Z3 W0 W1 W2 W3: W8.t list) n q:
 size L0 = n => size L1 = n => size L2 = n => size L3 = n =>
 size Z0 <= q => size Z1 <= q => size Z2 <= q => size Z3 <= q =>
 size W0 = q => size W1 = q => size W2 = q => size W3 = q =>
 0 <= n => disj4 b0 b1 b2 b3 (n + q) =>
 stores (stores (stores (stores (stores4 m b0 b1 b2 b3 (L0 ++ Z0) (L1 ++ Z1) (L2 ++ Z2) (L3 ++ Z3))
   (b0 + n) W0) (b1 + n) W1) (b2 + n) W2) (b3 + n) W3
 = stores4 m b0 b1 b2 b3 (L0 ++ W0) (L1 ++ W1) (L2 ++ W2) (L3 ++ W3).
proof.
rewrite /stores4 /disj4 => S0 S1 S2 S3 HZ0 HZ1 HZ2 HZ3 T0 T1 T2 T3 Hn D.
apply mem_eq_ext => j; rewrite !get_storesE !size_cat S0 S1 S2 S3 T0 T1 T2 T3.
smt(nth_cat size_ge0).
qed.

(* squeeze: one dumped chunk extends the output streams of the four lanes *)
lemma stores4_sqstream_step m r8 (s0 s1 s2 s3: state) k w n b0 b1 b2 b3:
 0 < r8 <= 200 => 0 <= k => 0 <= w => 0 <= n => (k + w) %% r8 + n <= r8 => disj4 b0 b1 b2 b3 (w + n) =>
 stores4 (stores4 m b0 b1 b2 b3 (sqstream r8 s0 k w) (sqstream r8 s1 k w) (sqstream r8 s2 k w) (sqstream r8 s3 k w))
   (b0 + w) (b1 + w) (b2 + w) (b3 + w)
   (sub (stbytes (st_i s0 ((k + w) %/ r8 + 1))) ((k + w) %% r8) n)
   (sub (stbytes (st_i s1 ((k + w) %/ r8 + 1))) ((k + w) %% r8) n)
   (sub (stbytes (st_i s2 ((k + w) %/ r8 + 1))) ((k + w) %% r8) n)
   (sub (stbytes (st_i s3 ((k + w) %/ r8 + 1))) ((k + w) %% r8) n)
 = stores4 m b0 b1 b2 b3 (sqstream r8 s0 k (w + n)) (sqstream r8 s1 k (w + n))
                         (sqstream r8 s2 k (w + n)) (sqstream r8 s3 k (w + n)).
proof.
move=> Hr Hk Hw Hn Hfit D.
rewrite -(sqstream_block r8 s0 (k + w) n) 1..4:/# -(sqstream_block r8 s1 (k + w) n) 1..4:/#.
rewrite -(sqstream_block r8 s2 (k + w) n) 1..4:/# -(sqstream_block r8 s3 (k + w) n) 1..4:/#.
have H := stores4_cat m b0 b1 b2 b3 (sqstream r8 s0 k w) (sqstream r8 s1 k w) (sqstream r8 s2 k w) (sqstream r8 s3 k w) (sqstream r8 s0 (k + w) n) (sqstream r8 s1 (k + w) n) (sqstream r8 s2 (k + w) n) (sqstream r8 s3 (k + w) n) w n _ _ _ _ _ _ _ _ D; 1..8: by rewrite size_sqstream /#.
rewrite H -(sqstream_cat r8 s0 k w n) 1..4:/# -(sqstream_cat r8 s1 k w n) 1..4:/#.
by rewrite -(sqstream_cat r8 s2 k w n) 1..4:/# -(sqstream_cat r8 s3 k w n) 1..4:/#.
qed.


(* ---- add ---- *)

lemma add_m_bcast_updstate_avx2x4_ll: islossless M._add_m_bcast_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_m_bcast_updstate_avx2x4_h _mem _st _at _buf _upto:
 M._add_m_bcast_updstate_avx2x4
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf = _buf /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ addstate_res4m _st _at _mem _buf _buf _buf _buf (_upto - _at) 0 res.`1 res.`2 res.`3 res.`3 res.`3 res.`3.
proof.
proc => /=; pose n := _upto - _at.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2; rewrite and7_mod8 /#.
seq 1 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] n 0 sz [buf; buf; buf; buf] st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 Hk; split; first smt().
    by exists _at; split => //; apply addstate_spec4m_init => /#.
  wp; ecall (m_rlen_read_upto8_h buf len).
  wp; skip => /> &hr H0 H1 H2 Hk Hnz.
have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
move=> _ [o0 t0] /= Hs0 ->.
have Esh : forall (w: W64.t), w `<<` W8.of_int (8 * (_at %% 8)) = w `<<<` 8 * (_at %% 8) by move=> w; rewrite W64.shl_shlw /#.
rewrite Esh truncateu64_VMOV_64.
pose base := 8 * (_at %/ 8).
have Hb : _at - base = _at %% 8 by smt().
have M0 := msubread_rlen _mem t0 base _at _buf n _ _ Hs0; 1,2: smt().
move: M0; rewrite Hb => M0.
have S0 : addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] n 0 base [_buf; _buf; _buf; _buf] _st _at n 0.
+ by apply addstate_spec4m_init => /#.
split => Hc.
+ have Emin : min n (base + 8 - _at) = base + 8 - _at by smt().
  move: M0; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: n - (base + 8 - _at) = _upto - (base + 8)) 1:/# (: base + 8 - _at = 8 - _at %% 8) 1:/# => M0.
  do 2!(split; first smt()).
  exists (base + 8); split; first smt().
  rewrite (: _buf + 8 - _at %% 8 = _buf + (8 - _at %% 8)) 1:/#.
  apply (addstate_spec4m_msubread _mem [_buf; _buf; _buf; _buf] [t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8)] base _st _at n 0 _st _ _at [_buf; _buf; _buf; _buf] n 0 (base + 8) (base + 8) [_buf + (8 - _at %% 8); _buf + (8 - _at %% 8); _buf + (8 - _at %% 8); _buf + (8 - _at %% 8)] (_upto - (base + 8)) 0) => //.
  + smt().
  + smt().
  + by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 _st _ (_at %/ 8)) 1..3:/#.
  + by move=> k Hk'; rewrite !nth4_const.
have Emin : min n (base + 8 - _at) = n by smt().
move: M0; rewrite Emin (: _at + n = _upto) 1:/# (: n - n = 0) 1:/# => M0.
rewrite (: min 8 (max 0 (_upto - _at)) = n) 1:/#.
exists (base + 8); split; first smt().
apply (addstate_spec4m_msubread _mem [_buf; _buf; _buf; _buf] [t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8)] base _st _at n 0 _st _ _at [_buf; _buf; _buf; _buf] n 0 (base + 8) _upto [_buf + n; _buf + n; _buf + n; _buf + n] 0 0) => //.
+ smt().
+ smt().
+ by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 _st _ (_at %/ 8)) 1..3:/#.
by move=> k Hk'; rewrite !nth4_const.
seq 3 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] n 0 sz [buf; buf; buf; buf] st at (_upto - at) 0).
+ while (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 8
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf; _buf; _buf; _buf] n 0 sz [buf; buf; buf; buf] st at (_upto - at) 0); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 3!(split; first smt()).
  exists (sz + 8); split; first smt().
  rewrite (: _upto - (at{hr} + 8) = _upto - at{hr} - 8) 1:/#.
  apply (addstate_spec4m_fullword _mem [_buf; _buf; _buf; _buf] sz _st _at n 0 st{hr} _ buf{hr} buf{hr} buf{hr} buf{hr} at{hr} (_upto - at{hr}) 0) => //.
  + smt().
  + smt().
  by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 st{hr} _ (at{hr} %/ 8)) 1..3:/# (: 8 * (at{hr} %/ 8) = at{hr}) 1:/#.
if; last first.
+ auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  by apply (addstate_spec4m_done _mem _buf _buf _buf _buf sz _st _at n 0 st{hr} buf{hr} buf{hr} buf{hr} buf{hr} _upto 0) => //; smt().
wp; ecall (m_rlen_read_upto8_h buf (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
split; first smt(). move=> _ [o0 t0] /= [Hs0 ->].
rewrite truncateu64_VMOV_64.
have M0 := msubread_rlen _mem t0 at{hr} at{hr} buf{hr} (_upto - at{hr}) _ _ Hs0; 1,2: smt().
move: M0; rewrite (: 8 * (at{hr} - at{hr}) = 0) 1:/# u64_shl0 (: min (_upto - at{hr}) (at{hr} + 8 - at{hr}) = min 8 (max 0 (_upto - at{hr}))) 1:/# (: at{hr} + min 8 (max 0 (_upto - at{hr})) = _upto) 1:/# (: _upto - at{hr} - min 8 (max 0 (_upto - at{hr})) = 0) 1:/# => M0.
apply (addstate_spec4m_finish _mem _buf _buf _buf _buf [t0; t0; t0; t0] sz _st _at n 0 st{hr} _ buf{hr} buf{hr} buf{hr} buf{hr} at{hr} (_upto - at{hr}) 0 _upto (buf{hr} + min 8 (max 0 (_upto - at{hr}))) (buf{hr} + min 8 (max 0 (_upto - at{hr}))) (buf{hr} + min 8 (max 0 (_upto - at{hr}))) (buf{hr} + min 8 (max 0 (_upto - at{hr}))) 0 0) => //.
+ smt().
+ smt().
+ smt().
+ by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 st{hr} _ (at{hr} %/ 8)) 1..3:/# (: 8 * (at{hr} %/ 8) = at{hr}) 1:/#.
by move=> k Hk'; rewrite !nth4_const.
qed.

phoare add_m_bcast_updstate_avx2x4_ph _mem _st _at _buf _upto:
 [ M._add_m_bcast_updstate_avx2x4
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf = _buf /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ addstate_res4m _st _at _mem _buf _buf _buf _buf (_upto - _at) 0 res.`1 res.`2 res.`3 res.`3 res.`3 res.`3
 ] = 1%r.
proof. by conseq add_m_bcast_updstate_avx2x4_ll (add_m_bcast_updstate_avx2x4_h _mem _st _at _buf _upto). qed.

lemma add_m_updstate_avx2x4_ll: islossless M._add_m_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_m_updstate_avx2x4_h _mem _st _at _buf0 _buf1 _buf2 _buf3 _upto:
 M._add_m_updstate_avx2x4
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ upto = _upto /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ addstate_res4m _st _at _mem _buf0 _buf1 _buf2 _buf3 (_upto - _at) 0 res.`1 res.`2 res.`3 res.`4 res.`5 res.`6.
proof.
proc => /=; pose n := _upto - _at.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2; rewrite and7_mod8 /#.
seq 1 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] n 0 sz [buf0; buf1; buf2; buf3] st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 Hk; split; first smt().
    by exists _at; split => //; apply addstate_spec4m_init => /#.
  wp; ecall (m_rlen_read_upto8_h buf3 len); wp; ecall (m_rlen_read_upto8_h buf2 len).
  wp; ecall (m_rlen_read_upto8_h buf1 len); wp; ecall (m_rlen_read_upto8_h buf0 len).
  wp; skip => /> &hr H0 H1 H2 Hk Hnz.
have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
move=> _ [o0 t0] /= Hs0 _ [o1 t1] /= Hs1 _ [o2 t2] /= Hs2 _ [o3 t3] /= Hs3 _.
have Esh : forall (w: W64.t), w `<<` W8.of_int (8 * (_at %% 8)) = w `<<<` 8 * (_at %% 8) by move=> w; rewrite W64.shl_shlw /#.
rewrite !Esh.
pose base := 8 * (_at %/ 8).
have Hb : _at - base = _at %% 8 by smt().
have M0 := msubread_rlen _mem t0 base _at _buf0 n _ _ Hs0; 1,2: smt().
have M1 := msubread_rlen _mem t1 base _at _buf1 n _ _ Hs1; 1,2: smt().
have M2 := msubread_rlen _mem t2 base _at _buf2 n _ _ Hs2; 1,2: smt().
have M3 := msubread_rlen _mem t3 base _at _buf3 n _ _ Hs3; 1,2: smt().
move: M0 M1 M2 M3; rewrite Hb => M0 M1 M2 M3.
have S0 : addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] n 0 base [_buf0; _buf1; _buf2; _buf3] _st _at n 0.
+ by apply addstate_spec4m_init => /#.
split => Hc.
+ have Emin : min n (base + 8 - _at) = base + 8 - _at by smt().
  move: M0 M1 M2 M3; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: n - (base + 8 - _at) = _upto - (base + 8)) 1:/# (: base + 8 - _at = 8 - _at %% 8) 1:/# => M0 M1 M2 M3.
  do 2!(split; first smt()).
  exists (base + 8); split; first smt().
  apply (addstate_spec4m_msubread _mem [_buf0; _buf1; _buf2; _buf3] [t0 `<<<` 8 * (_at %% 8); t1 `<<<` 8 * (_at %% 8); t2 `<<<` 8 * (_at %% 8); t3 `<<<` 8 * (_at %% 8)] base _st _at n 0 _st _ _at [_buf0; _buf1; _buf2; _buf3] n 0 (base + 8) (base + 8) [_buf0 + (8 - _at %% 8); _buf1 + (8 - _at %% 8); _buf2 + (8 - _at %% 8); _buf3 + (8 - _at %% 8)] (_upto - (base + 8)) 0) => //.
  + smt().
  + smt().
  + move=> k Hk'; rewrite (st4x_get_xor64x4_at _st base) //; smt().
  + by rewrite forall4 /=.
have Emin : min n (base + 8 - _at) = n by smt().
move: M0 M1 M2 M3; rewrite Emin (: _at + n = _upto) 1:/# (: n - n = 0) 1:/# => M0 M1 M2 M3.
rewrite (: _upto - _at + _at %% 8 - _at %% 8 = n) 1:/#.
exists (base + 8); split; first smt().
apply (addstate_spec4m_msubread _mem [_buf0; _buf1; _buf2; _buf3] [t0 `<<<` 8 * (_at %% 8); t1 `<<<` 8 * (_at %% 8); t2 `<<<` 8 * (_at %% 8); t3 `<<<` 8 * (_at %% 8)] base _st _at n 0 _st _ _at [_buf0; _buf1; _buf2; _buf3] n 0 (base + 8) _upto [_buf0 + n; _buf1 + n; _buf2 + n; _buf3 + n] 0 0) => //.
+ smt().
+ smt().
+ move=> k Hk'; rewrite (st4x_get_xor64x4_at _st base) //; smt().
by rewrite forall4 /=.
seq 3 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] n 0 sz [buf0; buf1; buf2; buf3] st at (_upto - at) 0).
+ while (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 8
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4m _st _at _mem [_buf0; _buf1; _buf2; _buf3] n 0 sz [buf0; buf1; buf2; buf3] st at (_upto - at) 0); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 3!(split; first smt()).
  exists (sz + 8); split; first smt().
  rewrite (: _upto - (at{hr} + 8) = _upto - at{hr} - 8) 1:/#.
  apply (addstate_spec4m_fullword _mem [_buf0; _buf1; _buf2; _buf3] sz _st _at n 0 st{hr} _ buf0{hr} buf1{hr} buf2{hr} buf3{hr} at{hr} (_upto - at{hr}) 0) => //.
  + smt().
  + smt().
  move=> k Hk'; rewrite (st4x_get_xor64x4_at st{hr} at{hr}) //; smt().
if; last first.
+ auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  by apply (addstate_spec4m_done _mem _buf0 _buf1 _buf2 _buf3 sz _st _at n 0 st{hr} buf0{hr} buf1{hr} buf2{hr} buf3{hr} _upto 0) => //; smt().
wp; ecall (m_rlen_read_upto8_h buf3 (W64.to_uint upto8)); wp; ecall (m_rlen_read_upto8_h buf2 (W64.to_uint upto8)).
wp; ecall (m_rlen_read_upto8_h buf1 (W64.to_uint upto8)); wp; ecall (m_rlen_read_upto8_h buf0 (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
split; first smt(). move=> _ [o0 t0] /= [Hs0 ->].
split; first smt(). move=> _ [o1 t1] /= [Hs1 ->].
split; first smt(). move=> _ [o2 t2] /= [Hs2 ->].
split; first smt(). move=> _ [o3 t3] /= [Hs3 ->].
have M0 := msubread_rlen _mem t0 at{hr} at{hr} buf0{hr} (_upto - at{hr}) _ _ Hs0; 1,2: smt().
have M1 := msubread_rlen _mem t1 at{hr} at{hr} buf1{hr} (_upto - at{hr}) _ _ Hs1; 1,2: smt().
have M2 := msubread_rlen _mem t2 at{hr} at{hr} buf2{hr} (_upto - at{hr}) _ _ Hs2; 1,2: smt().
have M3 := msubread_rlen _mem t3 at{hr} at{hr} buf3{hr} (_upto - at{hr}) _ _ Hs3; 1,2: smt().
move: M0 M1 M2 M3; rewrite (: 8 * (at{hr} - at{hr}) = 0) 1:/# !u64_shl0 (: min (_upto - at{hr}) (at{hr} + 8 - at{hr}) = min 8 (max 0 (_upto - at{hr}))) 1:/# (: at{hr} + min 8 (max 0 (_upto - at{hr})) = _upto) 1:/# (: _upto - at{hr} - min 8 (max 0 (_upto - at{hr})) = 0) 1:/# => M0 M1 M2 M3.
apply (addstate_spec4m_finish _mem _buf0 _buf1 _buf2 _buf3 [t0; t1; t2; t3] sz _st _at n 0 st{hr} _ buf0{hr} buf1{hr} buf2{hr} buf3{hr} at{hr} (_upto - at{hr}) 0 _upto (buf0{hr} + min 8 (max 0 (_upto - at{hr}))) (buf1{hr} + min 8 (max 0 (_upto - at{hr}))) (buf2{hr} + min 8 (max 0 (_upto - at{hr}))) (buf3{hr} + min 8 (max 0 (_upto - at{hr}))) 0 0) => //.
+ smt().
+ smt().
+ smt().
+ move=> k Hk'; rewrite (st4x_get_xor64x4_at st{hr} at{hr}) //; smt().
by rewrite forall4 /=.
qed.

phoare add_m_updstate_avx2x4_ph _mem _st _at _buf0 _buf1 _buf2 _buf3 _upto:
 [ M._add_m_updstate_avx2x4
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ upto = _upto /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ addstate_res4m _st _at _mem _buf0 _buf1 _buf2 _buf3 (_upto - _at) 0 res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
 ] = 1%r.
proof. by conseq add_m_updstate_avx2x4_ll (add_m_updstate_avx2x4_h _mem _st _at _buf0 _buf1 _buf2 _buf3 _upto). qed.


(* ---- absorb ---- *)

lemma absorb_m_bcast_updstate_avx2x4_ll: islossless M._absorb_m_bcast_updstate_avx2x4.
proof.
proc; seq 5: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_avx2x4_ll; call add_m_bcast_updstate_avx2x4_ll; auto => /#.
  by wp; call add_m_bcast_updstate_avx2x4_ll; auto.
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare absorb_m_bcast_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 M._absorb_m_bcast_updstate_avx2x4
 : Glob.mem = _mem /\ buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf _len) (_l1 ++ memread _mem _buf _len)
                              (_l2 ++ memread _mem _buf _len) (_l3 ++ memread _mem _buf _len) res.
proof.
proc => /=; exlim st => _st.
seq 5 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len
         /\ r8 = _r8 /\ buf = _buf
         /\ stk = A101u64toA25u256 _st /\ at = size _l0 %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> -> Habs H0 r [-> ->] /=.
  have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp Er8 Etb Hat.
  by rewrite Hp Er8 Etb Hat /= /A101u64toA25u256.
seq 1 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf <= buf <= _buf + _len
         /\ at = (size _l0 + (buf - _buf)) %% _r8
         /\ len = _len - (buf - _buf) + at /\ len < r8
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] (buf - _buf) stk).
+ while (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf <= buf <= _buf + _len
         /\ at = (size _l0 + (buf - _buf)) %% _r8
         /\ len = _len - (buf - _buf) + at
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len; memread _mem _buf _len] (buf - _buf) stk).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (add_m_bcast_updstate_avx2x4_h Glob.mem stk at buf r8).
    auto => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> Hp Hc.
    have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
    pose k := buf{hr} - _buf.
    pose a := (size _l0 + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ [stc at1 c0] /= Hres r ->.
    have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
    have Hl := addstate_res4m_lanes stk{hr} a _mem _buf _buf _buf _buf _len buf{hr} buf{hr} buf{hr} buf{hr} k (_r8 - a) 0 stc at1 c0 c0 c0 c0 _ _ _ _ _ _ _ Hres; 1..7: smt().
    have Hf := pabsorb4_fill _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) k (_r8 - a) a stk{hr} stc _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt(size_memread).
    have [_ [_ [Ec0 _]]] := Hres.
    rewrite Ec0 /=.
    rewrite (: buf{hr} + (_r8 - a) - _buf = k + (_r8 - a)) 1:/#.
    do 3!(split; first smt()).
    split; first by rewrite (absorb_block_arith (size _l0) k _r8 a) /#.
    split; first smt().
    exact Hf.
  auto => &hr [#] -> -> Habs H0 -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by apply pabsorb4_init.
wp; ecall (add_m_bcast_updstate_avx2x4_h Glob.mem stk at buf len); wp; skip => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> Hc Hp /=.
split; first smt().
move=> _ [stc at1 c0] /= Hres.
rewrite A25u256toA101u64E A101_set800.
have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
pose k := buf{hr} - _buf.
pose a := (size _l0 + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
have Hsz : forall b, size (memread _mem b _len) = _len by move=> b; rewrite size_memread /#.
move: Hres; rewrite (: _len - k + a - a = _len - k) 1:/# => Hres.
have Hl := addstate_res4m_lanes stk{hr} a _mem _buf _buf _buf _buf _len buf{hr} buf{hr} buf{hr} buf{hr} k (_len - k) 0 stc at1 c0 c0 c0 c0 _ _ _ _ _ _ _ Hres; 1..7: smt().
have [_ HL] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) (memread _mem _buf _len) k (_len - k) a stk{hr} stc 0 _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt().
have HL0 := HL _; first done.
have [_ [Eat1 _]] := Hres.
have [Hat2 [Hr2 Htb2]] := ststatus_set_atP _st.[100] at1 _; first smt().
have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp0 Hr0 Htb0 Hat0.
rewrite /absorbing_spec4 A101u64toA25u256K A25u256toA101u64_100; split.
+ have := Hp0; rewrite !pabsorb_spec_avx2x4E !size_cat !Hsz => [#] S1 S2 S3 _.
  rewrite S1 S2 S3 /=.
  move=> j Hj; have := HL0 j Hj.
  have: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  by case => [->|[->|[->|->]]].
have Hl2 := absorb_last_arith (size _l0) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat Hsz.
rewrite (: size _l0 + _len = size _l0 + (k + (_len - k))) 1:/# Hl2.
smt().
qed.

phoare absorb_m_bcast_updstate_avx2x4_ph _mem _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 [ M._absorb_m_bcast_updstate_avx2x4
 : Glob.mem = _mem /\ buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf _len) (_l1 ++ memread _mem _buf _len)
                              (_l2 ++ memread _mem _buf _len) (_l3 ++ memread _mem _buf _len) res
 ] = 1%r.
proof. by conseq absorb_m_bcast_updstate_avx2x4_ll (absorb_m_bcast_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf _len). qed.

lemma absorb_m_updstate_avx2x4_ll: islossless M._absorb_m_updstate_avx2x4.
proof.
proc; seq 5: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_avx2x4_ll; call add_m_updstate_avx2x4_ll; auto => /#.
  by wp; call add_m_updstate_avx2x4_ll; auto.
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare absorb_m_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 M._absorb_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf0 _len) (_l1 ++ memread _mem _buf1 _len)
                              (_l2 ++ memread _mem _buf2 _len) (_l3 ++ memread _mem _buf3 _len) res.
proof.
proc => /=; exlim st => _st.
seq 5 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len
         /\ r8 = _r8 /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ stk = A101u64toA25u256 _st /\ at = size _l0 %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> -> -> -> -> Habs H0 r [-> ->] /=.
  have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp Er8 Etb Hat.
  by rewrite Hp Er8 Etb Hat /= /A101u64toA25u256.
seq 1 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf0 <= buf0 <= _buf0 + _len
         /\ buf1 = _buf1 + (buf0 - _buf0) /\ buf2 = _buf2 + (buf0 - _buf0) /\ buf3 = _buf3 + (buf0 - _buf0)
         /\ at = (size _l0 + (buf0 - _buf0)) %% _r8
         /\ len = _len - (buf0 - _buf0) + at /\ len < r8
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] (buf0 - _buf0) stk).
+ while (Glob.mem = _mem /\ st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf0 <= buf0 <= _buf0 + _len
         /\ buf1 = _buf1 + (buf0 - _buf0) /\ buf2 = _buf2 + (buf0 - _buf0) /\ buf3 = _buf3 + (buf0 - _buf0)
         /\ at = (size _l0 + (buf0 - _buf0)) %% _r8
         /\ len = _len - (buf0 - _buf0) + at
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [memread _mem _buf0 _len; memread _mem _buf1 _len; memread _mem _buf2 _len; memread _mem _buf3 _len] (buf0 - _buf0) stk).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (add_m_updstate_avx2x4_h Glob.mem stk at buf0 buf1 buf2 buf3 r8).
    auto => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> -> -> -> Hp Hc.
    have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
    pose k := buf0{hr} - _buf0.
    pose a := (size _l0 + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ [stc at1 c0 c1 c2 c3] /= Hres r ->.
    have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
    have Hl := addstate_res4m_lanes stk{hr} a _mem _buf0 _buf1 _buf2 _buf3 _len buf0{hr} (_buf1 + k) (_buf2 + k) (_buf3 + k) k (_r8 - a) 0 stc at1 c0 c1 c2 c3 _ _ _ _ _ _ _ Hres; 1..7: smt().
    have Hf := pabsorb4_fill _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf0 _len) (memread _mem _buf1 _len) (memread _mem _buf2 _len) (memread _mem _buf3 _len) k (_r8 - a) a stk{hr} stc _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt(size_memread).
    have [_ [_ [Ec0 [Ec1 [Ec2 Ec3]]]]] := Hres.
    rewrite Ec0 Ec1 Ec2 Ec3 /=.
    rewrite (: buf0{hr} + (_r8 - a) - _buf0 = k + (_r8 - a)) 1:/#.
    do 6!(split; first smt()).
    split; first by rewrite (absorb_block_arith (size _l0) k _r8 a) /#.
    split; first smt().
    exact Hf.
  auto => &hr [#] -> -> Habs H0 -> -> -> -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by apply pabsorb4_init.
wp; ecall (add_m_updstate_avx2x4_h Glob.mem stk at buf0 buf1 buf2 buf3 len); wp; skip => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> -> -> -> Hc Hp /=.
split; first smt().
move=> _ [stc at1 c0 c1 c2 c3] /= Hres.
rewrite A25u256toA101u64E A101_set800.
have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
pose k := buf0{hr} - _buf0.
pose a := (size _l0 + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
have Hsz : forall b, size (memread _mem b _len) = _len by move=> b; rewrite size_memread /#.
move: Hres; rewrite (: _len - k + a - a = _len - k) 1:/# => Hres.
have Hl := addstate_res4m_lanes stk{hr} a _mem _buf0 _buf1 _buf2 _buf3 _len buf0{hr} (_buf1 + k) (_buf2 + k) (_buf3 + k) k (_len - k) 0 stc at1 c0 c1 c2 c3 _ _ _ _ _ _ _ Hres; 1..7: smt().
have [_ HL] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (memread _mem _buf0 _len) (memread _mem _buf1 _len) (memread _mem _buf2 _len) (memread _mem _buf3 _len) k (_len - k) a stk{hr} stc 0 _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt().
have HL0 := HL _; first done.
have [_ [Eat1 _]] := Hres.
have [Hat2 [Hr2 Htb2]] := ststatus_set_atP _st.[100] at1 _; first smt().
have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp0 Hr0 Htb0 Hat0.
rewrite /absorbing_spec4 A101u64toA25u256K A25u256toA101u64_100; split.
+ have := Hp0; rewrite !pabsorb_spec_avx2x4E !size_cat !Hsz => [#] S1 S2 S3 _.
  rewrite S1 S2 S3 /=.
  move=> j Hj; have := HL0 j Hj.
  have: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  by case => [->|[->|[->|->]]].
have Hl2 := absorb_last_arith (size _l0) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat Hsz.
rewrite (: size _l0 + _len = size _l0 + (k + (_len - k))) 1:/# Hl2.
smt().
qed.

phoare absorb_m_updstate_avx2x4_ph _mem _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 [ M._absorb_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf0 _len) (_l1 ++ memread _mem _buf1 _len)
                              (_l2 ++ memread _mem _buf2 _len) (_l3 ++ memread _mem _buf3 _len) res
 ] = 1%r.
proof. by conseq absorb_m_updstate_avx2x4_ll (absorb_m_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len). qed.


(* ---- dump ---- *)

lemma dump_m_updstate_avx2x4_ll: islossless M._dump_m_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare dump_m_updstate_avx2x4_h _mem _buf0 _buf1 _buf2 _buf3 _st _at _upto:
 M._dump_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 (_upto - _at)
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                  (sub (stbytes (st4x_get _st 0)) _at (_upto - _at)) (sub (stbytes (st4x_get _st 1)) _at (_upto - _at))
                  (sub (stbytes (st4x_get _st 2)) _at (_upto - _at)) (sub (stbytes (st4x_get _st 3)) _at (_upto - _at))
   /\ res = (_buf0 + (_upto - _at), _buf1 + (_upto - _at), _buf2 + (_upto - _at), _buf3 + (_upto - _at), _upto).
proof.
proc => /=.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 D; rewrite and7_mod8 /#.
seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 (_upto - _at)
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ buf0 = _buf0 + (at - _at) /\ buf1 = _buf1 + (at - _at) /\ buf2 = _buf2 + (at - _at) /\ buf3 = _buf3 + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                 (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
                 (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)).
+ if; last first.
  + auto => &hr [#] -> -> -> -> -> -> -> -> H0 H1 H2 D Hk Hnz /=.
    have Hal : _at %% 8 = 0 by move: Hnz; rewrite -Hk; smt(W64.to_uint0).
    do !(split; first smt()).
    by exists 0; rewrite !sub200_nil nseq0 /= /stores4 !store0 /#.
  wp; ecall (m_rlen_write_upto8_h Glob.mem buf3 t64 len); wp; ecall (m_rlen_write_upto8_h Glob.mem buf2 t64 len).
  wp; ecall (m_rlen_write_upto8_h Glob.mem buf1 t64 len); wp; ecall (m_rlen_write_upto8_h Glob.mem buf0 t64 len).
  wp; skip => &hr [#] -> -> -> -> -> -> -> -> H0 H1 H2 D Hk Hnz /=.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 0 (4 * (8 * (_at %/ 8)))) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 1 (4 * (8 * (_at %/ 8)) + 8)) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 2 (4 * (8 * (_at %/ 8)) + 16)) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 3 (4 * (8 * (_at %/ 8)) + 24)) 1..4:/#.
  rewrite (dump_first_take (stbytes (st4x_get _st 0)) _at (_upto - _at)) 1..4:/#.
  rewrite (dump_first_take (stbytes (st4x_get _st 1)) _at (_upto - _at)) 1..4:/#.
  rewrite (dump_first_take (stbytes (st4x_get _st 2)) _at (_upto - _at)) 1..4:/#.
  rewrite (dump_first_take (stbytes (st4x_get _st 3)) _at (_upto - _at)) 1..4:/#.
  split; first smt(). move=> _ r0 m0 [-> _].
  split; first smt(). move=> _ r1 m1 [-> _].
  split; first smt(). move=> _ r2 m2 [-> _].
  split; first smt(). move=> _ r3 m3 [-> _].
  case: (8 <= _upto - _at + _at %% 8) => Hc /=.
  + do !(split; first smt()).
    exists (min (_upto - _at - min (_upto - _at) (8 - _at %% 8)) (_at %% 8)).
    rewrite /stores4 (: 8 * (_at %/ 8) + 8 - _at = min (_upto - _at) (8 - _at %% 8)) 1:/#.
    smt().
  do !(split; first smt()).
  exists 0.
  rewrite /stores4 (: min (_upto - _at) (8 - _at %% 8) = _upto - _at) 1:/# (: min (_upto - _at - (_upto - _at)) (_at %% 8) = 0) 1:/#.
  smt().
have UB : forall (t: WArray200.t) o, W8u8.to_list (get64_direct t o) = sub t o 8 by move=> t o; rewrite -u64bytes_get64 /u64bytes.
seq 3 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 (_upto - _at)
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ buf0 = _buf0 + (at - _at) /\ buf1 = _buf1 + (at - _at) /\ buf2 = _buf2 + (at - _at) /\ buf3 = _buf3 + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                 (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
                 (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)).
+ while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 (_upto - _at) /\ newat = at + 8
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ buf0 = _buf0 + (at - _at) /\ buf1 = _buf1 + (at - _at) /\ buf2 = _buf2 + (at - _at) /\ buf3 = _buf3 + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                 (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
                 (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z) (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 D -> Ha0 Ha1 Ha8 -> -> -> -> [z [Hz [Hzl ->]]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  rewrite (st4x_get64_at _st at{hr} 0 (4 * at{hr})) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 1 (4 * at{hr} + 8)) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 2 (4 * at{hr} + 16)) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 3 (4 * at{hr} + 24)) 1..4:/#.
  rewrite !storeW64E !UB.
  do !(split; first smt()).
  exists 0; rewrite nseq0 !cats0; do 2!(split; first smt()).
  have SO := stores4_overwrite _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 1)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 2)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 3)) _at (at{hr} - _at)) (u8zeros z) (u8zeros z) (u8zeros z) (u8zeros z) (sub (stbytes (st4x_get _st 0)) at{hr} 8) (sub (stbytes (st4x_get _st 1)) at{hr} 8) (sub (stbytes (st4x_get _st 2)) at{hr} 8) (sub (stbytes (st4x_get _st 3)) at{hr} 8) (at{hr} - _at) 8 _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt(size_nseq).
  + smt(size_nseq).
  + smt(size_nseq).
  + smt(size_nseq).
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt(WArray200.size_sub).
  + smt().
  + by apply (disj4_le _ _ _ _ (_upto - _at)) => /#.
  rewrite SO.
  rewrite (: at{hr} + 8 - _at = (at{hr} - _at) + 8) 1:/#.
  rewrite (sub_cat (stbytes (st4x_get _st 0)) _at (at{hr} - _at) 8) 1,2:/# (sub_cat (stbytes (st4x_get _st 1)) _at (at{hr} - _at) 8) 1,2:/#.
  rewrite (sub_cat (stbytes (st4x_get _st 2)) _at (at{hr} - _at) 8) 1,2:/# (sub_cat (stbytes (st4x_get _st 3)) _at (at{hr} - _at) 8) 1,2:/#.
  by rewrite (: _at + (at{hr} - _at) = at{hr}) 1:/#.
if; last first.
+ auto => &hr [#] _ -> H0 H1 H2 D Ha0 Ha1 Ha8 Hlt -> -> -> -> [z [Hz [Hzl ->]]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  have Ez : z = 0 by smt().
  by rewrite Ea Ez nseq0 !cats0.
wp; ecall (m_rlen_write_upto8_h Glob.mem buf3 t64 (W64.to_uint upto8)); wp; ecall (m_rlen_write_upto8_h Glob.mem buf2 t64 (W64.to_uint upto8)).
wp; ecall (m_rlen_write_upto8_h Glob.mem buf1 t64 (W64.to_uint upto8)); wp; ecall (m_rlen_write_upto8_h Glob.mem buf0 t64 (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> H0 H1 H2 D Ha0 Ha1 Ha8 Hlt -> -> -> -> [z [Hz [Hzl ->]]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
rewrite (st4x_get64_at _st at{hr} 0 (4 * at{hr})) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 1 (4 * at{hr} + 8)) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 2 (4 * at{hr} + 16)) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 3 (4 * at{hr} + 24)) 1..4:/#.
rewrite !u64bytes_get64.
rewrite (take_sub200 (stbytes (st4x_get _st 0)) at{hr} (_upto - at{hr}) 8) 1:/# (take_sub200 (stbytes (st4x_get _st 1)) at{hr} (_upto - at{hr}) 8) 1:/#.
rewrite (take_sub200 (stbytes (st4x_get _st 2)) at{hr} (_upto - at{hr}) 8) 1:/# (take_sub200 (stbytes (st4x_get _st 3)) at{hr} (_upto - at{hr}) 8) 1:/#.
split; first smt(). move=> _ r0 m0 [-> ->].
split; first smt(). move=> _ r1 m1 [-> ->].
split; first smt(). move=> _ r2 m2 [-> ->].
split; first smt(). move=> _ r3 m3 [-> ->].
have SO := stores4_overwrite _mem _buf0 _buf1 _buf2 _buf3 (sub (stbytes (st4x_get _st 0)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 1)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 2)) _at (at{hr} - _at)) (sub (stbytes (st4x_get _st 3)) _at (at{hr} - _at)) (u8zeros z) (u8zeros z) (u8zeros z) (u8zeros z) (sub (stbytes (st4x_get _st 0)) at{hr} (_upto - at{hr})) (sub (stbytes (st4x_get _st 1)) at{hr} (_upto - at{hr})) (sub (stbytes (st4x_get _st 2)) at{hr} (_upto - at{hr})) (sub (stbytes (st4x_get _st 3)) at{hr} (_upto - at{hr})) (at{hr} - _at) (_upto - at{hr}) _ _ _ _ _ _ _ _ _ _ _ _ _ _.
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt(size_nseq).
+ smt(size_nseq).
+ smt(size_nseq).
+ smt(size_nseq).
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt(WArray200.size_sub).
+ smt().
+ by apply (disj4_le _ _ _ _ (_upto - _at)) => /#.
rewrite SO.
have SC : forall (S: WArray200.t), sub S _at (at{hr} - _at) ++ sub S at{hr} (_upto - at{hr}) = sub S _at (_upto - _at).
+ by move=> S; rewrite (: _upto - _at = (at{hr} - _at) + (_upto - at{hr})) 1:/# (sub_cat S _at (at{hr} - _at) (_upto - at{hr})) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
rewrite !SC /=.
smt().
qed.

phoare dump_m_updstate_avx2x4_ph _mem _buf0 _buf1 _buf2 _buf3 _st _at _upto:
 [ M._dump_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ disj4 _buf0 _buf1 _buf2 _buf3 (_upto - _at)
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                  (sub (stbytes (st4x_get _st 0)) _at (_upto - _at)) (sub (stbytes (st4x_get _st 1)) _at (_upto - _at))
                  (sub (stbytes (st4x_get _st 2)) _at (_upto - _at)) (sub (stbytes (st4x_get _st 3)) _at (_upto - _at))
   /\ res = (_buf0 + (_upto - _at), _buf1 + (_upto - _at), _buf2 + (_upto - _at), _buf3 + (_upto - _at), _upto)
 ] = 1%r.
proof. by conseq dump_m_updstate_avx2x4_ll (dump_m_updstate_avx2x4_h _mem _buf0 _buf1 _buf2 _buf3 _st _at _upto). qed.


(* ---- squeeze ---- *)

lemma squeeze_m_updstate_avx2x4_ll: islossless M._squeeze_m_updstate_avx2x4.
proof.
proc; seq 4: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 2: (8 <= r8) => //.
  + by wp; if; [wp; call keccakf1600_avx2x4_ll; auto | auto].
  + seq 1: true => //.
    + while (8 <= r8) len => [z|]; last by auto => /#.
      by wp; call keccakf1600_avx2x4_ll; call dump_m_updstate_avx2x4_ll; auto => /#.
    by wp; call dump_m_updstate_avx2x4_ll; auto.
  by hoare; wp; if; [wp; ecall (keccakf1600_avx2x4_h stk); auto | auto].
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare squeeze_m_updstate_avx2x4_h _mem _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 M._squeeze_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                  (sqstream _r8 (st4x_get _s0 0) _k _len) (sqstream _r8 (st4x_get _s0 1) _k _len)
                  (sqstream _r8 (st4x_get _s0 2) _k _len) (sqstream _r8 (st4x_get _s0 3) _k _len)
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res.
proof.
proc => /=; exlim st => _st.
seq 4 : (Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ stk = iter ((_k - 1) %/ _r8 + 1) keccak_f1600_x4 _s0).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> -> -> -> -> Hsq H0 D r [-> ->] /=.
  have := Hsq; rewrite /squeezing_spec4 => [#] Hr0 Hr1 Hk Est Er8 Eat.
  rewrite Er8 Eat /= -Est.
  by rewrite /A101u64toA25u256 /=; smt().
seq 2 : (Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ len = _len + at /\ stk = iter (_k %/ _r8 + 1) keccak_f1600_x4 _s0).
+ wp; if.
  + wp; ecall (keccakf1600_avx2x4_h stk); auto => &hr [#] -> -> -> -> -> -> Hsq H0 D -> -> Hat -> Hz.
    have [Hr [Hk _]] := Hsq.
    move=> r ->; do !(split; first smt()).
    rewrite -(squeeze_entry0 _r8 _k) 1,2:/# (iterS ((_k - 1) %/ _r8 + 1)); first by apply (squeeze_entry_ge0 _r8 _k) => /#.
    by rewrite /keccak_f1600_x4.
  auto => &hr [#] -> -> -> -> -> -> Hsq H0 D -> -> Hat -> Hz.
  have [Hr [Hk _]] := Hsq.
  by rewrite (squeeze_entry1 _r8 _k) 1,2:/#.
seq 1 : (Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
            (sqstream _r8 (st4x_get _s0 0) _k (buf0 - _buf0)) (sqstream _r8 (st4x_get _s0 1) _k (buf0 - _buf0))
            (sqstream _r8 (st4x_get _s0 2) _k (buf0 - _buf0)) (sqstream _r8 (st4x_get _s0 3) _k (buf0 - _buf0))
         /\ buf1 = _buf1 + (buf0 - _buf0) /\ buf2 = _buf2 + (buf0 - _buf0) /\ buf3 = _buf3 + (buf0 - _buf0)
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ st = _st /\ r8 = _r8
         /\ stk = iter ((_k + (buf0 - _buf0)) %/ _r8 + 1) keccak_f1600_x4 _s0 /\ at = (_k + (buf0 - _buf0)) %% _r8
         /\ len = at + (_len - (buf0 - _buf0)) /\ 0 <= buf0 - _buf0 < _len /\ len <= r8).
+ while (Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
            (sqstream _r8 (st4x_get _s0 0) _k (buf0 - _buf0)) (sqstream _r8 (st4x_get _s0 1) _k (buf0 - _buf0))
            (sqstream _r8 (st4x_get _s0 2) _k (buf0 - _buf0)) (sqstream _r8 (st4x_get _s0 3) _k (buf0 - _buf0))
         /\ buf1 = _buf1 + (buf0 - _buf0) /\ buf2 = _buf2 + (buf0 - _buf0) /\ buf3 = _buf3 + (buf0 - _buf0)
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len /\ st = _st /\ r8 = _r8
         /\ stk = iter ((_k + (buf0 - _buf0)) %/ _r8 + 1) keccak_f1600_x4 _s0 /\ at = (_k + (buf0 - _buf0)) %% _r8
         /\ len = at + (_len - (buf0 - _buf0)) /\ 0 <= buf0 - _buf0 < _len).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (dump_m_updstate_avx2x4_h Glob.mem buf0 buf1 buf2 buf3 stk at r8).
    auto => &hr [#] -> -> -> -> Hsq H0 D -> -> -> -> -> Hw0 Hw1 Hc.
    have [Hr [Hk _]] := Hsq.
    pose w := buf0{hr} - _buf0.
    have Eb0 : buf0{hr} = _buf0 + w by smt().
    have Ha : 0 <= (_k + w) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    rewrite Eb0.
    split.
    + split; first smt().
      by apply (disj4_shift _ _ _ _ _len) => /#.
    move=> _ rr mem [-> ->] r -> /=.
    have G : forall j, 0 <= j < 4 => st4x_get (iter ((_k + w) %/ _r8 + 1) keccak_f1600_x4 _s0) j = st_i (st4x_get _s0 j) ((_k + w) %/ _r8 + 1).
    + by move=> j Hj; apply st4x_get_iter => //; smt(divz_ge0).
    rewrite (G 0) // (G 1) // (G 2) // (G 3) //.
    have SS := stores4_sqstream_step _mem _r8 (st4x_get _s0 0) (st4x_get _s0 1) (st4x_get _s0 2) (st4x_get _s0 3) _k w (_r8 - (_k + w) %% _r8) _buf0 _buf1 _buf2 _buf3 _ _ _ _ _ _; 1..5: smt().
    + by apply (disj4_le _ _ _ _ _len) => /#.
    rewrite SS (: _buf0 + w + (_r8 - (_k + w) %% _r8) - _buf0 = w + (_r8 - (_k + w) %% _r8)) 1:/#.
    have [Hp0 Hp1] := squeeze_pos_arith _r8 (_k + w) ((_k + w) %% _r8) _ _; 1,2: smt().
    rewrite (: _k + (w + (_r8 - (_k + w) %% _r8)) = _k + w + (_r8 - (_k + w) %% _r8)) 1:/# Hp0 Hp1.
    split; first done.
    do 3!(split; first smt()).
    split; first exact Hsq.
    split; first smt().
    split; first exact D.
    split; first by rewrite (iterS ((_k + w) %/ _r8 + 1)); [smt(divz_ge0) | rewrite /keccak_f1600_x4].
    smt().
  auto => &hr [#] -> -> -> -> -> Hsq H0 D -> -> -> -> -> /=.
  have [Hr [Hk _]] := Hsq.
  split; last by smt().
  have E0 : forall j, sqstream _r8 (st4x_get _s0 j) _k 0 = [] by move=> j; rewrite -size_eq0 size_sqstream.
  by rewrite !E0 /stores4 !store0 /#.
wp; ecall (dump_m_updstate_avx2x4_h Glob.mem buf0 buf1 buf2 buf3 stk at len); wp; skip => &hr [#] -> -> -> -> Hsq H0 D -> -> -> -> -> Hw0 Hw1 Hle /=.
have [Hr [Hk _]] := Hsq.
pose w := buf0{hr} - _buf0.
have Eb0 : buf0{hr} = _buf0 + w by smt().
have Ha : 0 <= (_k + w) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
rewrite Eb0.
split.
+ split; first smt().
  by apply (disj4_shift _ _ _ _ _len) => /#.
move=> _ rr mem [-> ->] /=.
rewrite A25u256toA101u64E A101_set800.
rewrite (: (_k + w) %% _r8 + (_len - w) - (_k + w) %% _r8 = _len - w) 1:/#.
have G : forall j, 0 <= j < 4 => st4x_get (iter ((_k + w) %/ _r8 + 1) keccak_f1600_x4 _s0) j = st_i (st4x_get _s0 j) ((_k + w) %/ _r8 + 1).
+ by move=> j Hj; apply st4x_get_iter => //; smt(divz_ge0).
rewrite (G 0) // (G 1) // (G 2) // (G 3) //.
have SS := stores4_sqstream_step _mem _r8 (st4x_get _s0 0) (st4x_get _s0 1) (st4x_get _s0 2) (st4x_get _s0 3) _k w (_len - w) _buf0 _buf1 _buf2 _buf3 _ _ _ _ _ _; 1..5: smt().
+ by apply (disj4_le _ _ _ _ _len) => /#.
rewrite SS (: w + (_len - w) = _len) 1:/#.
have [Fq Fm] := squeeze_fin_arith _r8 (_k + w) ((_k + w) %% _r8) (_len - w) _ _ _ _; 1..4: smt().
have [Hat2 [Hr2 _]] := ststatus_set_atP _st.[100] ((_k + w) %% _r8 + (_len - w)) _; first smt().
have [_ [_ [_ [Hr0 _]]]] := Hsq.
split; first done.
rewrite /squeezing_spec4 A101u64toA25u256K A25u256toA101u64_100 /ststatus_at_norm Hr2 Hr0 Hat2.
rewrite (: _k + _len - 1 = _k + w + (_len - w) - 1) 1:/# Fq (: _k + _len = _k + w + (_len - w)) 1:/# Fm.
smt().
qed.

phoare squeeze_m_updstate_avx2x4_ph _mem _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 [ M._squeeze_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                  (sqstream _r8 (st4x_get _s0 0) _k _len) (sqstream _r8 (st4x_get _s0 1) _k _len)
                  (sqstream _r8 (st4x_get _s0 2) _k _len) (sqstream _r8 (st4x_get _s0 3) _k _len)
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res
 ] = 1%r.
proof. by conseq squeeze_m_updstate_avx2x4_ll (squeeze_m_updstate_avx2x4_h _mem _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len). qed.


(* ---- the exported wrappers ---- *)

lemma absorb_m_bcast_updstate_avx2x4_export_ll: islossless M.absorb_m_bcast_updstate_avx2x4.
proof. by proc; call absorb_m_bcast_updstate_avx2x4_ll; auto. qed.

hoare absorb_m_bcast_updstate_avx2x4_export_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 M.absorb_m_bcast_updstate_avx2x4
 : Glob.mem = _mem /\ buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf _len) (_l1 ++ memread _mem _buf _len)
                              (_l2 ++ memread _mem _buf _len) (_l3 ++ memread _mem _buf _len) res.
proof. by proc; ecall (absorb_m_bcast_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf _len); auto. qed.

lemma absorb_m_updstate_avx2x4_export_ll: islossless M.absorb_m_updstate_avx2x4.
proof. by proc; call absorb_m_updstate_avx2x4_ll; auto. qed.

hoare absorb_m_updstate_avx2x4_export_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 M.absorb_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len
 ==> Glob.mem = _mem
   /\ absorbing_spec4 _r8 _tb (_l0 ++ memread _mem _buf0 _len) (_l1 ++ memread _mem _buf1 _len)
                              (_l2 ++ memread _mem _buf2 _len) (_l3 ++ memread _mem _buf3 _len) res.
proof. by proc; ecall (absorb_m_updstate_avx2x4_h _mem _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len); auto. qed.

lemma squeeze_m_updstate_avx2x4_export_ll: islossless M.squeeze_m_updstate_avx2x4.
proof. by proc; call squeeze_m_updstate_avx2x4_ll; auto. qed.

hoare squeeze_m_updstate_avx2x4_export_h _mem _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 M.squeeze_m_updstate_avx2x4
 : Glob.mem = _mem /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len /\ disj4 _buf0 _buf1 _buf2 _buf3 _len
 ==> Glob.mem = stores4 _mem _buf0 _buf1 _buf2 _buf3
                  (sqstream _r8 (st4x_get _s0 0) _k _len) (sqstream _r8 (st4x_get _s0 1) _k _len)
                  (sqstream _r8 (st4x_get _s0 2) _k _len) (sqstream _r8 (st4x_get _s0 3) _k _len)
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res.
proof. by proc; ecall (squeeze_m_updstate_avx2x4_h _mem _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len); auto. qed.


(* ========================================================================= *)
(* Array-buffer absorb and squeeze                                           *)
(* ========================================================================= *)

abstract theory KeccakUpdstateAvx2x4.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

(* the 4-lane array layer of the fixedsizes proofs (and its ReadWriteArray) *)
clone import KeccakArrayAvx2x4 as FX
 with op _ASIZE <- _ASIZE,
      theory A <- A,
      theory WA <- WA
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

import RW.

(* The extracted array procedures (Keccak1600_Jazz_ASIZE at _ASIZE = 999),
   with Array999/WArray999 replaced by A/WA and the size-independent callees
   taken from Keccak1600_Jazz.M (checked by Keccak1600_updstate_avx2x4_checkXtr). *)
module MM = {
  proc _add_bcast_updstate_avx2x4 (st:W256.t Array25.t, at:int,
                                   buf:W8.t A.t, off:int, upto:int) : 
  W256.t Array25.t * int * int = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t128:W128.t;
    var t256:W256.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (off2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, len);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      t128 <- (VMOV_64 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0) t256)));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t256 <-
      (VPBROADCAST_4u64
      (get64_direct (WA.init8 (fun i => buf.[i])) off));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) (4 * at)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) 
      (4 * at) t256)));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, (W64.to_uint upto8));
      t128 <- (VMOV_64 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) (4 * at)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) 
      (4 * at) t256)));
    } else {
      
    }
    at <- upto;
    return (st, at, off);
  }

  proc _absorb_bcast_updstate_avx2x4 (st:W64.t Array101.t,
                                      buf:W8.t A.t, len:int) : 
  W64.t Array101.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ M._ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (stk, at, off) <@ _add_bcast_updstate_avx2x4 (stk, at, buf, off, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (stk, at,  _1) <@ _add_bcast_updstate_avx2x4 (stk, at, buf, off, len);
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }

  proc _add_updstate_avx2x4 (st:W256.t Array25.t, at:int,
                             buf0:W8.t A.t, buf1:W8.t A.t,
                             buf2:W8.t A.t, buf3:W8.t A.t,
                             off:int, upto:int) : W256.t Array25.t * int *
                                                  int = {
    var at8:W64.t;
    var shval:W8.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      shval <- (truncateu8 at8);
      shval <- (shval `<<` (W8.of_int 3));
      ( _0, t64) <@ RW.MM.__a_rlen_read_upto8 (buf0, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      ( _1, t64) <@ RW.MM.__a_rlen_read_upto8 (buf1, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      ( _2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf2, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      (off2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf3, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WA.init8 (fun i => buf0.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf1.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf2.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf3.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      ( _3, t64) <@ RW.MM.__a_rlen_read_upto8 (buf0, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      ( _4, t64) <@ RW.MM.__a_rlen_read_upto8 (buf1, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      ( _5, t64) <@ RW.MM.__a_rlen_read_upto8 (buf2, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf3, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
    } else {
      
    }
    at <- upto;
    return (st, at, off);
  }

  proc _absorb_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                                buf1:W8.t A.t, buf2:W8.t A.t,
                                buf3:W8.t A.t, len:int) : W64.t Array101.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ M._ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    (* Erased call to spill *)
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (* Erased call to spill *)
      (stk, at, off) <@ _add_updstate_avx2x4 (stk, at, buf0, buf1, buf2,
      buf3, off, r8);
      (* Erased call to unspill *)
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (stk, at,  _1) <@ _add_updstate_avx2x4 (stk, at, buf0, buf1, buf2, 
    buf3, off, len);
    (* Erased call to unspill *)
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }

  proc _dump_updstate_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                              buf2:W8.t A.t, buf3:W8.t A.t,
                              off:int, st:W256.t Array25.t, at:int, upto:int) : 
  W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t *
  int * int = {
    var at8:W64.t;
    var sh:W8.t;
    var t64:W64.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf0,  _0) <@ RW.MM.__a_rlen_write_upto8 (buf0, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf1,  _1) <@ RW.MM.__a_rlen_write_upto8 (buf1, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf2,  _2) <@ RW.MM.__a_rlen_write_upto8 (buf2, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf3, off2) <@ RW.MM.__a_rlen_write_upto8 (buf3, off, t64, len);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      buf0 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf0.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf1.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf2.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf3.[i])) off t64))
      );
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      (buf0,  _3) <@ RW.MM.__a_rlen_write_upto8 (buf0, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      (buf1,  _4) <@ RW.MM.__a_rlen_write_upto8 (buf1, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      (buf2,  _5) <@ RW.MM.__a_rlen_write_upto8 (buf2, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      (buf3, off) <@ RW.MM.__a_rlen_write_upto8 (buf3, off, t64,
      (W64.to_uint upto8));
    } else {
      
    }
    at <- upto;
    return (buf0, buf1, buf2, buf3, off, at);
  }

  proc _squeeze_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                                 buf1:W8.t A.t, buf2:W8.t A.t,
                                 buf3:W8.t A.t, len:int) : W64.t Array101.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ M._ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    if ((at = 0)) {
      stk <@ M._keccakf1600_avx2x4 (stk);
    } else {
      
    }
    off <- 0;
    len <- (len + at);
    while ((r8 < len)) {
      (buf0, buf1, buf2, buf3, off, at) <@ _dump_updstate_avx2x4 (buf0, 
      buf1, buf2, buf3, off, stk, at, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (buf0, buf1, buf2, buf3,  _1, at) <@ _dump_updstate_avx2x4 (buf0, 
    buf1, buf2, buf3, off, stk, at, len);
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return (st, buf0, buf1, buf2, buf3);
  }

  proc absorb_bcast_updstate_avx2x4 (st:W64.t Array101.t,
                                     buf:W8.t A.t, len:int) : 
  W64.t Array101.t = {
    
    st <- st;
    buf <- buf;
    len <- len;
    st <@ _absorb_bcast_updstate_avx2x4 (st, buf, len);
    return st;
  }

  proc absorb_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                               buf1:W8.t A.t, buf2:W8.t A.t,
                               buf3:W8.t A.t, len:int) : W64.t Array101.t = {
    
    st <- st;
    buf0 <- buf0;
    buf1 <- buf1;
    buf2 <- buf2;
    buf3 <- buf3;
    len <- len;
    st <@ _absorb_updstate_avx2x4 (st, buf0, buf1, buf2, buf3, len);
    return st;
  }

  proc squeeze_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                                buf1:W8.t A.t, buf2:W8.t A.t,
                                buf3:W8.t A.t, len:int) : W64.t Array101.t *
                                                                 W8.t A.t *
                                                                 W8.t A.t *
                                                                 W8.t A.t *
                                                                 W8.t A.t = {
    
    st <- st;
    buf0 <- buf0;
    buf1 <- buf1;
    buf2 <- buf2;
    buf3 <- buf3;
    (st, buf0, buf1, buf2, buf3) <@ _squeeze_updstate_avx2x4 (st, buf0, 
    buf1, buf2, buf3, len);
    return (st, buf0, buf1, buf2, buf3);
  }
}.

(* ---- lane helpers ---- *)

(* addstate_res4 (tb = 0) as the chunks of the absorbed inputs sub b 0 len *)
lemma addstate_res4_sub (st stc: state4x) a (b0 b1 b2 b3: W8.t A.t) len off n at1 c1:
 0 <= off => 0 <= n => off + n <= len => len <= _ASIZE =>
 addstate_res4 st a [b0; b1; b2; b3] off n 0 stc at1 c1 =>
 addstate_lanes st a [take n (drop off (sub b0 0 len)); take n (drop off (sub b1 0 len));
                      take n (drop off (sub b2 0 len)); take n (drop off (sub b3 0 len))] 0 stc.
proof.
move=> H0 H1 H2 H3 [Hl _] k Hk; rewrite Hl // /= !cats0.
have E : forall (b: W8.t A.t), take n (drop off (sub b 0 len)) = sub b off n.
+ by move=> b; rewrite drop_sub take_sub; congr; smt().
have: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
by case => [->|[->|[->|->]]] /=; rewrite E.
qed.

(* dump: the first (misaligned) word of a lane *)
lemma dump_lane_first (S: WArray200.t) (b: W8.t A.t) off at n:
 0 <= at => at %% 8 <> 0 => 0 <= n => at + n <= 200 =>
 A.fill (fun i => (u64bytes (get64_direct S (8 * (at %/ 8)) `>>` W8.of_int (8 * (at %% 8)))).[i - off]) off (min 8 (max 0 n)) b
 = afill b off (sub S at (min n (8 - at %% 8)) ++ u8zeros (min (n - min n (8 - at %% 8)) (at %% 8))).
proof. by move=> H0 Hm Hn Hfit; rewrite afill_rlen 1:/# (dump_first_take S at n). qed.

(* dump: a full (aligned) word of a lane *)
lemma dump_lane_step8 (S: WArray200.t) (b: W8.t A.t) off at0 at z:
 0 <= at0 <= at => at + 8 <= 200 => 0 <= z <= 8 =>
 A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" (afill b off (sub S at0 (at - at0) ++ u8zeros z)))) (off + (at - at0)) (get64_direct S at)))
 = afill b off (sub S at0 (at + 8 - at0) ++ u8zeros 0).
proof.
move=> Ha Hb Hz.
rewrite a_set64_afill u64bytes_get64 nseq0 cats0.
have Hsz : size (sub S at0 (at - at0)) = at - at0 by rewrite size_sub /#.
have := afill_overwrite b off (sub S at0 (at - at0)) (u8zeros z) (sub S at 8) _.
+ by rewrite size_nseq size_sub /#.
rewrite Hsz => ->.
by rewrite (: at + 8 - at0 = (at - at0) + 8) 1:/# (sub_cat S at0 (at - at0) 8) 1,2:/# (: at0 + (at - at0) = at) 1:/#.
qed.

(* dump: the last (partial, aligned) word of a lane *)
lemma dump_lane_last (S: WArray200.t) (b: W8.t A.t) off at0 at upto z:
 0 <= at0 <= at < upto => upto <= 200 => upto < at + 8 => 0 <= z <= upto - at =>
 A.fill (fun i => (u64bytes (get64_direct S at)).[i - (off + (at - at0))]) (off + (at - at0)) (min 8 (max 0 (upto - at)))
        (afill b off (sub S at0 (at - at0) ++ u8zeros z))
 = afill b off (sub S at0 (upto - at0)).
proof.
move=> Ha Hu Hlt Hz.
rewrite afill_rlen 1:/# u64bytes_get64 take_sub200 1:/#.
have Hsz : size (sub S at0 (at - at0)) = at - at0 by rewrite size_sub /#.
have := afill_overwrite b off (sub S at0 (at - at0)) (u8zeros z) (sub S at (upto - at)) _.
+ by rewrite size_nseq size_sub /#.
rewrite Hsz => ->.
by rewrite (: upto - at0 = (at - at0) + (upto - at)) 1:/# (sub_cat S at0 (at - at0) (upto - at)) 1,2:/# (: at0 + (at - at0) = at) 1:/#.
qed.

(* squeeze: one dumped chunk extends the output stream of a lane *)
lemma afill_sqstream_step r8 (s0: state) k w n (b: W8.t A.t):
 0 < r8 <= 200 => 0 <= k => 0 <= w => 0 <= n => (k + w) %% r8 + n <= r8 =>
 afill (afill b 0 (sqstream r8 s0 k w)) w (sub (stbytes (st_i s0 ((k + w) %/ r8 + 1))) ((k + w) %% r8) n)
 = afill b 0 (sqstream r8 s0 k (w + n)).
proof.
move=> Hr Hk Hw Hn Hfit.
rewrite -(sqstream_block r8 s0 (k + w) n) 1..4:/# (sqstream_cat r8 s0 k w n) 1..4:/#.
have := afill_overwrite b 0 (sqstream r8 s0 k w) [] (sqstream r8 s0 (k + w) n) _; first by rewrite size_ge0.
by rewrite cats0 size_sqstream 1..3:/# /=.
qed.


(* ---- add ---- *)

lemma add_updstate_avx2x4_ll: islossless MM._add_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_updstate_avx2x4_h _st _at _buf0 _buf1 _buf2 _buf3 _off _upto:
 MM._add_updstate_avx2x4
 : st = _st /\ at = _at /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> addstate_res4 _st _at [_buf0; _buf1; _buf2; _buf3] _off (_upto - _at) 0 res.`1 res.`2 res.`3.
proof.
proc => /=; pose n := _upto - _at.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 H3 H4; rewrite and7_mod8 /#.
seq 1 : (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf0 _off n; sub _buf1 _off n; sub _buf2 _off n; sub _buf3 _off n] 0 sz _off off st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 H3 H4 Hk; split; first smt().
    exists _at; split => //; apply addstate_spec4_init => //.
    by move=> k Hk'; rewrite nth_sub4 // A.size_sub /#.
  wp; ecall (a_rlen_read_upto8_h buf3 off len); wp; ecall (a_rlen_read_upto8_h buf2 off len).
  wp; ecall (a_rlen_read_upto8_h buf1 off len); wp; ecall (a_rlen_read_upto8_h buf0 off len).
  wp; skip => /> &hr H0 H1 H2 H3 H4 Hk Hnz.
have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
move=> _ [o0 t0] /= Hs0 Ho0 [o1 t1] /= Hs1 Ho1 [o2 t2] /= Hs2 Ho2 [o3 t3] /= Hs3 ->.
have Esh : forall (w: W64.t), w `<<` W8.of_int (8 * (_at %% 8)) = w `<<<` 8 * (_at %% 8) by move=> w; rewrite W64.shl_shlw /#.
rewrite !Esh.
pose base := 8 * (_at %/ 8).
have Hb : _at - base = _at %% 8 by smt().
have M0 := asubread_rlen _buf0 t0 base _at _off 0 n _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M1 := asubread_rlen _buf1 t1 base _at _off 0 n _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M2 := asubread_rlen _buf2 t2 base _at _off 0 n _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M3 := asubread_rlen _buf3 t3 base _at _off 0 n _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
move: M0 M1 M2 M3; rewrite Hb => M0 M1 M2 M3.
have S0 : addstate_spec4 _st _at [sub _buf0 _off n; sub _buf1 _off n; sub _buf2 _off n; sub _buf3 _off n] 0 base _off (_off + 0) _st _at n 0.
+ rewrite addz0; apply addstate_spec4_init; first smt().
  by move=> k Hk'; rewrite nth_sub4 // A.size_sub /#.
split => Hc.
+ have Emin : min n (base + 8 - _at) = base + 8 - _at by smt().
  move: M0 M1 M2 M3; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: 0 + (base + 8 - _at) = 8 - _at %% 8) 1:/# (: n - (base + 8 - _at) = _upto - (base + 8)) 1:/# => M0 M1 M2 M3.
  do 2!(split; first smt()).
  exists (base + 8); split; first smt().
  rewrite (: _off + 8 - _at %% 8 = _off + (8 - _at %% 8)) 1:/#.
  apply (addstate_spec4_asubread _buf0 _buf1 _buf2 _buf3 [t0 `<<<` 8 * (_at %% 8); t1 `<<<` 8 * (_at %% 8); t2 `<<<` 8 * (_at %% 8); t3 `<<<` 8 * (_at %% 8)] base _st _at _off n 0 _st _ _at 0 n 0 (base + 8) (base + 8) (8 - _at %% 8) (_upto - (base + 8)) 0) => //.
  + smt().
  + smt().
  + move=> k Hk'; rewrite (st4x_get_xor64x4_at _st base) //; smt().
  + by rewrite forall4 /=.
have Emin : min n (base + 8 - _at) = n by smt().
move: M0 M1 M2 M3; rewrite Emin (: _at + n = _upto) 1:/# (: 0 + n = min 8 (max 0 (_upto - _at))) 1:/# (: n - n = 0) 1:/# => M0 M1 M2 M3.
exists (base + 8); split; first smt().
apply (addstate_spec4_asubread _buf0 _buf1 _buf2 _buf3 [t0 `<<<` 8 * (_at %% 8); t1 `<<<` 8 * (_at %% 8); t2 `<<<` 8 * (_at %% 8); t3 `<<<` 8 * (_at %% 8)] base _st _at _off n 0 _st _ _at 0 n 0 (base + 8) _upto (min 8 (max 0 (_upto - _at))) 0 0) => //.
+ smt().
+ smt().
+ move=> k Hk'; rewrite (st4x_get_xor64x4_at _st base) //; smt().
by rewrite forall4 /=.
seq 3 : (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf0 _off n; sub _buf1 _off n; sub _buf2 _off n; sub _buf3 _off n] 0 sz _off off st at (_upto - at) 0).
+ while (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ newat = at + 8
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf0 _off n; sub _buf1 _off n; sub _buf2 _off n; sub _buf3 _off n] 0 sz _off off st at (_upto - at) 0); last by auto => /#.
  auto => &hr [#] -> -> -> -> -> H0 H1 H2 H3 H4 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 5!(split; first smt()).
  exists (sz + 8); split; first smt().
  rewrite (: _upto - (at{hr} + 8) = _upto - at{hr} - 8) 1:/#.
  apply (addstate_spec4_fullword _buf0 _buf1 _buf2 _buf3 [get64_direct (WA.init8 ("_.[_]" _buf0)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf1)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf2)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf3)) off{hr}] sz _st _at _off n 0 st{hr} _ off{hr} at{hr} (_upto - at{hr}) 0) => //.
  + smt().
  + smt().
  + move=> k Hk'; rewrite (st4x_get_xor64x4_at st{hr} at{hr}) //; smt().
  + by rewrite forall4.
if; last first.
+ auto => &hr [#] _ _ _ _ -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  by apply (addstate_spec4_done _buf0 _buf1 _buf2 _buf3 sz _st _at _off n 0 st{hr} off{hr} _upto 0) => //; smt().
wp; ecall (a_rlen_read_upto8_h buf3 off (W64.to_uint upto8)); wp; ecall (a_rlen_read_upto8_h buf2 off (W64.to_uint upto8)).
wp; ecall (a_rlen_read_upto8_h buf1 off (W64.to_uint upto8)); wp; ecall (a_rlen_read_upto8_h buf0 off (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> -> -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
move: (IH 0 _) => //= IH0.
have [_ [Ec1 Ec2]] := addstate_spec_sub_rem (st4x_get _st 0) _at _buf0 _off n 0 sz off{hr} (st4x_get st{hr} 0) at{hr} (_upto - at{hr}) 0 H3 _ _ IH0; 1,2: smt().
split; first smt(). move=> _ [o0 t0] /= [Hs0 Ho0].
split; first smt(). move=> _ [o1 t1] /= [Hs1 Ho1].
split; first smt(). move=> _ [o2 t2] /= [Hs2 Ho2].
split; first smt(). move=> _ [o3 t3] /= [Hs3 ->].
have M0 := asubread_rlen _buf0 t0 at{hr} at{hr} off{hr} 0 (_upto - at{hr}) _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M1 := asubread_rlen _buf1 t1 at{hr} at{hr} off{hr} 0 (_upto - at{hr}) _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M2 := asubread_rlen _buf2 t2 at{hr} at{hr} off{hr} 0 (_upto - at{hr}) _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
have M3 := asubread_rlen _buf3 t3 at{hr} at{hr} off{hr} 0 (_upto - at{hr}) _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
move: M0 M1 M2 M3; rewrite (: 8 * (at{hr} - at{hr}) = 0) 1:/# !u64_shl0 (: min (_upto - at{hr}) (at{hr} + 8 - at{hr}) = _upto - at{hr}) 1:/# (: at{hr} + (_upto - at{hr}) = _upto) 1:/# (: 0 + (_upto - at{hr}) = min 8 (max 0 (_upto - at{hr}))) 1:/# (: _upto - at{hr} - (_upto - at{hr}) = 0) 1:/# => M0 M1 M2 M3.
apply (addstate_spec4_finish _buf0 _buf1 _buf2 _buf3 [t0; t1; t2; t3] sz _st _at _off n 0 st{hr} _ off{hr} at{hr} (_upto - at{hr}) 0 _upto (min 8 (max 0 (_upto - at{hr}))) 0 0) => //.
+ smt().
+ smt().
+ smt().
+ move=> k Hk'; rewrite (st4x_get_xor64x4_at st{hr} at{hr}) //; smt().
by rewrite forall4 /=.
qed.

phoare add_updstate_avx2x4_ph _st _at _buf0 _buf1 _buf2 _buf3 _off _upto:
 [ MM._add_updstate_avx2x4
 : st = _st /\ at = _at /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> addstate_res4 _st _at [_buf0; _buf1; _buf2; _buf3] _off (_upto - _at) 0 res.`1 res.`2 res.`3
 ] = 1%r.
proof. by conseq add_updstate_avx2x4_ll (add_updstate_avx2x4_h _st _at _buf0 _buf1 _buf2 _buf3 _off _upto). qed.

lemma add_bcast_updstate_avx2x4_ll: islossless MM._add_bcast_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_bcast_updstate_avx2x4_h _st _at _buf _off _upto:
 MM._add_bcast_updstate_avx2x4
 : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> addstate_res4 _st _at [_buf; _buf; _buf; _buf] _off (_upto - _at) 0 res.`1 res.`2 res.`3.
proof.
proc => /=; pose n := _upto - _at.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 H3 H4; rewrite and7_mod8 /#.
seq 1 : (buf = _buf /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf _off n; sub _buf _off n; sub _buf _off n; sub _buf _off n] 0 sz _off off st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 H3 H4 Hk; split; first smt().
    exists _at; split => //; apply addstate_spec4_init => //.
    by move=> k Hk'; rewrite nth4_const // A.size_sub /#.
  wp; ecall (a_rlen_read_upto8_h buf off len).
  wp; skip => /> &hr H0 H1 H2 H3 H4 Hk Hnz.
have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
move=> _ [o0 t0] /= Hs0 ->.
have Esh : forall (w: W64.t), w `<<` W8.of_int (8 * (_at %% 8)) = w `<<<` 8 * (_at %% 8) by move=> w; rewrite W64.shl_shlw /#.
rewrite Esh truncateu64_VMOV_64.
pose base := 8 * (_at %/ 8).
have Hb : _at - base = _at %% 8 by smt().
have M0 := asubread_rlen _buf t0 base _at _off 0 n _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
move: M0; rewrite Hb => M0.
have S0 : addstate_spec4 _st _at [sub _buf _off n; sub _buf _off n; sub _buf _off n; sub _buf _off n] 0 base _off (_off + 0) _st _at n 0.
+ rewrite addz0; apply addstate_spec4_init; first smt().
  by move=> k Hk'; rewrite nth4_const // A.size_sub /#.
split => Hc.
+ have Emin : min n (base + 8 - _at) = base + 8 - _at by smt().
  move: M0; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: 0 + (base + 8 - _at) = 8 - _at %% 8) 1:/# (: n - (base + 8 - _at) = _upto - (base + 8)) 1:/# => M0.
  do 2!(split; first smt()).
  exists (base + 8); split; first smt().
  rewrite (: _off + 8 - _at %% 8 = _off + (8 - _at %% 8)) 1:/#.
  apply (addstate_spec4_asubread _buf _buf _buf _buf [t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8)] base _st _at _off n 0 _st _ _at 0 n 0 (base + 8) (base + 8) (8 - _at %% 8) (_upto - (base + 8)) 0) => //.
  + smt().
  + smt().
  + by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 _st _ (_at %/ 8)) 1..3:/#.
  + by move=> k Hk'; rewrite !nth4_const.
have Emin : min n (base + 8 - _at) = n by smt().
move: M0; rewrite Emin (: _at + n = _upto) 1:/# (: 0 + n = min 8 (max 0 (_upto - _at))) 1:/# (: n - n = 0) 1:/# => M0.
exists (base + 8); split; first smt().
apply (addstate_spec4_asubread _buf _buf _buf _buf [t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8); t0 `<<<` 8 * (_at %% 8)] base _st _at _off n 0 _st _ _at 0 n 0 (base + 8) _upto (min 8 (max 0 (_upto - _at))) 0 0) => //.
+ smt().
+ smt().
+ by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 _st _ (_at %/ 8)) 1..3:/#.
by move=> k Hk'; rewrite !nth4_const.
seq 3 : (buf = _buf /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf _off n; sub _buf _off n; sub _buf _off n; sub _buf _off n] 0 sz _off off st at (_upto - at) 0).
+ while (buf = _buf /\ upto = _upto
         /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ newat = at + 8
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec4 _st _at [sub _buf _off n; sub _buf _off n; sub _buf _off n; sub _buf _off n] 0 sz _off off st at (_upto - at) 0); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 H3 H4 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 5!(split; first smt()).
  exists (sz + 8); split; first smt().
  rewrite (: _upto - (at{hr} + 8) = _upto - at{hr} - 8) 1:/#.
  apply (addstate_spec4_fullword _buf _buf _buf _buf [get64_direct (WA.init8 ("_.[_]" _buf)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf)) off{hr}; get64_direct (WA.init8 ("_.[_]" _buf)) off{hr}] sz _st _at _off n 0 st{hr} _ off{hr} at{hr} (_upto - at{hr}) 0) => //.
  + smt().
  + smt().
  + by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 st{hr} _ (at{hr} %/ 8)) 1..3:/# (: 8 * (at{hr} %/ 8) = at{hr}) 1:/#.
  + by rewrite forall4.
if; last first.
+ auto => &hr [#] _ -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  by apply (addstate_spec4_done _buf _buf _buf _buf sz _st _at _off n 0 st{hr} off{hr} _upto 0) => //; smt().
wp; ecall (a_rlen_read_upto8_h buf off (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
move: (IH 0 _) => //= IH0.
have [_ [Ec1 Ec2]] := addstate_spec_sub_rem (st4x_get _st 0) _at _buf _off n 0 sz off{hr} (st4x_get st{hr} 0) at{hr} (_upto - at{hr}) 0 H3 _ _ IH0; 1,2: smt().
split; first smt(). move=> _ [o0 t0] /= [Hs0 ->].
rewrite truncateu64_VMOV_64.
have M0 := asubread_rlen _buf t0 at{hr} at{hr} off{hr} 0 (_upto - at{hr}) _ _ _; 1,2: smt(). by move=> _; rewrite addz0.
move: M0; rewrite (: 8 * (at{hr} - at{hr}) = 0) 1:/# u64_shl0 (: min (_upto - at{hr}) (at{hr} + 8 - at{hr}) = _upto - at{hr}) 1:/# (: at{hr} + (_upto - at{hr}) = _upto) 1:/# (: 0 + (_upto - at{hr}) = min 8 (max 0 (_upto - at{hr}))) 1:/# (: _upto - at{hr} - (_upto - at{hr}) = 0) 1:/# => M0.
apply (addstate_spec4_finish _buf _buf _buf _buf [t0; t0; t0; t0] sz _st _at _off n 0 st{hr} _ off{hr} at{hr} (_upto - at{hr}) 0 _upto (min 8 (max 0 (_upto - at{hr}))) 0 0) => //.
+ smt().
+ smt().
+ smt().
+ by move=> k Hk'; rewrite nth4_const // (st4x_get_xorbcast256 st{hr} _ (at{hr} %/ 8)) 1..3:/# (: 8 * (at{hr} %/ 8) = at{hr}) 1:/#.
by move=> k Hk'; rewrite !nth4_const.
qed.

phoare add_bcast_updstate_avx2x4_ph _st _at _buf _off _upto:
 [ MM._add_bcast_updstate_avx2x4
 : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> addstate_res4 _st _at [_buf; _buf; _buf; _buf] _off (_upto - _at) 0 res.`1 res.`2 res.`3
 ] = 1%r.
proof. by conseq add_bcast_updstate_avx2x4_ll (add_bcast_updstate_avx2x4_h _st _at _buf _off _upto). qed.


(* ---- absorb ---- *)

lemma absorb_updstate_avx2x4_ll: islossless MM._absorb_updstate_avx2x4.
proof.
proc; seq 6: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_avx2x4_ll; call add_updstate_avx2x4_ll; auto => /#.
  by wp; call add_updstate_avx2x4_ll; auto.
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare absorb_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 MM._absorb_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf0 0 _len) (_l1 ++ sub _buf1 0 _len)
                             (_l2 ++ sub _buf2 0 _len) (_l3 ++ sub _buf3 0 _len) res.
proof.
proc => /=; exlim st => _st.
seq 6 : (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE
         /\ r8 = _r8 /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ off = 0 /\ stk = A101u64toA25u256 _st /\ at = size _l0 %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> -> -> -> Habs H0 H1 r [-> ->] /=.
  have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp Er8 Etb Hat.
  rewrite Hp Er8 Etb Hat /=; split; [smt() | by rewrite /A101u64toA25u256].
seq 1 : (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8
         /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ 0 <= off <= _len /\ at = (size _l0 + off) %% _r8
         /\ len = _len - off + at /\ len < r8
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [sub _buf0 0 _len; sub _buf1 0 _len; sub _buf2 0 _len; sub _buf3 0 _len] off stk).
+ while (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8
         /\ buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ 0 <= off <= _len /\ at = (size _l0 + off) %% _r8
         /\ len = _len - off + at
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [sub _buf0 0 _len; sub _buf1 0 _len; sub _buf2 0 _len; sub _buf3 0 _len] off stk).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (add_updstate_avx2x4_h stk at buf0 buf1 buf2 buf3 off r8).
    auto => &hr [#] -> Habs H0 H1 -> -> -> -> -> Hb0 Hb1 -> -> Hp Hc.
    have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
    pose k := off{hr}.
    pose a := (size _l0 + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ [stc at1 c1] /= Hres r -> /=.
    have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
    have Hl := addstate_res4_sub stk{hr} stc a _buf0 _buf1 _buf2 _buf3 _len k (_r8 - a) at1 c1 _ _ _ _ Hres; 1..4: smt().
    have Hf := pabsorb4_fill _r8 (size _l0) [_l0; _l1; _l2; _l3] (sub _buf0 0 _len) (sub _buf1 0 _len) (sub _buf2 0 _len) (sub _buf3 0 _len) k (_r8 - a) a stk{hr} stc _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt(A.size_sub).
    have [_ [_ Ec1]] := Hres.
    rewrite Ec1 /=.
    do 3!(split; first smt()).
    split; first by rewrite (absorb_block_arith (size _l0) k _r8 a) /#.
    split; first smt().
    exact Hf.
  auto => &hr [#] -> Habs H0 H1 -> -> -> -> -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by apply pabsorb4_init.
wp; ecall (add_updstate_avx2x4_h stk at buf0 buf1 buf2 buf3 off len); wp; skip => &hr [#] -> Habs H0 H1 -> -> -> -> -> Hb0 Hb1 -> -> Hc Hp /=.
split; first smt().
move=> _ [stc at1 c1] /= Hres.
rewrite A25u256toA101u64E A101_set800.
have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
pose k := off{hr}.
pose a := (size _l0 + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
have Hsz : forall (b: W8.t A.t), size (sub b 0 _len) = _len by move=> b; rewrite A.size_sub /#.
move: Hres; rewrite (: _len - k + a - a = _len - k) 1:/# => Hres.
have Hl := addstate_res4_sub stk{hr} stc a _buf0 _buf1 _buf2 _buf3 _len k (_len - k) at1 c1 _ _ _ _ Hres; 1..4: smt().
have [_ HL] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (sub _buf0 0 _len) (sub _buf1 0 _len) (sub _buf2 0 _len) (sub _buf3 0 _len) k (_len - k) a stk{hr} stc 0 _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt().
have HL0 := HL _; first done.
have [_ [Eat1 _]] := Hres.
have [Hat2 [Hr2 Htb2]] := ststatus_set_atP _st.[100] at1 _; first smt().
have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp0 Hr0 Htb0 Hat0.
rewrite /absorbing_spec4 A101u64toA25u256K A25u256toA101u64_100; split.
+ have := Hp0; rewrite !pabsorb_spec_avx2x4E !size_cat !Hsz => [#] S1 S2 S3 _.
  rewrite S1 S2 S3 /=.
  move=> j Hj; have := HL0 j Hj.
  have: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  by case => [->|[->|[->|->]]].
have Hl2 := absorb_last_arith (size _l0) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat Hsz.
rewrite (: size _l0 + _len = size _l0 + (k + (_len - k))) 1:/# Hl2.
smt().
qed.

phoare absorb_updstate_avx2x4_ph _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 [ MM._absorb_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf0 0 _len) (_l1 ++ sub _buf1 0 _len)
                             (_l2 ++ sub _buf2 0 _len) (_l3 ++ sub _buf3 0 _len) res
 ] = 1%r.
proof. by conseq absorb_updstate_avx2x4_ll (absorb_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len). qed.

lemma absorb_bcast_updstate_avx2x4_ll: islossless MM._absorb_bcast_updstate_avx2x4.
proof.
proc; seq 6: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_avx2x4_ll; call add_bcast_updstate_avx2x4_ll; auto => /#.
  by wp; call add_bcast_updstate_avx2x4_ll; auto.
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare absorb_bcast_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 MM._absorb_bcast_updstate_avx2x4
 : buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf 0 _len) (_l1 ++ sub _buf 0 _len)
                             (_l2 ++ sub _buf 0 _len) (_l3 ++ sub _buf 0 _len) res.
proof.
proc => /=; exlim st => _st.
seq 6 : (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE
         /\ r8 = _r8 /\ buf = _buf
         /\ off = 0 /\ stk = A101u64toA25u256 _st /\ at = size _l0 %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> Habs H0 H1 r [-> ->] /=.
  have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp Er8 Etb Hat.
  rewrite Hp Er8 Etb Hat /=; split; [smt() | by rewrite /A101u64toA25u256].
seq 1 : (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8
         /\ buf = _buf
         /\ 0 <= off <= _len /\ at = (size _l0 + off) %% _r8
         /\ len = _len - off + at /\ len < r8
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [sub _buf 0 _len; sub _buf 0 _len; sub _buf 0 _len; sub _buf 0 _len] off stk).
+ while (st = _st /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8
         /\ buf = _buf
         /\ 0 <= off <= _len /\ at = (size _l0 + off) %% _r8
         /\ len = _len - off + at
         /\ pabsorb4 _r8 [_l0; _l1; _l2; _l3] [sub _buf 0 _len; sub _buf 0 _len; sub _buf 0 _len; sub _buf 0 _len] off stk).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (add_bcast_updstate_avx2x4_h stk at buf off r8).
    auto => &hr [#] -> Habs H0 H1 -> -> Hb0 Hb1 -> -> Hp Hc.
    have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
    pose k := off{hr}.
    pose a := (size _l0 + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ [stc at1 c1] /= Hres r -> /=.
    have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
    have Hl := addstate_res4_sub stk{hr} stc a _buf _buf _buf _buf _len k (_r8 - a) at1 c1 _ _ _ _ Hres; 1..4: smt().
    have Hf := pabsorb4_fill _r8 (size _l0) [_l0; _l1; _l2; _l3] (sub _buf 0 _len) (sub _buf 0 _len) (sub _buf 0 _len) (sub _buf 0 _len) k (_r8 - a) a stk{hr} stc _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt(A.size_sub).
    have [_ [_ Ec1]] := Hres.
    rewrite Ec1 /=.
    do 3!(split; first smt()).
    split; first by rewrite (absorb_block_arith (size _l0) k _r8 a) /#.
    split; first smt().
    exact Hf.
  auto => &hr [#] -> Habs H0 H1 -> -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by apply pabsorb4_init.
wp; ecall (add_bcast_updstate_avx2x4_h stk at buf off len); wp; skip => &hr [#] -> Habs H0 H1 -> -> Hb0 Hb1 -> -> Hc Hp /=.
split; first smt().
move=> _ [stc at1 c1] /= Hres.
rewrite A25u256toA101u64E A101_set800.
have Hr8 := pabsorb4_r8 _ _ _ _ _ Hp.
pose k := off{hr}.
pose a := (size _l0 + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Hs := absorbing_spec4_sizes _ _ _ _ _ _ _ Habs.
have Hsz : forall (b: W8.t A.t), size (sub b 0 _len) = _len by move=> b; rewrite A.size_sub /#.
move: Hres; rewrite (: _len - k + a - a = _len - k) 1:/# => Hres.
have Hl := addstate_res4_sub stk{hr} stc a _buf _buf _buf _buf _len k (_len - k) at1 c1 _ _ _ _ Hres; 1..4: smt().
have [_ HL] := pabsorb4_last _r8 (size _l0) [_l0; _l1; _l2; _l3] (sub _buf 0 _len) (sub _buf 0 _len) (sub _buf 0 _len) (sub _buf 0 _len) k (_len - k) a stk{hr} stc 0 _ _ _ _ _ _ _ Hs Hp Hl; 1..7: smt().
have HL0 := HL _; first done.
have [_ [Eat1 _]] := Hres.
have [Hat2 [Hr2 Htb2]] := ststatus_set_atP _st.[100] at1 _; first smt().
have := Habs; rewrite /absorbing_spec4 /status_spec => [#] Hp0 Hr0 Htb0 Hat0.
rewrite /absorbing_spec4 A101u64toA25u256K A25u256toA101u64_100; split.
+ have := Hp0; rewrite !pabsorb_spec_avx2x4E !size_cat !Hsz => [#] S1 S2 S3 _.
  rewrite S1 S2 S3 /=.
  move=> j Hj; have := HL0 j Hj.
  have: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  by case => [->|[->|[->|->]]].
have Hl2 := absorb_last_arith (size _l0) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat Hsz.
rewrite (: size _l0 + _len = size _l0 + (k + (_len - k))) 1:/# Hl2.
smt().
qed.

phoare absorb_bcast_updstate_avx2x4_ph _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 [ MM._absorb_bcast_updstate_avx2x4
 : buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf 0 _len) (_l1 ++ sub _buf 0 _len)
                             (_l2 ++ sub _buf 0 _len) (_l3 ++ sub _buf 0 _len) res
 ] = 1%r.
proof. by conseq absorb_bcast_updstate_avx2x4_ll (absorb_bcast_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf _len). qed.


(* ---- dump ---- *)

lemma dump_updstate_avx2x4_ll: islossless MM._dump_updstate_avx2x4.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare dump_updstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _st _at _upto:
 MM._dump_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res.`1 = afill _buf0 _off (sub (stbytes (st4x_get _st 0)) _at (_upto - _at))
   /\ res.`2 = afill _buf1 _off (sub (stbytes (st4x_get _st 1)) _at (_upto - _at))
   /\ res.`3 = afill _buf2 _off (sub (stbytes (st4x_get _st 2)) _at (_upto - _at))
   /\ res.`4 = afill _buf3 _off (sub (stbytes (st4x_get _st 3)) _at (_upto - _at))
   /\ res.`5 = _off + (_upto - _at) /\ res.`6 = _upto.
proof.
proc => /=.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 H3 H4; rewrite and7_mod8 /#.
seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ buf0 = afill _buf0 _off (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z)
            /\ buf1 = afill _buf1 _off (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
            /\ buf2 = afill _buf2 _off (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z)
            /\ buf3 = afill _buf3 _off (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)).
+ if; last first.
  + auto => /> H0 H1 H2 H3 H4 Hk; split; first smt().
    by exists 0; rewrite !sub200_nil nseq0 /= !afill_nil /#.
  wp; ecall (a_rlen_write_upto8_h buf3 off t64 len); wp; ecall (a_rlen_write_upto8_h buf2 off t64 len).
  wp; ecall (a_rlen_write_upto8_h buf1 off t64 len); wp; ecall (a_rlen_write_upto8_h buf0 off t64 len).
  wp; skip => /> &hr H0 H1 H2 H3 H4 Hk Hnz.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#.
  split; first smt().
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 0 (4 * (8 * (_at %/ 8)))) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 1 (4 * (8 * (_at %/ 8)) + 8)) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 2 (4 * (8 * (_at %/ 8)) + 16)) 1..4:/#.
  rewrite (st4x_get64_at _st (8 * (_at %/ 8)) 3 (4 * (8 * (_at %/ 8)) + 24)) 1..4:/#.
  rewrite (dump_lane_first _ _buf0 _off _at (_upto - _at)) 1..4:/#.
  rewrite (dump_lane_first _ _buf1 _off _at (_upto - _at)) 1..4:/#.
  rewrite (dump_lane_first _ _buf2 _off _at (_upto - _at)) 1..4:/#.
  rewrite (dump_lane_first _ _buf3 _off _at (_upto - _at)) 1..4:/#.
  move=> _ [b0 o0] /= -> _ [b1 o1] /= -> _ [b2 o2] /= -> _ [b3 o3] /= -> ->.
  split => Hc.
  + do 3!(split; first smt()).
    exists (min (_upto - _at - min (_upto - _at) (8 - _at %% 8)) (_at %% 8)).
    rewrite (: 8 * (_at %/ 8) + 8 - _at = min (_upto - _at) (8 - _at %% 8)) 1:/#.
    by do 2!(split; first smt()).
  split; first smt().
  exists 0; rewrite (: min (_upto - _at) (8 - _at %% 8) = _upto - _at) 1:/# (: min (_upto - _at - (_upto - _at)) (_at %% 8) = 0) 1:/#.
  done.
seq 3 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 8
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ buf0 = afill _buf0 _off (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z)
            /\ buf1 = afill _buf1 _off (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
            /\ buf2 = afill _buf2 _off (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z)
            /\ buf3 = afill _buf3 _off (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)).
+ while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ newat = at + 8
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ buf0 = afill _buf0 _off (sub (stbytes (st4x_get _st 0)) _at (at - _at) ++ u8zeros z)
            /\ buf1 = afill _buf1 _off (sub (stbytes (st4x_get _st 1)) _at (at - _at) ++ u8zeros z)
            /\ buf2 = afill _buf2 _off (sub (stbytes (st4x_get _st 2)) _at (at - _at) ++ u8zeros z)
            /\ buf3 = afill _buf3 _off (sub (stbytes (st4x_get _st 3)) _at (at - _at) ++ u8zeros z)); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> -> [z [Hz [Hzl [-> [-> [-> ->]]]]]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  rewrite (st4x_get64_at _st at{hr} 0 (4 * at{hr})) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 1 (4 * at{hr} + 8)) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 2 (4 * at{hr} + 16)) 1..4:/#.
  rewrite (st4x_get64_at _st at{hr} 3 (4 * at{hr} + 24)) 1..4:/#.
  rewrite (dump_lane_step8 _ _buf0 _off _at at{hr} z) 1..3:/#.
  rewrite (dump_lane_step8 _ _buf1 _off _at at{hr} z) 1..3:/#.
  rewrite (dump_lane_step8 _ _buf2 _off _at at{hr} z) 1..3:/#.
  rewrite (dump_lane_step8 _ _buf3 _off _at at{hr} z) 1..3:/#.
  do 6!(split; first smt()).
  by exists 0; do 2!(split; first smt()).
if; last first.
+ auto => &hr [#] _ -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl [-> [-> [-> ->]]]]]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  have Ez : z = 0 by smt().
  by rewrite Ea Ez nseq0 !cats0.
wp; ecall (a_rlen_write_upto8_h buf3 off t64 (W64.to_uint upto8)); wp; ecall (a_rlen_write_upto8_h buf2 off t64 (W64.to_uint upto8)).
wp; ecall (a_rlen_write_upto8_h buf1 off t64 (W64.to_uint upto8)); wp; ecall (a_rlen_write_upto8_h buf0 off t64 (W64.to_uint upto8)).
wp; skip => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl [-> [-> [-> ->]]]]]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu.
rewrite (st4x_get64_at _st at{hr} 0 (4 * at{hr})) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 1 (4 * at{hr} + 8)) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 2 (4 * at{hr} + 16)) 1..4:/#.
rewrite (st4x_get64_at _st at{hr} 3 (4 * at{hr} + 24)) 1..4:/#.
rewrite (dump_lane_last _ _buf0 _off _at at{hr} _upto z) 1..4:/#.
rewrite (dump_lane_last _ _buf1 _off _at at{hr} _upto z) 1..4:/#.
rewrite (dump_lane_last _ _buf2 _off _at at{hr} _upto z) 1..4:/#.
rewrite (dump_lane_last _ _buf3 _off _at at{hr} _upto z) 1..4:/#.
split; first smt().
move=> _ [b0 o0] /= [-> _].
split; first smt(). move=> _ [b1 o1] /= [-> _].
split; first smt(). move=> _ [b2 o2] /= [-> _].
split; first smt(). move=> _ [b3 o3] /= [-> ->].
smt().
qed.

phoare dump_updstate_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _off _st _at _upto:
 [ MM._dump_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
   /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res.`1 = afill _buf0 _off (sub (stbytes (st4x_get _st 0)) _at (_upto - _at))
   /\ res.`2 = afill _buf1 _off (sub (stbytes (st4x_get _st 1)) _at (_upto - _at))
   /\ res.`3 = afill _buf2 _off (sub (stbytes (st4x_get _st 2)) _at (_upto - _at))
   /\ res.`4 = afill _buf3 _off (sub (stbytes (st4x_get _st 3)) _at (_upto - _at))
   /\ res.`5 = _off + (_upto - _at) /\ res.`6 = _upto
 ] = 1%r.
proof. by conseq dump_updstate_avx2x4_ll (dump_updstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _st _at _upto). qed.


(* ---- squeeze ---- *)

lemma squeeze_updstate_avx2x4_ll: islossless MM._squeeze_updstate_avx2x4.
proof.
proc; seq 4: (8 <= r8).
+ by wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
+ by wp; call ststatus_data_avx2x4_bnd_ph; auto.
+ seq 3: (8 <= r8) => //.
  + by wp; if; [wp; call keccakf1600_avx2x4_ll; auto | auto].
  + seq 1: true => //.
    + while (8 <= r8) len => [z|]; last by auto => /#.
      by wp; call keccakf1600_avx2x4_ll; call dump_updstate_avx2x4_ll; auto => /#.
    by wp; call dump_updstate_avx2x4_ll; auto.
  by hoare; wp; if; [wp; ecall (keccakf1600_avx2x4_h stk); auto | auto].
+ by hoare; wp; ecall (ststatus_data_avx2x4_bnd_h); auto.
by [].
qed.

hoare squeeze_updstate_avx2x4_h _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 MM._squeeze_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 0) _k _len).[i]) 0 _len _buf0
   /\ res.`3 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 1) _k _len).[i]) 0 _len _buf1
   /\ res.`4 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 2) _k _len).[i]) 0 _len _buf2
   /\ res.`5 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 3) _k _len).[i]) 0 _len _buf3
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res.`1.
proof.
proc => /=; exlim st => _st.
seq 4 : (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len <= _ASIZE
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ stk = iter ((_k - 1) %/ _r8 + 1) keccak_f1600_x4 _s0).
+ wp; ecall (ststatus_data_avx2x4_h st.[100]); auto => &hr [#] <- -> -> -> -> -> Hsq H0 H1 r [-> ->] /=.
  have := Hsq; rewrite /squeezing_spec4 => [#] Hr0 Hr1 Hk Est Er8 Eat.
  rewrite Er8 Eat /= -Est.
  by rewrite /A101u64toA25u256 /=; smt().
seq 3 : (buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len <= _ASIZE
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ off = 0 /\ len = _len + at /\ stk = iter (_k %/ _r8 + 1) keccak_f1600_x4 _s0).
+ wp; if.
  + wp; ecall (keccakf1600_avx2x4_h stk); auto => &hr [#] -> -> -> -> -> Hsq H0 H1 -> -> Hat -> Hz.
    have [Hr [Hk _]] := Hsq.
    move=> r ->; do !(split; first smt()).
    rewrite -(squeeze_entry0 _r8 _k) 1,2:/# (iterS ((_k - 1) %/ _r8 + 1)); first by apply (squeeze_entry_ge0 _r8 _k) => /#.
    by rewrite /keccak_f1600_x4.
  auto => &hr [#] -> -> -> -> -> Hsq H0 H1 -> -> Hat -> Hz.
  have [Hr [Hk _]] := Hsq.
  by rewrite (squeeze_entry1 _r8 _k) 1,2:/#.
seq 1 : (buf0 = afill _buf0 0 (sqstream _r8 (st4x_get _s0 0) _k off)
         /\ buf1 = afill _buf1 0 (sqstream _r8 (st4x_get _s0 1) _k off)
         /\ buf2 = afill _buf2 0 (sqstream _r8 (st4x_get _s0 2) _k off)
         /\ buf3 = afill _buf3 0 (sqstream _r8 (st4x_get _s0 3) _k off)
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len <= _ASIZE /\ st = _st /\ r8 = _r8
         /\ stk = iter ((_k + off) %/ _r8 + 1) keccak_f1600_x4 _s0 /\ at = (_k + off) %% _r8
         /\ len = at + (_len - off) /\ 0 <= off < _len /\ len <= r8).
+ while (buf0 = afill _buf0 0 (sqstream _r8 (st4x_get _s0 0) _k off)
         /\ buf1 = afill _buf1 0 (sqstream _r8 (st4x_get _s0 1) _k off)
         /\ buf2 = afill _buf2 0 (sqstream _r8 (st4x_get _s0 2) _k off)
         /\ buf3 = afill _buf3 0 (sqstream _r8 (st4x_get _s0 3) _k off)
         /\ squeezing_spec4 _r8 _s0 _k _st /\ 0 < _len <= _ASIZE /\ st = _st /\ r8 = _r8
         /\ stk = iter ((_k + off) %/ _r8 + 1) keccak_f1600_x4 _s0 /\ at = (_k + off) %% _r8
         /\ len = at + (_len - off) /\ 0 <= off < _len).
  + wp; ecall (keccakf1600_avx2x4_h stk); ecall (dump_updstate_avx2x4_h buf0 buf1 buf2 buf3 off stk at r8).
    auto => &hr [#] -> -> -> -> Hsq H0 H1 -> -> -> -> -> Hw0 Hw1 Hc.
    have [Hr [Hk _]] := Hsq.
    have Ha : 0 <= (_k + off{hr}) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ [b0 b1 b2 b3 off1 at1] /= [-> [-> [-> [-> [-> _]]]]] r -> /=.
    have G : forall j, 0 <= j < 4 => st4x_get (iter ((_k + off{hr}) %/ _r8 + 1) keccak_f1600_x4 _s0) j = st_i (st4x_get _s0 j) ((_k + off{hr}) %/ _r8 + 1).
    + by move=> j Hj; apply st4x_get_iter => //; smt(divz_ge0).
    rewrite (G 0) // (G 1) // (G 2) // (G 3) //.
    rewrite (afill_sqstream_step _r8 (st4x_get _s0 0) _k off{hr} (_r8 - (_k + off{hr}) %% _r8) _buf0) 1..5:/#.
    rewrite (afill_sqstream_step _r8 (st4x_get _s0 1) _k off{hr} (_r8 - (_k + off{hr}) %% _r8) _buf1) 1..5:/#.
    rewrite (afill_sqstream_step _r8 (st4x_get _s0 2) _k off{hr} (_r8 - (_k + off{hr}) %% _r8) _buf2) 1..5:/#.
    rewrite (afill_sqstream_step _r8 (st4x_get _s0 3) _k off{hr} (_r8 - (_k + off{hr}) %% _r8) _buf3) 1..5:/#.
    have [Hp0 Hp1] := squeeze_pos_arith _r8 (_k + off{hr}) ((_k + off{hr}) %% _r8) _ _; 1,2: smt().
    rewrite (: _k + (off{hr} + (_r8 - (_k + off{hr}) %% _r8)) = _k + off{hr} + (_r8 - (_k + off{hr}) %% _r8)) 1:/# Hp0 Hp1.
    do 4!(split; first done).
    split; first exact Hsq.
    split; first smt().
    split; first by rewrite (iterS ((_k + off{hr}) %/ _r8 + 1)); [smt(divz_ge0) | rewrite /keccak_f1600_x4].
    smt().
  auto => &hr [#] -> -> -> -> Hsq H0 H1 -> -> -> -> -> -> /=.
  have [Hr [Hk _]] := Hsq.
  split; last by smt().
  have E0 : forall j, sqstream _r8 (st4x_get _s0 j) _k 0 = [] by move=> j; rewrite -size_eq0 size_sqstream.
  by rewrite !E0 !afill_nil /#.
wp; ecall (dump_updstate_avx2x4_h buf0 buf1 buf2 buf3 off stk at len); wp; skip => &hr [#] -> -> -> -> Hsq H0 H1 -> -> -> -> -> Hw0 Hw1 Hle /=.
have [Hr [Hk _]] := Hsq.
have Ha : 0 <= (_k + off{hr}) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
split; first smt().
move=> _ [b0 b1 b2 b3 off1 at1] /= [-> [-> [-> [-> [_ ->]]]]].
rewrite A25u256toA101u64E A101_set800.
rewrite (: (_k + off{hr}) %% _r8 + (_len - off{hr}) - (_k + off{hr}) %% _r8 = _len - off{hr}) 1:/#.
have G : forall j, 0 <= j < 4 => st4x_get (iter ((_k + off{hr}) %/ _r8 + 1) keccak_f1600_x4 _s0) j = st_i (st4x_get _s0 j) ((_k + off{hr}) %/ _r8 + 1).
+ by move=> j Hj; apply st4x_get_iter => //; smt(divz_ge0).
rewrite (G 0) // (G 1) // (G 2) // (G 3) //.
rewrite (afill_sqstream_step _r8 (st4x_get _s0 0) _k off{hr} (_len - off{hr}) _buf0) 1..5:/#.
rewrite (afill_sqstream_step _r8 (st4x_get _s0 1) _k off{hr} (_len - off{hr}) _buf1) 1..5:/#.
rewrite (afill_sqstream_step _r8 (st4x_get _s0 2) _k off{hr} (_len - off{hr}) _buf2) 1..5:/#.
rewrite (afill_sqstream_step _r8 (st4x_get _s0 3) _k off{hr} (_len - off{hr}) _buf3) 1..5:/#.
rewrite (: off{hr} + (_len - off{hr}) = _len) 1:/#.
have AF : forall (b: W8.t A.t) j, afill b 0 (sqstream _r8 (st4x_get _s0 j) _k _len) = A.fill (fun i => (sqstream _r8 (st4x_get _s0 j) _k _len).[i]) 0 _len b.
+ by move=> b j; rewrite /afill size_sqstream 1..3:/#; congr; apply fun_ext => i /=.
rewrite !AF /=.
have [Fq Fm] := squeeze_fin_arith _r8 (_k + off{hr}) ((_k + off{hr}) %% _r8) (_len - off{hr}) _ _ _ _; 1..4: smt().
have [Hat2 [Hr2 _]] := ststatus_set_atP _st.[100] ((_k + off{hr}) %% _r8 + (_len - off{hr})) _; first smt().
have [_ [_ [_ [Hr0 _]]]] := Hsq.
rewrite /squeezing_spec4 A101u64toA25u256K A25u256toA101u64_100 /ststatus_at_norm Hr2 Hr0 Hat2.
rewrite (: _k + _len - 1 = _k + off{hr} + (_len - off{hr}) - 1) 1:/# Fq (: _k + _len = _k + off{hr} + (_len - off{hr})) 1:/# Fm.
smt().
qed.

phoare squeeze_updstate_avx2x4_ph _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 [ MM._squeeze_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 0) _k _len).[i]) 0 _len _buf0
   /\ res.`3 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 1) _k _len).[i]) 0 _len _buf1
   /\ res.`4 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 2) _k _len).[i]) 0 _len _buf2
   /\ res.`5 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 3) _k _len).[i]) 0 _len _buf3
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res.`1
 ] = 1%r.
proof. by conseq squeeze_updstate_avx2x4_ll (squeeze_updstate_avx2x4_h _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len). qed.


(* ---- the exported wrappers ---- *)

lemma absorb_updstate_avx2x4_export_ll: islossless MM.absorb_updstate_avx2x4.
proof. by proc; call absorb_updstate_avx2x4_ll; auto. qed.

hoare absorb_updstate_avx2x4_export_h _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len:
 MM.absorb_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf0 0 _len) (_l1 ++ sub _buf1 0 _len)
                             (_l2 ++ sub _buf2 0 _len) (_l3 ++ sub _buf3 0 _len) res.
proof. by proc; ecall (absorb_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf0 _buf1 _buf2 _buf3 _len); auto. qed.

lemma absorb_bcast_updstate_avx2x4_export_ll: islossless MM.absorb_bcast_updstate_avx2x4.
proof. by proc; call absorb_bcast_updstate_avx2x4_ll; auto. qed.

hoare absorb_bcast_updstate_avx2x4_export_h _r8 _tb _l0 _l1 _l2 _l3 _buf _len:
 MM.absorb_bcast_updstate_avx2x4
 : buf = _buf /\ len = _len
   /\ absorbing_spec4 _r8 _tb _l0 _l1 _l2 _l3 st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec4 _r8 _tb (_l0 ++ sub _buf 0 _len) (_l1 ++ sub _buf 0 _len)
                             (_l2 ++ sub _buf 0 _len) (_l3 ++ sub _buf 0 _len) res.
proof. by proc; ecall (absorb_bcast_updstate_avx2x4_h _r8 _tb _l0 _l1 _l2 _l3 _buf _len); auto. qed.

lemma squeeze_updstate_avx2x4_export_ll: islossless MM.squeeze_updstate_avx2x4.
proof. by proc; call squeeze_updstate_avx2x4_ll; auto. qed.

hoare squeeze_updstate_avx2x4_export_h _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len:
 MM.squeeze_updstate_avx2x4
 : buf0 = _buf0 /\ buf1 = _buf1 /\ buf2 = _buf2 /\ buf3 = _buf3 /\ len = _len
   /\ squeezing_spec4 _r8 _s0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 0) _k _len).[i]) 0 _len _buf0
   /\ res.`3 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 1) _k _len).[i]) 0 _len _buf1
   /\ res.`4 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 2) _k _len).[i]) 0 _len _buf2
   /\ res.`5 = A.fill (fun i => (sqstream _r8 (st4x_get _s0 3) _k _len).[i]) 0 _len _buf3
   /\ squeezing_spec4 _r8 _s0 (_k + _len) res.`1.
proof. by proc; ecall (squeeze_updstate_avx2x4_h _r8 _s0 _k _buf0 _buf1 _buf2 _buf3 _len); auto. qed.

end KeccakUpdstateAvx2x4.

