(******************************************************************************
   Keccak1600_updstate_finish.ec:

   Contracts of the single-lane `_finish_updstate` and of the status export
   `ststatus_updstate` (src/fips202/ref/keccak1600_updstate.jinc), used by
   ref/Keccak1600_updstate_ref.ec.
   (Kept apart from Keccak1600_updstate.ec and from the ref file: the
   low-level finish script is sensitive to the lemmas in scope.)
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.
from Jasmin require import JModel_x86.
from JazzEC require import Keccak1600_Jazz.
from JazzEC require import BArray3 BArray32 BArray40 BArray160 BArray192 BArray200 BArray208 BArray224 BArray800 BArray808 SBArray208_200 SBArray808_800.
require import Keccak1600_barrays.
from JazzEC require import WArray200.
from JazzEC require import Array25.
from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.
require import Keccak1600_statebytes Keccak1600_subreadwrite Keccak1600_updstate.
import IntOrder.
import BitEncoding.BS2Int.

(* ------------------------------------------------------------------------- *)
(* finish                                                                    *)
(* ------------------------------------------------------------------------- *)

lemma finish_updstate_ll: islossless M._finish_updstate by islossless.

(* the byte view of the lanes of a u64[26] *)
lemma stbytes_ust_state st i:
 0 <= i < 200 => (stbytes (ust_state st)).[i] = st.[i].
proof.
move=> Hi; rewrite stbytes_get // ust_stateE 1:/# BArray208.get64d_byte 1:/#.
by rewrite (_: 8 * (i %/ 8) + i %% 8 = i) 1:/#.
qed.

hoare finish_updstate_spec_h _st:
 M._finish_updstate : st = _st ==> res = finish_updstate_spec _st.
proof.
(* byte extensionality: below 200 the two XORs of the lanes, at 200..207 the
   cleared status word (bytes 0 and 2 of the 64-bit mask are 0, the others 0xFF) *)
proc. wp; ecall (ststatus_data_h ststatus); wp; skip => />.
rewrite /finish_updstate_spec !ststatus_data_specE /=.
pose s := get64d _st 200.
have [_ [Hr8a Hr8b]] := ststatus_r8_bounds s.
have [Ha0 Ha1] := ststatus_at_norm_bounds s.
apply BArray208.ext_eq => i Hi.
rewrite BArray208.get8_set32dE BArray208.get8_of_list64 size_cat Array25.size_to_list /=.
case: (i < 200) => Ci.
+ rewrite ifF 1:/# ifT 1:/# nth_cat Array25.size_to_list ifT 1:/#.
  rewrite (nth_change_dfl witness) 1:Array25.size_to_list 1:/# Array25.get_to_list.
  rewrite -stbytes_get 1:/# xor_byte_at_st25E 1:/# stwordsK xor_byte_at_st25E 1:/# stwordsK.
  rewrite !WArray200.get_set_if !BArray208.get_set_if !stbytes_ust_state 1..3:/#.
  smt().
case: (i < 204) => C2.
+ rewrite ifT 1:/# ifT 1:/# nth_cat Array25.size_to_list ifF 1:/# (_: i %/ 8 - 25 = 0) 1:/# /=.
  rewrite /clear_at_trailb /= BArray208.get64d_byte 1:/# (_: 200 + i %% 8 = i) 1:/#.
  rewrite BArray208.get32d_byte 1:/# !BArray208.get_set_if ifF 1:/# ifF 1:/#.
  rewrite (_: 200 + (i - 200) = i) 1:/#; congr.
  have: i = 200 \/ i = 201 \/ i = 202 \/ i = 203 by smt().
  by move=> [->|[->|[->|->]]].
rewrite ifF 1:/# ifT 1:/# nth_cat Array25.size_to_list ifF 1:/# (_: i %/ 8 - 25 = 0) 1:/# /=.
rewrite /clear_at_trailb /= BArray208.get64d_byte 1:/# (_: 200 + i %% 8 = i) 1:/#.
rewrite !BArray208.get_set_if ifF 1:/# ifF 1:/#.
move: (_st.[i]) => x.
have: i = 204 \/ i = 205 \/ i = 206 \/ i = 207 by smt().
by move=> [->|[->|[->|->]]] /=; circuit.
qed.

hoare finish_updstate_h _r8 _tb _l:
 M._finish_updstate
 : absorbing_spec _r8 _tb _l st
 ==> squeezing_spec _r8 (ABSORB1600 _tb _r8 _l) 0 res.
proof.
exlim st => _st.
conseq (finish_updstate_spec_h _st); first by move=> />.
by move=> &hr [#] <- Habs r ->; apply finish_spec_absorbing.
qed.

phoare finish_updstate_ph _r8 _tb _l:
 [ M._finish_updstate
 : absorbing_spec _r8 _tb _l st
 ==> squeezing_spec _r8 (ABSORB1600 _tb _r8 _l) 0 res
 ] = 1%r.
proof. by conseq finish_updstate_ll (finish_updstate_h _r8 _tb _l). qed.

(* ------------------------------------------------------------------------- *)
(* the status export                                                         *)
(* ------------------------------------------------------------------------- *)

lemma ststatus_updstate_ll: islossless M.ststatus_updstate.
proof. islossless. qed.

hoare ststatus_updstate_h _st:
 M.ststatus_updstate
 : st = _st
 ==> W8.to_uint (BArray3.get8 res 0) = ststatus_r8 (ust_status _st)
  /\ W8.to_uint (BArray3.get8 res 1) = ststatus_at_norm (ust_status _st)
  /\ BArray3.get8 res 2 = ststatus_trailb (ust_status _st).
proof.
proc; wp; ecall (ststatus_data_h ststatus); wp; skip => &hr -> /= r ->; rewrite ststatus_data_specE /=.
have [Hr0 Hr1] : 0 <= ststatus_r8 (ust_status _st) <= 200 by rewrite /ststatus_r8 /=; smt(W64.to_uint_cmp).
have [Ha0 Ha1] : 0 <= ststatus_at_norm (ust_status _st) <= 200 by rewrite /ststatus_at_norm /ststatus_r8 /ststatus_at /=; smt(W64.to_uint_cmp).
split; first by rewrite /truncateu8 W8.of_uintK W64.of_uintK; smt(modz_small pow2_64).
split; first by rewrite /truncateu8 W8.of_uintK W64.of_uintK; smt(modz_small pow2_64).
by rewrite (_: 202 = 200 + 2) 1:// -BArray208.get64d_byte // /ststatus_trailb W8u8.bits8_div // /truncateu8 W64.shr_div_le //=.
qed.

phoare ststatus_updstate_ph _st:
 [ M.ststatus_updstate
 : st = _st
 ==> W8.to_uint (BArray3.get8 res 0) = ststatus_r8 (ust_status _st)
  /\ W8.to_uint (BArray3.get8 res 1) = ststatus_at_norm (ust_status _st)
  /\ BArray3.get8 res 2 = ststatus_trailb (ust_status _st)
 ] = 1%r.
proof. by conseq ststatus_updstate_ll (ststatus_updstate_h _st). qed.
