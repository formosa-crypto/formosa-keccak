(******************************************************************************
   Keccak1600_avx2.ec:

   Correctness proof for the Keccak REF implementation



******************************************************************************)

require import List Real Int IntDiv CoreMap List.
require BitEncoding.
import BitEncoding.BitChunking.

from Jasmin require import JModel.

from CryptoSpecs require import JWordList.
from CryptoSpecs require export Keccakf1600_Spec Keccak1600_Spec.
from CryptoSpecs require import Bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200.
from JazzEC require import Array25.

(******************************************************************************
   
******************************************************************************)

(* MOVE TO CryptoSpecs *)
lemma state2bytesE st i:
 (state2bytes st).[i] = (stbytes st).[i].
proof.
case: (0 <= i < 200) => C.
 rewrite /state2bytes.
 have ?: 8*size (to_list st) = 200 by smt(Array25.size_to_list).
 rewrite nth_w64L_to_bytes 1:/# W8u8.nth_to_list.
 rewrite initiE 1:// /=.
 by rewrite (nth_change_dfl witness) 1:/# get_to_list.
rewrite nth_out.
 by rewrite size_state2bytes.
by rewrite get_out.
qed.

lemma addstate_st0 st:
 addstate st0 st = st.
proof.
rewrite tP => i Hi.
rewrite /addstate /st0 /map2.
by rewrite initiE //= createiE //=.
qed.

lemma bytes2state0: bytes2state [] = st0.
proof.
rewrite /bytes2state /st0 tP => i Hi.
rewrite get_of_list 1:// createiE //.
by rewrite w64L_from_bytes_nil.
qed.
(* end: MOVE TO CryptoSpecs *)


op fillstate_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill 
   (fun i => l.[i-at]) at (size l) (stbytes st)).

op addstate_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill 
   (fun i => (stbytes st).[i] `^` l.[i-at]) at (size l) (stbytes st)).

op absorb_spec_ref (r8: int) (tb: int) (l: W8.t list) st =
 st = ABSORB1600 (W8.of_int tb) r8 l.

op pabsorb_spec_ref r8 l st: bool =
 0 < r8 <= 200 /\
 st = addstate (stateabsorb_iblocks (chunk r8 l) st0) (bytes2state (chunkremains r8 l)).

lemma pabsorb_spec_ref_nil r8:
 0 < r8 <= 200 =>
 pabsorb_spec_ref r8 [] st0.
proof.
move=> Hr; rewrite /pabsorb_spec_ref => />.
rewrite chunk0 /= 1:/#.
rewrite /stateabsorb_iblocks /= /chunkremains /=.
by rewrite addstate_st0 bytes2state0.
qed.


(******************************************************************************
   
******************************************************************************)

lemma state_init_ref_ll:
 islossless M.__state_init_ref.
proof.
proc.
while true (25- i).
 by move=> z; auto => /> &m Hi /#.
by auto => /> i Hi /#.
qed.

hoare state_init_ref_h _r8:
 M.__state_init_ref
 : 0 < _r8 <= 200
 ==> pabsorb_spec_ref _r8 [] res.
proof.
proc.
conseq (:_ ==> st=st0) => //=.
 by move=> ? st ->; apply (pabsorb_spec_ref_nil _r8).
while (0 <= i <= 25 /\ forall k, 0 <= k < i => st.[k] = z64).
 auto => /> &m Hi1 _ IH Hi2; split; first smt().
 by move => k Hk1 Hk2; case: (k=i{m}) => C; rewrite get_setE /#.
auto => /> &m Hr1 Hr2; split; first smt().
move=> i st ???; have->: i=25 by smt().
move=> H; rewrite tP /st0 => j Hj.
by rewrite createiE 1:// H.
qed.

phoare state_init_ref_ph _r8:
 [ M.__state_init_ref
 : 0 < _r8 <= 200
 ==> pabsorb_spec_ref _r8 [] res
 ] = 1%r.
proof. by conseq state_init_ref_ll (state_init_ref_h _r8). qed.

lemma addratebit_ref_ll: islossless M.__addratebit_ref
 by islossless.

hoare addratebit_ref_h _r8 _st:
 M.__addratebit_ref
 : st = _st /\ _RATE8=_r8
 ==> res = addratebit _r8 _st.
proof.
admit (* BDEP? *).
qed.

phoare addratebit_ref_ph _r8 _st:
 [ M.__addratebit_ref
 : st = _st /\ _RATE8=_r8
 ==> res = addratebit _r8 _st
 ] = 1%r.
proof. by conseq addratebit_ref_ll (addratebit_ref_h _r8 _st). qed.

