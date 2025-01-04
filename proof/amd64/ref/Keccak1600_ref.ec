(******************************************************************************
   Keccak1600_avx2.ec:

   Correctness proof for the Keccak REF implementation



******************************************************************************)

require import List Real Int IntDiv CoreMap.
require BitEncoding.
import BitEncoding.BitChunking.

from Jasmin require import JModel.

from CryptoSpecs require import JWordList.
from CryptoSpecs require export Keccakf1600_Spec Keccak1600_Spec.
from CryptoSpecs require import Bindings.

from JazzEC require import Jazz_ref.
from JazzEC require import WArray200.
from JazzEC require import Array25.

(******************************************************************************
   
******************************************************************************)

(* MOVE TO CryptoSpecs *)
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
admit (* should we add lemmas to the spec? *).
qed.


(******************************************************************************
   
******************************************************************************)

lemma state_init_ref_ll:
 islossless M.__state_init_ref.
proof.
proc.
while true (25-to_uint i).
 move=> z; auto => /> &m; rewrite ultE of_uintK /= => Hi.
 by rewrite to_uintD_small /#.
by auto => /> i Hi; rewrite ultE of_uintK /#.
qed.

hoare state_init_ref_h _r8:
 M.__state_init_ref
 : 0 < _r8 <= 200
 ==> pabsorb_spec_ref _r8 [] res.
proof.
proc.
conseq (:_ ==> st=st0) => //=.
 by move=> ? st ->; apply (pabsorb_spec_ref_nil _r8).
while (0 <= to_uint i <= 25 /\ forall k, 0 <= k < to_uint i => st.[k] = z64).
 auto => /> &m Hi1 _ IH; rewrite ultE of_uintK /= => Hi2.
 rewrite to_uintD_small 1:/# /=; split; first smt().
 by move => k Hk1 Hk2; case: (k=to_uint i{m}) => C; rewrite get_setE /#.
auto => /> &m Hr1 Hr2; split; first smt().
move=> i st; rewrite ultE of_uintK /= => ???; have->: to_uint i=25 by smt().
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
 : st = _st /\ rATE8=_r8
 ==> res = addratebit _r8 _st.
proof.
admit (* BDEP? *).
qed.

phoare addratebit_ref_ph _r8 _st:
 [ M.__addratebit_ref
 : st = _st /\ rATE8=_r8
 ==> res = addratebit _r8 _st
 ] = 1%r.
proof. by conseq addratebit_ref_ll (addratebit_ref_h _r8 _st). qed.

