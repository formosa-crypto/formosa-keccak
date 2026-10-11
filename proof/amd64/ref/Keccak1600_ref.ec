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
require export Keccak1600_statebytes.

require import Keccak_bindings.

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
by rewrite initiE //= initiE //.
qed.

lemma bytes2state0: bytes2state [] = st0.
proof.
rewrite /bytes2state /st0 tP => i Hi.
rewrite get_of_list 1:// initiE //.
by rewrite w64L_from_bytes_nil.
qed.
(* end: MOVE TO CryptoSpecs *)


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

(* the shared predicate (Keccak1600_statebytes) under its ref name; kept as
   a separate op because downstream proofs unfold it by qualified name *)
lemma pabsorb_spec_refE r8 l st:
 pabsorb_spec_ref r8 l st = pabsorb_spec r8 l st.
proof. by []. qed.


(******************************************************************************
   
******************************************************************************)

(* A zero 256-bit store at byte offset [o] (a multiple of 8) of the state's
   byte view clears the 64-bit words it covers (AVX2 branch of [__state_init]). *)
lemma get64_set256_zero (t: WArray200.t) o k:
 0 <= o => o + 32 <= 200 => o %% 8 = 0 => 0 <= k < 25 =>
 WArray200.get64 (WArray200.set256_direct t o W256.zero) k
 = if o <= 8*k < o + 32 then W64.zero else WArray200.get64 t k.
proof.
move=> Ho1 Ho2 Ho3 Hk; rewrite !get64E.
case: (o <= 8*k < o + 32) => C.
 apply W8u8.wordP => i Hi; rewrite pack8bE // initiE //= set256E initiE 1:/# /=.
 by rewrite ifT 1:/# W32u8.get_zero W8u8.get_zero.
congr; apply W8u8.Pack.init_ext => i Hi /=.
by rewrite set256E initiE 1:/# /= ifF 1:/#.
qed.

lemma state_init_ll:
 islossless M.__state_init.
proof.
proc; islossless.
while true (25- i).
 by move=> z; auto => /> &m Hi /#.
by auto => /> i Hi /#.
qed.

hoare state_init_h _r8:
 M.__state_init
 : 0 < _r8 <= 200
 ==> pabsorb_spec_ref _r8 [] res.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc.
conseq (:_ ==> st=st0) => //=.
 by move=> ? st ->; apply (pabsorb_spec_ref_nil _r8).
seq 1: #pre; first inline*; auto.
if => //.
 (* AVX2 path *)
 wp; skip => /> &m _ _ _; rewrite tP => k Hk.
 rewrite get_setE //; case: (k = 24) => Ck; first by rewrite Ck /st0 /init_25_64 initiE.
 rewrite /st0 /init_25_64 !initiE //= !(stwordsK, get64_set256_zero) //.
 smt().
(* scalar path *)
while (0 <= i <= 25 /\ forall k, 0 <= k < i => st.[k] = z64).
 auto => /> &m Hi1 _ IH Hi2; split; first smt().
 by move => k Hk1 Hk2; case: (k=i{m}) => C; rewrite get_setE /#.
wp; auto => /> &m Hr1 Hr2 ?; split; first smt().
move=> i st ???; have->: i=25 by smt().
move=> H; rewrite tP /st0 => j Hj.
by rewrite initiE 1:// H.
qed.

phoare state_init_ph _r8:
 [ M.__state_init
 : 0 < _r8 <= 200
 ==> pabsorb_spec_ref _r8 [] res
 ] = 1%r.
proof. by conseq state_init_ll (state_init_h _r8). qed.

lemma addratebit_ll: islossless M.__addratebit
 by islossless.

hoare addratebit_h _r8 _st:
 M.__addratebit
 : st = _st /\ _RATE8=_r8
 ==> res = addratebit _r8 _st.
proof.
proc; simplify.
by auto => />.
qed.

phoare addratebit_ph _r8 _st:
 [ M.__addratebit
 : st = _st /\ _RATE8=_r8
 ==> res = addratebit _r8 _st
 ] = 1%r.
proof. by conseq addratebit_ll (addratebit_h _r8 _st). qed.

