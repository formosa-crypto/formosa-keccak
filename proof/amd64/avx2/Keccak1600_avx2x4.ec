(******************************************************************************
   Keccak1600_avx2x4.ec:

   Correctness proof for the 4-way AVX2 implementation



******************************************************************************)

require import AllCore List Real Int IntDiv StdOrder.

from Jasmin require import JModel_x86.

from CryptoSpecs require export FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec Keccak1600_Spec FIPS202_SHA3_Spec.

require import Keccak_bindings.
require import Avx2_extra.

from JazzEC require import Keccak1600_Jazz.


from JazzEC require import WArray200 WArray800.
from JazzEC require import Array100 Array25.

import IntOrder.

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



(** Packed 4x-state *)

type state4x = W256.t Array25.t.

op st4x_get a k=
 init_25_64 (fun i => sliceget64_256_25 a (8*(4*i+k)*8)).


lemma st4x_getiE x k i:
 0 <= k < 4 =>
 0 <= i < 25 =>
 (st4x_get x k).[i] = x.[i] \bits64 k.
proof.  
move=> Hk Hi; rewrite initiE //= /sliceget64_256_25 ifT 1:/#.
rewrite get64E pack8E.
apply W64.ext_eq => b Hb.
rewrite bits64iE // initiE //= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
by congr; smt().
qed.

op st4x_pack (sts: state*state*state*state): state4x =
 init_25_256 (fun i => u256_pack4 sts.`1.[i] sts.`2.[i] sts.`3.[i] sts.`4.[i]).

lemma st4x_packiE (sts: state*state*state*state) i:
 0 <= i < 25 =>
 (st4x_pack sts).[i] = u256_pack4 (sts.`1.[i]) (sts.`2.[i]) (sts.`3.[i]) (sts.`4.[i]).
proof. by rewrite /st4x_pack => Hi; rewrite initiE //. qed.

op st4x_unpack (st4: state4x): state*state*state*state =
 ( st4x_get st4 0
 , st4x_get st4 1
 , st4x_get st4 2
 , st4x_get st4 3
 ).

lemma st4x_unpackK st4x:
 st4x_pack (st4x_unpack st4x) = st4x.
proof.
rewrite /st4x_pack /st4x_unpack.
apply Array25.ext_eq => i Hi; rewrite initiE //.
beta; iota.
rewrite !st4x_getiE //=.
rewrite u256_pack4E -{5}(unpack64K st4x.[i]); congr.
by rewrite unpack64E init_of_list -iotaredE /=. 
qed.

lemma st4x_packK (sts: state*state*state*state):
 st4x_unpack (st4x_pack sts) = sts.
proof.
move: sts => [st0 st1 st2 st3].
rewrite /st4x_pack /st4x_unpack.
congr; 
 by (apply Array25.ext_eq => i Hi;
     rewrite st4x_getiE //= initiE //= u256_pack4E pack4bE //).
qed.

op st4x_map (f:W64.t Array25.t->W64.t Array25.t) (st4x:W256.t Array25.t): W256.t Array25.t =
 st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).

lemma st4x_mapE (f: state->state) (st4x: state4x):
 st4x_map f st4x
 = st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).
proof.
apply Array25.ext_eq => i Hi.
by rewrite initiE //= st4x_packiE. 
qed.

op st4x_match st4x sts = (st4x = st4x_pack sts).


(******************************************************************************
   
******************************************************************************)

import BitEncoding BitChunking.


op keccak_f1600_x4 = st4x_map keccak_f1600_op.

op st4x0 = Array25.create W256.zero.

lemma st4x0E: st4x_match st4x0 (st0,st0,st0,st0).
proof.
rewrite /st4x_match tP => i Hi.
rewrite createiE // st4x_packiE //; iota.
by rewrite !createiE // u256_pack4_zero.
qed.


op addstate_avx2x4 (st: state4x, l0 l1 l2 l3: W8.t list): state4x.

op absorb_spec_avx2x4 (r8: int) (tb: int) (l0 l1 l2 l3: W8.t list) st4x =
 st4x_match st4x ( ABSORB1600 (W8.of_int tb) r8 l0
                 , ABSORB1600 (W8.of_int tb) r8 l1
                 , ABSORB1600 (W8.of_int tb) r8 l2
                 , ABSORB1600 (W8.of_int tb) r8 l3).

op pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 st4x: bool =
 0 < r8 <= 200 /\
 size l1 = size l0 /\ size l2 = size l0 /\ size l3 = size l0 /\
 st4x_match st4x
            ( addstate (stateabsorb_iblocks (chunk r8 l0) st0) (bytes2state (chunkremains r8 l0))
            , addstate (stateabsorb_iblocks (chunk r8 l1) st0) (bytes2state (chunkremains r8 l1))
            , addstate (stateabsorb_iblocks (chunk r8 l2) st0) (bytes2state (chunkremains r8 l2))
            , addstate (stateabsorb_iblocks (chunk r8 l3) st0) (bytes2state (chunkremains r8 l3))).

lemma pabsorb_spec_avx2x4_nil r8:
 0 < r8 <= 200 =>
 pabsorb_spec_avx2x4 r8 [] [] [] [] st4x0.
proof.
admitted.

(******************************************************************************
   
******************************************************************************)

lemma state_init_avx2x4_ll:
 islossless M.__state_init_avx2x4.
proof.
proc.
while true (32*25-i).
 by move=> z; auto => /> &m /#.
by auto => /#.
qed.

hoare state_init_avx2x4_h':
 M.__state_init_avx2x4
 : true
 ==> res = st4x0.
proof.
proc.
admitted (* BDEP? *).


phoare state_init_avx2x4_ph':
 [ M.__state_init_avx2x4
 : true
 ==> res = st4x0
 ] = 1%r.
admitted.

hoare state_init_avx2x4_h _r8:
 M.__state_init_avx2x4
 : 0 < _r8 <= 200
 ==> pabsorb_spec_avx2x4 _r8 [] [] [] [] res.
proof.
conseq state_init_avx2x4_h' => _ Hr8 st ->.
exact pabsorb_spec_avx2x4_nil.
qed.

phoare state_init_avx2x4_ph _r8:
 [ M.__state_init_avx2x4
 : 0 < _r8 <= 200
 ==> pabsorb_spec_avx2x4 _r8 [] [] [] [] res
 ] = 1%r.
proof. by conseq state_init_avx2x4_ll (state_init_avx2x4_h _r8). qed.


lemma addratebit_avx2x4_ll: islossless M.__addratebit_avx2x4
 by islossless.

