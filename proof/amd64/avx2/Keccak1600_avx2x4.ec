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

(* nth_SQUEEZE1600 lives in common/Keccak1600_statebytes.ec *)



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

lemma st4x_get_pack0 sts:
 st4x_get (st4x_pack sts) 0 = sts.`1.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack1 sts:
 st4x_get (st4x_pack sts) 1 = sts.`2.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack2 sts:
 st4x_get (st4x_pack sts) 2 = sts.`3.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack3 sts:
 st4x_get (st4x_pack sts) 3 = sts.`4.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.


op st4x_match st4x sts = (st4x = st4x_pack sts).


op st4x_map (f:W64.t Array25.t->W64.t Array25.t) (st4x:W256.t Array25.t): W256.t Array25.t =
 st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).

lemma st4x_mapE (f: state->state) (st4x: state4x):
 st4x_map f st4x
 = st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).
proof.
apply Array25.ext_eq => i Hi.
by rewrite initiE //= st4x_packiE. 
qed.

lemma st4x_get_map f st4x k:
 0 <= k < 4 =>
 st4x_get (st4x_map f st4x) k
 = f (st4x_get st4x k).
proof.
move=> Hk.
have: k=0 \/ k=1 \/ k=2 \/ k=3 by smt().
move=> [->|]; first by rewrite st4x_get_pack0.
move=> [->|]; first by rewrite st4x_get_pack1.
move=> [->|]; first by rewrite st4x_get_pack2.
move=> ->; by rewrite st4x_get_pack3.
qed.

lemma st4x_map_comp (f g: state -> state) st4x:
 st4x_map f (st4x_map g st4x) = st4x_map (fun s => f (g s)) st4x.
proof.
rewrite {1}/st4x_map /=.
rewrite (st4x_get_map g st4x 0) 1:// (st4x_get_map g st4x 1) 1://.
rewrite (st4x_get_map g st4x 2) 1:// (st4x_get_map g st4x 3) 1://.
by rewrite /st4x_map.
qed.

abbrev st4x_keccak_iota rc (st4x:state4x) =
 st4x.[0 <- VPBROADCAST_4u64 rc `^` st4x.[0]].

lemma sliceget64_256_25E k i st4x:
 0 <= k < 4 =>
 0 <= i < 25 =>
 sliceget64_256_25 st4x (8 * (4 * i + k) * 8)
 = st4x.[i] \bits64 k.
proof.
move=> Hk Hi.
rewrite /sliceget64_256_25 ifT 1:/# get64E bits64E /=.
apply W64.ext_eq => b Hb.
rewrite !initiE //= pack8E initiE //= initiE 1:/# /= initiE 1:/# /=.
by rewrite bits8iE 1:/# /#.
qed.

lemma VPBROADCAST_4u64_bits64 w k:
 0 <= k < 4 =>
 VPBROADCAST_4u64 w \bits64 k = w.
proof.
move=> Hk; have: k\in iota_ 0 4 by smt(mem_iota).
move: {Hk} k; apply/List.allP.
rewrite -iotaredE /=.
by circuit.
qed.

(* ------------------------------------------------------------------------ *)
(* Lane view of the stores the 4-way code performs on its state, through the *)
(* WArray800 byte encoding (64-bit word q is lane q%%4 of 256-bit word q%/4) *)
(* ------------------------------------------------------------------------ *)

lemma st4x_ext (a b: state4x):
 (forall k, 0 <= k < 4 => st4x_get a k = st4x_get b k) => a = b.
proof.
move=> H; rewrite -(st4x_unpackK a) -(st4x_unpackK b) /st4x_unpack.
by rewrite (H 0) // (H 1) // (H 2) // (H 3).
qed.

lemma st4x_get_set (st: state4x) j w k:
 0 <= k < 4 =>
 st4x_get st.[j <- w] k = (st4x_get st k).[j <- w \bits64 k].
proof.
move=> Hk; rewrite tP => i Hi.
rewrite st4x_getiE // !get_set_if.
by case: (0 <= j < 25 /\ i = j) => C //; rewrite st4x_getiE.
qed.

lemma get64_init256 (st: state4x) q:
 0 <= q < 100 =>
 get64_direct (WArray800.init256 ("_.[_]" st)) (8*q) = st.[q %/ 4] \bits64 (q %% 4).
proof.
move=> Hq; apply W64.wordP => b Hb.
rewrite get64E pack8wE // initiE 1:/# /= initiE 1:/# /= bits8iE 1:/# bits64iE //.
by congr; smt().
qed.

lemma get256_init256 (st: state4x) j:
 0 <= j < 25 =>
 get256_direct (WArray800.init256 ("_.[_]" st)) (32*j) = st.[j].
proof.
move=> Hj; apply W256.wordP => b Hb.
rewrite get256E pack32wE // initiE 1:/# /= initiE 1:/# /= bits8iE 1:/#.
by congr; smt().
qed.

lemma init256_set256 (st: state4x) j w:
 0 <= j < 25 =>
 Array25.init (WArray800.get256 (WArray800.set256_direct (WArray800.init256 ("_.[_]" st)) (32*j) w))
 = st.[j <- w].
proof.
move=> Hj; rewrite tP => i Hi; rewrite initiE //= get_setE //.
apply W256.wordP => b Hb.
rewrite get256E pack32wE // initiE 1:/# /= set256E initiE 1:/# /=.
case: (i = j) => C.
 by rewrite ifT 1:/# bits8iE 1:/#; congr; smt().
by rewrite ifF 1:/# initiE 1:/# /= bits8iE 1:/#; congr; smt().
qed.

(* [init256_set256] at a byte offset (the shape of [__state_init_avx2x4]'s loop) *)
lemma init256_set256_direct (st: state4x) o w:
 0 <= o < 800 => o %% 32 = 0 =>
 Array25.init (WArray800.get256 (WArray800.set256_direct (WArray800.init256 ("_.[_]" st)) o w))
 = st.[o %/ 32 <- w].
proof.
move=> Ho Hm; have {1}->: o = 32 * (o %/ 32) by smt().
by apply init256_set256; smt().
qed.

lemma st4x_get_set64 (st: state4x) q v k:
 0 <= q < 100 => 0 <= k < 4 =>
 st4x_get (Array25.init (WArray800.get256 (WArray800.set64_direct (WArray800.init256 ("_.[_]" st)) (8*q) v))) k
 = if q %% 4 = k then (st4x_get st k).[q %/ 4 <- v] else st4x_get st k.
proof.
move=> Hq Hk; rewrite tP => i Hi.
rewrite st4x_getiE // initiE //=.
have ->: (if q %% 4 = k then (st4x_get st k).[q %/ 4 <- v] else st4x_get st k).[i]
         = if q %% 4 = k /\ i = q %/ 4 then v else st.[i] \bits64 k.
 case: (q %% 4 = k) => C1 /=; last by rewrite st4x_getiE.
 by rewrite get_setE 1:/#; case: (i = q %/ 4) => C2 //; rewrite st4x_getiE.
apply W64.wordP => b Hb.
rewrite bits64iE // get256E pack32wE 1:/# initiE 1:/# /= set64E initiE 1:/# /=.
case: (q %% 4 = k /\ i = q %/ 4) => C.
 by rewrite ifT 1:/# bits8iE 1:/#; congr; smt().
rewrite ifF 1:/# initiE 1:/# /= bits8iE 1:/# bits64iE //.
by congr; smt().
qed.

lemma st4x_keccak_iotaE rc st4x:
 st4x_keccak_iota rc st4x
 = st4x_map (fun st=>st.[0 <- st.[0] `^` rc]) st4x.
proof.
rewrite tP => i Hi.
rewrite get_setE //.
rewrite initiE //= !get_setE // !initiE //=.
rewrite -(W4u64.unpack64K) u256_pack4E.
congr.
rewrite unpack64E.
rewrite W4u64.Pack.init_of_list; congr.
rewrite -iotaredE /=.
case: (i=0) => Ei.
 rewrite (sliceget64_256_25E 0 0) // (sliceget64_256_25E 1 0) //.
 rewrite (sliceget64_256_25E 2 0) // (sliceget64_256_25E 3 0) //.
 by rewrite xorwC !xorb64E !VPBROADCAST_4u64_bits64 //.
rewrite (sliceget64_256_25E 0 i) // (sliceget64_256_25E 1 i) //.
by rewrite (sliceget64_256_25E 2 i) // (sliceget64_256_25E 3 i) //.
qed.


op st4x_keccak_pround =  st4x_map keccak_pround_op.

abbrev keccak_round_i i st =
 foldl (fun s i => keccak_round_op rc_spec.[i] s) st (iota_ 0 i).




(******************************************************************************
   
******************************************************************************)

import BitEncoding BitChunking.


op keccak_f1600_x4 = st4x_map keccak_f1600_op.

lemma st4x_get_iter (st: state4x) n k:
 0 <= n => 0 <= k < 4 =>
 st4x_get (iter n keccak_f1600_x4 st) k = st_i (st4x_get st k) n.
proof.
move=> Hn Hk; elim/natind: n Hn => [n Hn _|n Hn IH _].
 by rewrite !iter0 // /st_i iter0.
by rewrite iterS // /keccak_f1600_x4 st4x_get_map // IH // /st_i iterS.
qed.

op st4x0 = Array25.create W256.zero.

lemma st4x0E: st4x_match st4x0 (st0,st0,st0,st0).
proof.
rewrite /st4x_match tP => i Hi.
rewrite createiE // st4x_packiE //; iota.
by rewrite initiE // u256_pack4_zero.
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
move=> Hr; rewrite /pabsorb_spec_avx2x4 Hr /=.
rewrite chunk0 1:/# /stateabsorb_iblocks /= /chunkremains /= bytes2state0 addstate_st0.
exact st4x0E.
qed.

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
while (0 <= i <= 32*25 /\ i %% 32 = 0 /\ z256 = W256.zero /\
       forall k, 0 <= k < i %/ 32 => st.[k] = W256.zero).
 auto => /> &m Hi0 _ Hm IH Hi.
 rewrite init256_set256_direct 1,2:/#; do! split; 1..3:smt().
 by move=> k Hk1 Hk2; rewrite get_setE 1:/#; case: (k = i{m} %/ 32) => C //; apply IH => /#.
auto => /> &hr; split => [/# | i0 st0 Hlt Hi1 Hi2 _ H].
by rewrite tP /st4x0 => k Hk; rewrite createiE // H /#.
qed.


phoare state_init_avx2x4_ph':
 [ M.__state_init_avx2x4
 : true
 ==> res = st4x0
 ] = 1%r.
proof. by conseq state_init_avx2x4_ll state_init_avx2x4_h'. qed.

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

(* the rate bit as a XOR with a power of two (one bit of one word) *)
lemma u64_xorbit_ofint (w: W64.t) b:
 0 <= b < 64 => u64_xorbit b w = w `^` W64.of_int (1 `<<` b).
proof.
move=> Hb; have: b \in iota_ 0 64 by smt(mem_iota).
move: {Hb} b; apply/List.allP.
by rewrite -iotaredE /=; circuit.
qed.

hoare addratebit_avx2x4_h _r8 _st:
 M.__addratebit_avx2x4
 : st = _st /\ rATE8 = _r8 /\ 0 < _r8 <= 200
 ==> res = st4x_map (addratebit _r8) _st.
proof.
proc; auto => /> Hr0 Hr1.
apply st4x_ext => k Hk.
rewrite st4x_get_map // st4x_get_set // xorb64E VPBROADCAST_4u64_bits64 //.
rewrite /addratebit -addratebitE 1:/#.
congr; rewrite u64_xorbit_ofint 1:/# -st4x_getiE 1,2:/#.
by rewrite xorwC.
qed.

phoare addratebit_avx2x4_ph _r8 _st:
 [ M.__addratebit_avx2x4
 : st = _st /\ rATE8 = _r8 /\ 0 < _r8 <= 200
 ==> res = st4x_map (addratebit _r8) _st
 ] = 1%r.
proof. by conseq addratebit_avx2x4_ll (addratebit_avx2x4_h _r8 _st). qed.

(* the 4x4 transposition used by the 4-way dump: output k packs lane k of the
   four inputs *)
hoare u64x4_u256x4_h _y0 _y1 _y2 _y3:
 M.__4u64x4_u256x4
 : y0 = _y0 /\ y1 = _y1 /\ y2 = _y2 /\ y3 = _y3
 ==> res.`1 = u256_pack4 (_y0 \bits64 0) (_y1 \bits64 0) (_y2 \bits64 0) (_y3 \bits64 0)
  /\ res.`2 = u256_pack4 (_y0 \bits64 1) (_y1 \bits64 1) (_y2 \bits64 1) (_y3 \bits64 1)
  /\ res.`3 = u256_pack4 (_y0 \bits64 2) (_y1 \bits64 2) (_y2 \bits64 2) (_y3 \bits64 2)
  /\ res.`4 = u256_pack4 (_y0 \bits64 3) (_y1 \bits64 3) (_y2 \bits64 3) (_y3 \bits64 3).
proof. by proc; auto => />; circuit. qed.

lemma u64x4_u256x4_ll: islossless M.__4u64x4_u256x4 by islossless.
