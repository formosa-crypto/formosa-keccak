(******************************************************************************
   Keccak1600_avx2x4.ec:

   Correctness proof for the 4-way AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import Bindings.
from CryptoSpecs require export FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec Keccak1600_Spec FIPS202_SHA3_Spec.

from JazzEC require import Jazz_avx2.


from JazzEC require import WArray768 WArray200.
from JazzEC require import Array25 Array24 Array5.


require import StdOrder.
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


(*
import Ring.IntID.

lemma bits8_bits (w: W256.t) (k: int):
 w \bits8 k = W8.bits2w (bits w (8*k) 8).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

lemma bits64_bits (w: W256.t) (k: int):
 w \bits64 k = W64.bits2w (bits w (64*k) 64).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

(* useful to eval constants... *)
lemma bits8_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits8 k
 = W8.of_int (to_uint w %/ (2^(8*k)) %% 2^8).
proof.
move=> Hk; rewrite bits8_bits.
apply W8.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W8.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma bits64_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits64 k
 = W64.of_int (to_uint w %/ (2^(64*k)) %% 2^64).
proof.
move=> Hk; rewrite bits64_bits.
apply W64.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W64.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma get256_init256 (a: W256.t Array24.t) i:
 0 <= i < 24 =>
 get256 (WArray768.init256 ("_.[_]" a)) i = a.[i].
proof.
move=> Hi; rewrite /get256_direct /init256 -(unpack8K a.[i]).
congr; apply W32u8.Pack.ext_eq => x Hx.
rewrite initiE //= unpack8E !initiE 1..2:/# /=; congr.
 congr; smt().
smt().
qed.
*)


require import Avx2_extra.

import BitEncoding BitChunking.

from JazzEC require import WArray800.

op sliceget64_256_25 (arr: W256.t Array25.t) (offset: int) : W64.t = 
 if 8 %| offset
 then WArray800.get64_direct (WArray800.init256 (fun i => arr.[i])) (offset %/ 8)
 else W64.bits2w (take 64 (drop offset (flatten (map W256.w2bits (to_list arr))))).

bind op [W256.t & W64.t & Array25.t] sliceget64_256_25 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget64_256_25 /= => H k kb. 
case (8 %| offset) => /= *; last by smt(W64.get_bits2w).
rewrite /get64_direct pack8E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 256 _). 
 by rewrite allP => x /=; rewrite mapP => He; elim He;smt(W256.size_w2bits).
rewrite (nth_map W256.zero []); 1: smt(Array25.size_to_list).
by rewrite nth_mkseq /#.
qed.


op sliceget256_64_25 (arr: W64.t Array25.t) (offset: int) : W256.t = 
 if 8 %| offset
 then  WArray200.get256_direct (WArray200.init64 (fun (i_0 : int) => arr.[i_0])) (offset %/ 8)
 else W256.bits2w (take 256 (drop offset (flatten (map W64.w2bits (to_list arr))))).

bind op [W64.t & W256.t & Array25.t] sliceget256_64_25 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget256_64_25 /= => H k kb. 
case (8 %| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 64 _). 
 by rewrite allP => x /=; rewrite mapP => He; elim He;smt(W64.size_w2bits).
rewrite (nth_map W64.zero []); 1: smt(Array25.size_to_list).
by rewrite nth_mkseq /#.
qed.

op sliceset64_256_25 (arr: W256.t Array25.t) (offset: int) (bv: W64.t) : W256.t Array25.t =
 if 8 %| offset
 then Array25.init 
       (fun i =>
        WArray800.get256
         (WArray800.set64_direct
           (WArray800.init256 (fun j => arr.[j]))
           (offset %/ 8)
           bv)
         i)
 else Array25.of_list
       witness
       (map W256.bits2w
            (chunk 256
                   (take offset (flatten (map W256.w2bits (to_list arr)))
                     ++ w2bits bv ++
                     drop (offset+64) (flatten (map W256.w2bits (to_list arr)))))).

lemma size_flatten_W256_w2bits (a : W256.t list) :
  (size (flatten (map W256.w2bits (a))))  =  256 * size a.
proof.
rewrite (size_flatten' 256).
 by move=> l /mapP [x [Hx ->]]; rewrite W256.size_w2bits.
by rewrite size_map.
qed.

bind op [W256.t & W64.t & Array25.t] sliceset64_256_25 "asliceset".
realize bvaslicesetP.
move => arr offset bv H /= k kb; rewrite /sliceset64_256_25 /=.
case (8 %| offset) => /= *; last first.
+ rewrite of_listK; 1: by rewrite size_map size_chunk 1:// !size_cat size_take;
      by smt(size_take size_drop  W256.size_w2bits size_cat Array25.size_to_list size_flatten_W256_w2bits size_ge0). 
  rewrite -(map_comp W256.w2bits W256.bits2w) /(\o). 
  have := eq_in_map ((fun (x : bool list) => w2bits ((bits2w x))%W256)) idfun (chunk 256
        (take offset (flatten (map W256.w2bits (to_list arr))) ++ w2bits bv ++
         drop (offset + 64) (flatten (map W256.w2bits (to_list arr))))).
  rewrite iffE => [#] -> * /=; 1: by smt(in_chunk_size W256.bits2wK).
  rewrite map_id /= chunkK 1://;1: by rewrite !size_cat size_take;
    by smt(size_take size_drop  W256.size_w2bits size_cat Array25.size_to_list size_flatten_W256_w2bits size_ge0). 
  by rewrite !nth_cat !size_cat /=;
     smt(nth_take nth_drop size_take size_drop  W256.size_w2bits size_cat Array25.size_to_list size_flatten_W256_w2bits size_ge0). 
rewrite (nth_flatten _ 256); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W256.size_w2bits).
rewrite (nth_map W256.zero []); 1: smt(Array25.size_to_list).
rewrite nth_mkseq 1:/# /= initiE 1:/# /= get256E pack32E initiE 1:/# /= initiE 1:/# /= /set64_direct.
rewrite initiE 1:/# /=.
case (offset <= k && k < offset + 64) => *; 1: by 
  rewrite ifT 1:/#  get_bits8 /= 1,2:/# initiE // initiE //.
rewrite ifF 1:/# initiE 1:/# /=.
rewrite (nth_flatten _ 256); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W256.size_w2bits).
rewrite (nth_map W256.zero []); 1: smt(Array25.size_to_list).
rewrite nth_mkseq 1:/# /= bits8E /= initiE /# /=.
qed.

op sliceset256_64_25 (arr: W64.t Array25.t) (offset: int) (bv: W256.t) : W64.t Array25.t =
 if 8 %| offset
 then Array25.init 
       (fun i =>
        WArray200.get64
         (WArray200.set256_direct
           (WArray200.init64 (fun j => arr.[j]))
           (offset %/ 8)
           bv)
         i)
 else Array25.of_list
       witness
       (map W64.bits2w
            (chunk 64
                   (take offset (flatten (map W64.w2bits (to_list arr)))
                     ++ w2bits bv ++
                     drop (offset+256) (flatten (map W64.w2bits (to_list arr)))))).

lemma size_flatten_W64_w2bits (a : W64.t list) :
  (size (flatten (map W64.w2bits (a))))  =  64 * size a.
proof.
rewrite (size_flatten' 64).
 by move=> l /mapP [x [Hx ->]]; rewrite W64.size_w2bits.
by rewrite size_map.
qed.


bind op [W64.t & W256.t & Array25.t] sliceset256_64_25 "asliceset".
realize bvaslicesetP. 
move => arr offset bv H /= k kb; rewrite /sliceset256_64_25 /=.
case (8 %| offset) => /= *; last first.
+ rewrite of_listK; 1: by rewrite size_map size_chunk 1:// !size_cat size_take;
      by smt(size_take size_drop  W64.size_w2bits size_cat Array25.size_to_list size_flatten_W64_w2bits size_ge0). 
  rewrite -(map_comp W64.w2bits W64.bits2w) /(\o). 
  have := eq_in_map ((fun (x : bool list) => w2bits ((bits2w x))%W64)) idfun (chunk 64
        (take offset (flatten (map W64.w2bits (to_list arr))) ++ w2bits bv ++
         drop (offset + 256) (flatten (map W64.w2bits (to_list arr))))).
  rewrite iffE => [#] -> * /=; 1: by smt(in_chunk_size W64.bits2wK).
  rewrite map_id /= chunkK 1://;1: by rewrite !size_cat size_take;
    by smt(size_take size_drop  W64.size_w2bits size_cat Array25.size_to_list size_flatten_W64_w2bits size_ge0). 
  by rewrite !nth_cat !size_cat /=;
     smt(nth_take nth_drop size_take size_drop  W64.size_w2bits size_cat Array25.size_to_list size_flatten_W64_w2bits size_ge0). 
rewrite (nth_flatten _ 64); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W64.size_w2bits).
rewrite (nth_map W64.zero []); 1: smt(Array25.size_to_list).
rewrite nth_mkseq 1:/# /= initiE 1:/# /= get64E pack8E initiE 1:/# /= initiE 1:/# /= /set256_direct.
rewrite initiE 1:/# /=.
case (offset <= k && k < offset + 256) => *; 1: by 
  rewrite ifT 1:/#  get_bits8 /= 1,2:/# initiE // initiE //.
rewrite ifF 1:/# initiE 1:/# /=.
rewrite (nth_flatten _ 64); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W64.size_w2bits).
rewrite (nth_map W64.zero []); 1: smt(Array25.size_to_list).
rewrite nth_mkseq 1:/# /= bits8E /= initiE /# /=.
qed.

(** Packed 4x-state *)

type state4x = W256.t Array25.t.

(*
abbrev st4x_get (a: state4x) (k: int): state =
 init_25_64 (fun i => u256_bits64 a.[i] k).
*)
abbrev st4x_get a k=
 init_25_64 (fun i => sliceget64_256_25 a (8*(4*i+k)*8)).


lemma st4x_getiE x k i:
 0 <= k < 4 =>
 0 <= i < 25 =>
 (st4x_get x k).[i] = x.[i] \bits64 k.
proof.  admit(*by move=> Hk Hi; rewrite initiE //= u256_bits64E*). qed.

abbrev st4x_pack (sts: state*state*state*state): state4x =
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

abbrev st4x_map (f:W64.t Array25.t->W64.t Array25.t) (st4x:W256.t Array25.t): W256.t Array25.t =
 st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).

lemma st4x_mapE (f: state->state) (st4x: state4x):
 st4x_map f st4x
 = st4x_pack (f (st4x_get st4x 0), f (st4x_get st4x 1), f (st4x_get st4x 2), f (st4x_get st4x 3)).
proof.
apply Array25.ext_eq => i Hi.
by rewrite initiE //. 
qed.

(*op st4x_match (st4x: state4x) (st0 st1 st2 st3: state) =
 st4x = st4x_pack (st0,st1,st2,st3).
*)
abbrev st4x_match st4x sts = (st4x = st4x_pack sts).




(*
lemma a25bits64iE x k i:
 0 <= i < 25 =>
 (x \a25bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a24bits64iE x k i:
 0 <= i < 24 =>
 (x \a24bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a5bits64iE x k i:
 0 <= i < 5 =>
 (x \a5bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a25unpack4K s4:
 a25pack4 (a25unpack4 s4) = s4.
proof.
rewrite /a25pack4 /a25unpack4.
apply Array25.ext_eq => i Hi; rewrite initiE //=.
rewrite -iotaredE /= !a25bits64iE //=.
rewrite -{5}(unpack64K s4.[i]); congr.
by rewrite unpack64E init_of_list -iotaredE /=. 
qed.

lemma a25pack4_bits64 k (stl: state list):
 0 <= k < 4 =>
 a25pack4 stl \a25bits64 k = nth st0 stl k.
proof.
move=> Hk; apply Array25.ext_eq => i Hi.
rewrite mapiE //= initiE //= pack4bE //=.
rewrite of_listE initiE //=.
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

op a5pack4 (l: (W64.t Array5.t) list): W256.t Array5.t =
 Array5.init (fun i => pack4 (map (fun (x: W64.t Array5.t) => x.[i]) l)).

lemma a25pack4_eq stl st4x:
 a25pack4 stl = st4x
 <=>
 all (fun k=>st4x \a25bits64 k = nth st0 stl k) (iota_ 0 4).
proof.
split.
 move => <-; apply/List.allP => k. 
 rewrite mem_iota => Hk /=; apply a25pack4_bits64; smt().
move=> /List.allP H.
apply Array25.ext_eq => i Hi.
rewrite initiE //=.
rewrite -(unpack64K st4x.[i]); congr.
apply W4u64.Pack.ext_eq => k Hk.
rewrite of_listE unpack64E !initiE //=.
rewrite -a25bits64iE // H; first smt(mem_iota).
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

lemma a5bits64_set (c: W256.t Array5.t) x y i:
 0 <= i < 4 =>
 0 <= x < 5 =>
 c.[x <- y] \a5bits64 i
 = (c \a5bits64 i).[x <- y \bits64 i].
proof.
move=> Hi Hx; apply Array5.ext_eq => j Hj.
rewrite a5bits64iE 1:// !get_setE 1..2:/#.
case: (j=x) => E //.
by rewrite a5bits64iE.
qed.

lemma xorw_bits64 (w1 w2: W256.t) k:
 0 <= k < 4 =>
 w1 `^` w2 \bits64 k = (w1 \bits64 k) `^` (w2 \bits64 k).
proof.
move=> Hk; rewrite -{1}(unpack64K w1) -{1}(unpack64K w2). 
by rewrite xorb4u64E pack4bE // map2iE // !unpack64E !initiE.
qed.


op map_state4x (f:state->state) (st:state4x): state4x =
 a25pack4 (map f (a25unpack4 st)).

lemma map_state4x_a25bits64 f st k:
 0 <= k < 4 =>
 (map_state4x f st) \a25bits64 k = f (st \a25bits64 k).
proof.
move=> Hk.
rewrite /map_state4x /a25unpack4 -map_comp /(\o) /= a25pack4_bits64 1:// -iotaredE.
have: k \in iotared 0 4 by smt(mem_iota).
by move: {Hk} k ; apply/List.allP.
qed.

*)
(******************)


(******************************************************************************
   
******************************************************************************)

from CryptoSpecs require import Keccak1600_Spec.
import BitEncoding BitChunking.
from JazzEC require import Array25 WArray200.



op keccak_f1600_x4 = st4x_map keccak_f1600_op.

op st4x0 = Array25.create W256.zero.

lemma st4x0E: st4x_match st4x0 (st0,st0,st0,st0).
proof.
rewrite tP => i Hi.
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

hoare state_init_avx2x4_h:
 Jazz_avx2.M.__state_init_avx2x4
 : true
 ==> res = st4x0.
proof.
proc.
admitted (* BDEP? *).


lemma state_init_avx2x4_ll:
 islossless M.__state_init_avx2x4.
proof.
proc.
while true (32*25-to_uint i).
 move=> z; auto => /> &m; rewrite ultE of_uintK /= => Hi.
 by rewrite to_uintD_small /#.
by auto => /> i Hi; rewrite ultE of_uintK /#.
qed.

phoare state_init_avx2x4_ph:
 [ Jazz_avx2.M.__state_init_avx2x4
 : true
 ==> res = st4x0
 ] = 1%r.
admitted.


lemma addratebit_avx2x4_ll: islossless M.__addratebit_avx2x4
 by islossless.

