require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.

from JazzEC require Jazz_ref.
from JazzEC require import Jazz_avx2.
from JazzEC require import WArray768 Array5 Array25.

from JazzEC require import WArray200 WArray800.
from JazzEC require import Array100.


op st4x_to_4st (st4x: state4x): state*state*state*state =
 ( init_25_64 (fun i => sliceget64_256_25 st4x ((200*0+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*1+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*2+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*3+8*i)*8))
 ).


bind array Array100."_.[_]" Array100."_.[_<-_]" Array100.to_list Array100.of_list Array100.t 100.
realize tolistP by done.
realize get_setP by smt(Array100.get_setE). 
realize eqP by smt(Array100.tP).
realize get_out by smt(Array100.get_out).

op init_100_64 (f: int -> W64.t) = Array100.init f.

bind op [W64.t & Array100.t] init_100_64 "ainit".
realize bvainitP.
proof.
rewrite /init_100_64 => f.
rewrite BVA_Top_Array100_Array100_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array100.initE).
qed.



op sliceget256_64_100 (arr: W64.t Array100.t) (offset:int): W256.t =
 if 8 %| offset
 then WArray800.get256_direct
       (WArray800.init64 (fun i => arr.[i]))
       (offset %/ 8)
 else W256.bits2w (take 256 (drop offset (flatten (map W64.w2bits (to_list arr))))).

bind op [W64.t & W256.t & Array100.t] sliceget256_64_100 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget256_64_100 /= => H k kb. 
case (8 %| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 64 _). 
 by rewrite allP => x /=; rewrite mapP => He; elim He;smt(W64.size_w2bits).
rewrite (nth_map W64.zero []); 1: smt(Array100.size_to_list).
by rewrite nth_mkseq /#.
qed.


abbrev st4x_from_4st (sts: state*state*state*state): state4x =
 init_25_256
  (fun i =>
    sliceget256_64_100
     (init_100_64
      (fun j =>
        if j < 25 then sts.`1.[j]
        else if j < 50 then sts.`2.[j-25]
        else if j < 75 then sts.`3.[j-50]
        else sts.`4.[j-75]))
      (32*i*8)
    ).

require import Avx2_extra.
op st4x_pack_spec (sts: state4x): state4x =
 st4x_pack (st4x_to_4st sts).

op st4x_unpack_spec (st4x: state4x) =
 st4x_from_4st (st4x_unpack st4x).
(*
  (init_25_64 (fun i => zero),init_25_64 (fun i => zero),init_25_64 (fun i => zero),init_25_64 (fun i => zero)). 
*)
op st4x_inv (_: state4x) = true.


import BitEncoding BitChunking.
lemma chunk1 ['a] n (l: 'a list):
 size l = n =>
 n <> 0 =>
 chunk n l = [l].
proof.
rewrite /chunk.
move=> Hn H0.
by rewrite Hn divzz H0 b2i1 mkseq1 /= drop0 -Hn take_size.
qed.

lemma stx4_bvP (_a: state4x):
 (map
     (fun (temp : bool list) =>
        (Array25.of_list W256.zero (map W256.bits2w (chunk 256 temp)))%Array7)
     (chunk 6400 (flatten [flatten (map W256.w2bits (to_list _a))])))
 = [_a].
proof.
rewrite flatten1 chunk_size 1://= /=.
 rewrite (size_flatten_ctt 256).
  by move=> bs /mapP => [[w [_ ->]]].
 by rewrite size_map size_to_list.
rewrite flattenK 1://.
 move=> bs /mapP [l [Hl ->]].
 by rewrite /w2bits size_mkseq.
by rewrite -map_comp /(\o) /= map_id to_listK.
qed.

lemma X1 st4x:
 Array25.of_list W256.zero
  (map W256.bits2w (chunk 256 (flatten (map W256.w2bits (to_list st4x))))) = st4x.
proof.
rewrite tP => i Hi.
rewrite get_of_list // (nth_map []).
 rewrite size_chunk // (size_flatten' 256);
   1: by  move=> l /mapP [y [Hy ->]]; smt(W256.size_w2bits).
 by rewrite size_map size_to_list /#.
rewrite flattenK //.
 admit.
rewrite (nth_map witness) //.
by rewrite size_to_list.
qed.

lemma X2 (st0 st1 st2 st3:state):
 WArray800.init256
  (fun (i : int) =>
   (Array25.of_list W256.zero
           (map W256.bits2w
              (chunk 256
                 (flatten (map W64.w2bits (to_list st0)) ++
                  (flatten (map W64.w2bits (to_list st1)) ++
                   (flatten (map W64.w2bits (to_list st2)) ++
                    flatten (map W64.w2bits (to_list st3)))))))).[i])
 = WArray800.init64
    (fun i => (Array100.of_list W64.zero (to_list st0++to_list st1++to_list st2++to_list st3)).[i]).
proof.
admitted.

lemma X3 (x: W64.t Array100.t) i:
 0 <= i < 100 =>
 get64
  (WArray800.init64
     (fun (i0 : int) => x.[i0])) i
 = x.[i].
proof.
move=> Hi.
search WArray800.init64.
search WArray800.get64_direct.
rewrite get64E pack8E.
apply W64.ext_eq => k Hk.
rewrite initiE //= initiE 1:/# /= initiE 1:/# /=.
rewrite bits8iE 1:/# /#.
qed.

lemma XX (st0 st1 st2 st3:state) i:
 0 <= i < 100 =>
 get64
  (WArray800.init256
     (fun (i0 : int) =>
        (Array25.of_list W256.zero
           (map W256.bits2w
              (chunk 256
                 (flatten (map W64.w2bits (to_list st0)) ++
                  (flatten (map W64.w2bits (to_list st1)) ++
                   (flatten (map W64.w2bits (to_list st2)) ++
                    flatten (map W64.w2bits (to_list st3)))))))).[i0])) i
 = if i < 25
   then st0.[i]
   else if i < 50
        then st1.[i-25]
        else if i < 75
             then st2.[i-50]
             else st3.[i-75].
proof.
move=> Hi; rewrite X2 X3 // get_of_list // -!catA.
case: (i<25) => C1.
 rewrite nth_cat !size_to_list ifT 1:/#.
 rewrite -get_to_list.
 apply nth_change_dfl.
 by rewrite size_to_list /#.
case: (i<50) => C2.
 rewrite nth_cat !size_to_list ifF 1:/#.
 rewrite nth_cat !size_to_list ifT 1:/#.
 rewrite -get_to_list.
 apply nth_change_dfl.
 by rewrite size_to_list /#.
case: (i<75) => C3.
 rewrite nth_cat !size_to_list ifF 1:/#.
 rewrite nth_cat !size_to_list ifF 1:/#.
 rewrite nth_cat !size_to_list ifT 1:/#.
 rewrite -get_to_list.
 apply nth_change_dfl.
 by rewrite size_to_list /#.
rewrite nth_cat !size_to_list ifF 1:/#.
rewrite nth_cat !size_to_list ifF 1:/#.
rewrite nth_cat !size_to_list ifF 1:/#.
rewrite -get_to_list.
apply nth_change_dfl.
by rewrite size_to_list /#.
qed.



hoare st4x_pack_h _st0 _st1 _st2 _st3:
 Jazz_avx2.M.__st4x_pack:
 st0 = _st0 /\ st1 = _st1 /\ st2 = _st2 /\ st3 = _st3
 ==> res = st4x_pack (_st0, _st1, _st2, _st3).
proof.
proc.
proc change ^while.1: (sliceget256_64_25 st0 (32*i*8));
 1: by auto => /#.
proc change ^while.2: (sliceget256_64_25 st1 (32*i*8));
 1: by auto => /#.
proc change ^while.3: (sliceget256_64_25 st2 (32*i*8));
 1: by auto => /#.
proc change ^while.4: (sliceget256_64_25 st3 (32*i*8));
 1: by auto => /#.
unroll for 2.
proc change 60: (sliceset64_256_25 st4x (8*(4 * 24 + 0)*8) t0);
 1: by auto => /#.
proc change 61: (sliceset64_256_25 st4x (8*(4 * 24 + 1)*8) t1);
 1: by auto => /#.
proc change 62: (sliceset64_256_25 st4x (8*(4 * 24 + 2)*8) t2);
 1: by auto => /#.
proc change 63: (sliceset64_256_25 st4x (8*(4 * 24 + 3)*8) t3);
 1: by auto => /#.
inline*; simplify.
swap 127 8; wp 134.
bdep 6400 6400
     [_st0;_st1;_st2;_st3] [st0;st1;st2;st3] [st4x]
     st4x_pack_spec
     st4x_inv.
+ by move=> &m /> *; rewrite all_predT.
move=> &m /> st4x /=.
rewrite /st4x_pack_spec !flatten_cons flatten_nil !cats0.
rewrite chunk1 //.
 rewrite !size_cat !(size_flatten' 64);
  1..4: by  move=> l /mapP [y [Hy ->]]; smt(W64.size_w2bits).
 by rewrite !size_map !size_iota /#.
rewrite chunk1 //.
 rewrite (size_flatten' 256);
  1: by  move=> l /mapP [y [Hy ->]]; smt(W256.size_w2bits).
 by rewrite !size_map !size_iota /#.
rewrite /= X1 => <-.
rewrite tP => i Hi.
rewrite !initiE //= /st4x_to_4st /=; congr.
+ rewrite !initiE //= /sliceget64_256_25 ifT 1:/#.
  rewrite (:8*i*8 %/ 8=8*i) 1:/# XX /#.
+ rewrite !initiE //= /sliceget64_256_25 ifT 1:/#.
  rewrite (:(200+8*i)*8 %/ 8=8*(25+i)) 1:/# XX /#.
+ rewrite !initiE //= /sliceget64_256_25 ifT 1:/#.
  rewrite (:(400+8*i)*8 %/ 8=8*(50+i)) 1:/# XX /#.
+ rewrite !initiE //= /sliceget64_256_25 ifT 1:/#.
  rewrite (:(600+8*i)*8 %/ 8=8*(75+i)) 1:/# XX /#.
qed.


hoare st4x_unpack_h _st4x:
 Jazz_avx2.M.__st4x_unpack:
 st4x = _st4x
 ==> res = st4x_unpack _st4x.
proof.
proc; simplify.
proc change ^while.6: (sliceset256_64_25 st0 (4*8*i*8) x0);
 1: by auto => /#.
proc change ^while.7: (sliceset256_64_25 st1 (4*8*i*8) x1);
 1: by auto => /#.
proc change ^while.8: (sliceset256_64_25 st2 (4*8*i*8) x2);
 1: by auto => /#.
proc change ^while.9: (sliceset256_64_25 st3 (4*8*i*8) x3);
 1: by auto => /#.
proc change 3: (sliceget64_256_25 st4x (8*(4*24)*8));
 1: by auto => /#.
proc change 4: (sliceget64_256_25 st4x (8*(4*24+1)*8));
 1: by auto => /#.
proc change 5: (sliceget64_256_25 st4x (8*(4*24+2)*8));
 1: by auto => /#.
proc change 6: (sliceget64_256_25 st4x (8*(4*24+3)*8));
 1: by auto => /#.
unroll for 2.
swap 55 8.
wp 62.
inline*.
bdep 6400 6400
     [_st4x] [st4x] [st0;st1;st2;st3]
     st4x_unpack_spec
     st4x_inv.
+ by move=> &m /> *; rewrite all_predT.
move=> &m /> st0 st1 st2 st3 /=.
rewrite /st4x_unpack_spec !flatten_cons flatten_nil !cats0.
rewrite chunk1 //=. admit.
rewrite chunk1 //=. admit.
rewrite chunk1 //=. admit.
admitted.

op st4x_id (x:state4x) = x.
op st4x_id2 (x:state4x) = st4x_from_4st (st4x_to_4st x).

op st_inv (_:state) = true.

module MM = {
 proc ttt1(st4x: state4x): state4x = {
  var st0, st1, st2, st3: state;
  (st0, st1, st2, st3) <@ M.__st4x_unpack(st0, st1, st2, st3, st4x);
  st4x <@ M.__st4x_pack(st4x, st0, st1, st2, st3);
  return st4x;
  }
 proc ttt2(st0 st1 st2 st3: state): state*state*state*state = {
  var st4x: state4x;
  st4x <@ M.__st4x_pack(st4x, st0, st1, st2, st3);
  (st0, st1, st2, st3) <@ M.__st4x_unpack(st0, st1, st2, st3, st4x);
  return (st0,st1,st2,st3);
  }
}.

hoare test1 _st4x:
 MM.ttt1:
 st4x = _st4x
 ==> res = _st4x.
proof.
proc; inline*.
proc change ^while.18: (sliceset256_64_25 st00 (4*8*i*8) x0);
 1: by auto => /#.
proc change ^while.19: (sliceset256_64_25 st10 (4*8*i*8) x1);
 1: by auto => /#.
proc change ^while.20: (sliceset256_64_25 st20 (4*8*i*8) x2);
 1: by auto => /#.
proc change ^while.21: (sliceset256_64_25 st30 (4*8*i*8) x3);
 1: by auto => /#.
proc change 8: (sliceget64_256_25 st4x0 (8*(4*24)*8));
 1: by auto => /#.
proc change 9: (sliceget64_256_25 st4x0 (8*(4*24+1)*8));
 1: by auto => /#.
proc change 10: (sliceget64_256_25 st4x0 (8*(4*24+2)*8));
 1: by auto => /#.
proc change 11: (sliceget64_256_25 st4x0 (8*(4*24+3)*8));
 1: by auto => /#.
unroll for 7.
swap 132 25.
proc change ^while.1: (sliceget256_64_25 st01 (32*i0*8));
 1: by auto => /#.
proc change ^while.2: (sliceget256_64_25 st11 (32*i0*8));
 1: by auto => /#.
proc change ^while.3: (sliceget256_64_25 st21 (32*i0*8));
 1: by auto => /#.
proc change ^while.4: (sliceget256_64_25 st31 (32*i0*8));
 1: by auto => /#.
proc change 152: (sliceset64_256_25 st4x1 (8*(4 * 24 + 0)*8) t00);
 1: by auto => /#.
proc change 153: (sliceset64_256_25 st4x1 (8*(4 * 24 + 1)*8) t10);
 1: by auto => /#.
proc change 154: (sliceset64_256_25 st4x1 (8*(4 * 24 + 2)*8) t20);
 1: by auto => /#.
proc change 155: (sliceset64_256_25 st4x1 (8*(4 * 24 + 3)*8) t30);
 1: by auto => /#.
unroll for 147.
swap 272 9; wp 280.
bdep 6400 6400
     [_st4x] [st4x] [st4x]
     st4x_id2
     st4x_inv.
admitted.

hoare test2 _st0 _st1 _st2 _st3:
 MM.ttt2:
 st0 = _st0 /\ st1 = _st1 /\ st2 = _st2 /\ st3 = _st3 
 ==> res.`1 = _st0
     /\ res.`2 = _st1
     /\ res.`3 = _st2
     /\ res.`4 = _st3.
proof.
proc; inline*; simplify.
proc change ^while.1: (sliceget256_64_25 st00 (32*i*8));
 1: by auto => /#.
proc change ^while.2: (sliceget256_64_25 st10 (32*i*8));
 1: by auto => /#.
proc change ^while.3: (sliceget256_64_25 st20 (32*i*8));
 1: by auto => /#.
proc change ^while.4: (sliceget256_64_25 st30 (32*i*8));
 1: by auto => /#.
proc change 12: (sliceset64_256_25 st4x0 (8*(4 * 24 + 0)*8) t0);
 1: by auto => /#.
proc change 13: (sliceset64_256_25 st4x0 (8*(4 * 24 + 1)*8) t1);
 1: by auto => /#.
proc change 14: (sliceset64_256_25 st4x0 (8*(4 * 24 + 2)*8) t2);
 1: by auto => /#.
proc change 15: (sliceset64_256_25 st4x0 (8*(4 * 24 + 3)*8) t3);
 1: by auto => /#.
unroll for 7.
swap 132 25.
proc change ^while.18: (sliceset256_64_25 st01 (4*8*i0*8) x00);
 1: by auto => /#.
proc change ^while.19: (sliceset256_64_25 st11 (4*8*i0*8) x10);
 1: by auto => /#.
proc change ^while.20: (sliceset256_64_25 st21 (4*8*i0*8) x20);
 1: by auto => /#.
proc change ^while.21: (sliceset256_64_25 st31 (4*8*i0*8) x30);
 1: by auto => /#.
proc change 148: (sliceget64_256_25 st4x1 (8*(4*24)*8));
 1: by auto => /#.
proc change 149: (sliceget64_256_25 st4x1 (8*(4*24+1)*8));
 1: by auto => /#.
proc change 150: (sliceget64_256_25 st4x1 (8*(4*24+2)*8));
 1: by auto => /#.
proc change 151: (sliceget64_256_25 st4x1 (8*(4*24+3)*8));
 1: by auto => /#.
unroll for 147.
swap 272 9; wp 280.
bdep 6400 6400
     [_st0;_st1;_st2;_st3] [st0;st1;st2;st3] [st0;st1;st2;st3]
     st4x_id
     st4x_inv.
admitted.

hoare keccak_pround_avx2x4_h _st0 _st1 _st2 _st3:
 Jazz_avx2.M.__keccakf1600_pround_unpacked:
 st0 = _st0 /\ st1 = _st1 /\ st2 = _st2 /\ st3 = _st3
 ==> res.`1 = keccak_pround_op _st0
     /\ res.`2 = keccak_pround_op _st1
     /\ res.`3 = keccak_pround_op _st2
     /\ res.`4 = keccak_pround_op _st3.
proof.
proc; simplify.
inline __st4x_pack.
proc change ^while.1: (sliceget256_64_25 st00 (32*i*8));
 1: by auto => /#.
proc change ^while.2: (sliceget256_64_25 st10 (32*i*8));
 1: by auto => /#.
proc change ^while.3: (sliceget256_64_25 st20 (32*i*8));
 1: by auto => /#.
proc change ^while.4: (sliceget256_64_25 st30 (32*i*8));
 1: by auto => /#.
proc change 16: (sliceset64_256_25 st4x (8*(4 * 24 + 0)*8) t0);
 1: by auto => /#.
proc change 17: (sliceset64_256_25 st4x (8*(4 * 24 + 1)*8) t1);
 1: by auto => /#.
proc change 18: (sliceset64_256_25 st4x (8*(4 * 24 + 2)*8) t2);
 1: by auto => /#.
proc change 19: (sliceset64_256_25 st4x (8*(4 * 24 + 3)*8) t3);
 1: by auto => /#.
unroll for 11.
swap 64 11; wp 74.
inline __st4x_unpack.
proc change ^while.6: (sliceset256_64_25 st01 (4*8*i0*8) x00);
 1: by auto => /#.
proc change ^while.7: (sliceset256_64_25 st11 (4*8*i0*8) x10);
 1: by auto => /#.
proc change ^while.8: (sliceset256_64_25 st21 (4*8*i0*8) x20);
 1: by auto => /#.
proc change ^while.9: (sliceset256_64_25 st31 (4*8*i0*8) x30);
 1: by auto => /#.
proc change 81: (sliceget64_256_25 st4x0 (8*(4*24)*8));
 1: by auto => /#.
proc change 82: (sliceget64_256_25 st4x0 (8*(4*24+1)*8));
 1: by auto => /#.
proc change 83: (sliceget64_256_25 st4x0 (8*(4*24+2)*8));
 1: by auto => /#.
proc change 84: (sliceget64_256_25 st4x0 (8*(4*24+3)*8));
 1: by auto => /#.
unroll for 80.
swap 133 9; wp 141.
inline*.
admit(*
bdep 1600 1600
     [_st0;_st1;_st2;_st3] [st0;st1;st2;st3] [st0;st1;st2;st3]
     keccak_pround_op
     st_inv.
*).
qed.

print st4x_map.
print st4x_get.

op st4x_keccak_pround =
 st4x_map keccak_pround_op.

hoare keccak_pround_avx2x4_h2 _st4x:
 Jazz_avx2.M.__keccakf1600_4x_pround:
 a_357 = _st4x
 ==> res = st4x_keccak_pround _st4x.
proof.
proc; simplify.
(*
(* não consegue lidar com isto... (grande demais?)*)
bdep 6400 6400
 [_st4x] [a_357] [e_356]
 st4x_keccak_pround st4x_inv.
*)
admitted.





from CryptoSpecs require import FIPS202_Keccakf1600.
print state.

op st00 = init_25_64 (fun _ => W64.zero).
require import Avx2_extra.
op st4x_keccak_pround2 (x:state4x) = 
 init_25_256 (fun _ => u256_pack4 W64.zero W64.zero W64.zero W64.zero).
op st4x_keccak_pround3 (x:state4x) = 
 init_25_256 (fun i => u256_pack4 st00.[i] st00.[i] st00.[i] st00.[i]).
print st4x_map.
print st4x_get.
print u256_bits64.

op srl_256 (w1 w2 : W256.t) : W256.t =
w1 `>>>` to_uint w2.

bind op [W256.t] srl_256 "shr".
realize bvshrP.
rewrite /shr_256 => bv1 bv2.
by rewrite W256.to_uint_shr; 1:smt(W256.to_uint_cmp).
qed.

op sliceget256_64 (a: W256.t) (offset: int) : W64.t =
W4u64.truncateu64 (srl_256 a (W256.of_int offset)).

abbrev u256_bits64' (w : W256.t) (k : int) : W64.t =
sliceget256_64 w (k*64).

print st4x_get.
abbrev st4x_get' (a : state4x) (k : int) : FIPS202_Keccakf1600.state =
  init_25_64 (fun (i : int) => u256_bits64 a.[i] k).
print st4x_map.
abbrev st4x_map2 (f : W64.t Array25.t -> W64.t Array25.t)
  (st4x : W256.t Array25.t) : W256.t Array25.t =
  st4x_pack
    (f (st4x_get' st4x 0), f (st4x_get' st4x 1), f (st4x_get' st4x 2),
     f (st4x_get' st4x 3)).

(*
abbrev st4x_pack (sts : state * state *
  state * state) : state4x =
  init_25_256
    (fun (i : int) => u256_pack4 sts.`1.[i] sts.`2.[i] sts.`3.[i] sts.`4.[i]).
*)
op st4x_keccak_pround4 (x:state4x) = 
 st4x_pack (st4x_get x 0, st4x_get x 0, st4x_get x 0, st4x_get x 0).
op st4x_keccak_pround5 (x:state4x) = 
 st4x_pack (st0,st0,st0,st0).

print keccak_pround_op.

op X_op (x:W64.t Array25.t)= x.
op X0 = st4x_map2 X_op.
op X1 = st4x_map2 keccak_theta_op.
print st4x_pack.
print st4x_map.

hoare keccak_pround_avx2x4_h _a:
 Jazz_avx2_inlined.M._keccakf1600_4x_pround :
 a = _a /\ r8 = rOL8 /\ r56 = rOL56
 ==> res = st4x_keccak_pround2 _a.
proof.
proc.
simplify.
bdep 6400 6400 [_a] [a] [e] st4x_keccak_pround st4x_inv.
print st4x_keccak_pround.
bdep 6400 6400 [_a] [a] [a] X1 st4x_inv.
+ rewrite allP => />.
+ move=> />.
  by rewrite stavx2x4_bvP /stavx2x4_keccak_pround /= => ->.
qed.


(*op stavx2x4_keccak_pround = stF_avx2 keccak_pround_op.*)


(** lemmata (move?) *)

(* add this to JWord, and relax the hyp. in rol_xor_shft accordingly *)
lemma rol_or_shft (w : W64.t) (r : int):
   0 <= r && r < 64 =>
   w `|<<<|` r = (w `<<` (of_int r)%W8) `|` (w `>>` (of_int (64 - r))%W8).
proof.
move => Hr; apply W64.ext_eq => i Hi.
rewrite rolwE Hi /= shlwE Hi /= shrwE Hi /=.
smt(W64.get_out).
qed.


lemma invw_bits64 (w: W256.t) k:
 0 <= k < 4 =>
 invw w \bits64 k = invw (w \bits64 k).
proof. by move=> Hk; rewrite -{1}(unpack64K w) invw64E //. qed.


(******************************************************************************
   Equivalence between lane '_k' and REF1
******************************************************************************)

lemma theta_sum_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.keccakf1600_4x_theta_sum ~ Jazz_ref.M.__theta_sum_ref:
         a{1} \a25bits64 _k = a{2} ==> res{1} \a5bits64 _k = res{2} ].
proof.
move=> Hk; proc.
while (={y} /\ 1<=y{2}<=5 /\ #pre /\
       c{1} \a5bits64 _k = c{2}).
 wp; while (#pre /\ ={x} /\ 0<=x{2}<=5).
  auto => /> &1 &2 Hy1 _ Hy2 Hx1 _ Hx2.
  split.
   rewrite a5bits64iE 1:/# a5bits64_set 1..2:/#.
   by rewrite  a25bits64iE 1:/# xorw_bits64.
  smt().
 auto => />; smt().
wp; while (={x} /\ 0<=x{2}<=5 /\ #pre /\
           forall i, 0<=i<x{2} => (c{1} \a5bits64 _k).[i] = c{2}.[i]).
 auto => /> &1 &2 Hx1 _ H Hx2; split; first smt().
 move=> i Hi1 Hi2.
 case: (i = x{2}) => E.
  rewrite !get_setE 1:/# E /= a5bits64_set 1..2:/#.
  by rewrite get_setE 1:/# /= a25bits64iE 1:/#.
 rewrite get_setE 1:/# E /= -H 1:/# a5bits64_set 1..2:/#.
 by rewrite get_setE 1:/# ifF 1:/#.
auto => />; split; first smt().
move=> cL cR x _?_?; have ->: x=5 by smt().
move=> H; apply Array5.ext_eq => i Hi.
by rewrite -H 1:/#.
qed.

lemma rol8P _x _k:
 0 <= _k < 4 =>
 ((VPSHUFB_256 _x rOL8) \bits64 _k)
 = (_x \bits64 _k) `|<<<|` 8.
proof.
move=> Hk; have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/List.allP; rewrite -iotaredE /=.
rewrite /VPSHUFB_256 /VPSHUFB_128 /VPSHUFB_128_B /=.
rewrite !bits8_red // !of_uintK /=.
by rewrite -!all_eqP /all_eq /=.
qed.

lemma rol56P _x _k:
 0 <= _k < 4 =>
 ((VPSHUFB_256 _x rOL56) \bits64 _k) = (_x \bits64 _k) `|<<<|` 56.
proof.
move=> Hk; have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/List.allP; rewrite -iotaredE /=.
rewrite /VPSHUFB_256 /VPSHUFB_128 /VPSHUFB_128_B /=.
rewrite !bits8_red // !of_uintK /=.
by rewrite -!all_eqP /all_eq /=.
qed.

(* possibly useful if function __rol_4x_avx2 is include in library... 
lemma rol_4x_h _k _x _r:
 0 <= _k < 4 => 
 hoare [ M.__rol_4x_avx2
       : x = _x /\ r = _r%%64 /\ r8 = ROL8 /\ r56 = ROL56
         ==> res \bits64 _k = (_x \bits64 _k) `|<<<|` _r%%64 ].
proof.
move => Hk; proc; simplify.
case: (r=0).
 by rcondf 1; auto => /> ->; rewrite ROL_64_by0.
case: (r=8).
 rcondt 1 => //; rcondt 1 => //.
 by auto => /> *; rewrite rol8P /#.
case: (r=56). 
 rcondt 1 => //; rcondf 1 => //; rcondt 1 => //.
 by auto => /> *; rewrite rol56P /#.
rcondt 1 => //; rcondf 1 => //; rcondf 1 => //.
auto => /> *.
have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/allP; rewrite -iotaredE /=.
rewrite /VPSRL_4u64 /VPSLL_4u64 /=.
smt(W64.orwC rol_or_shft).
qed.

lemma rol_4x_ll: islossless M.__rol_4x_avx2
 by islossless.

lemma rol_4x_ph _k _x _r:
 0 <= _k < 4 => 
 phoare [ M.__rol_4x_avx2
        : x = _x /\ r = _r%%64 /\ r8 = ROL8 /\ r56 = ROL56
          ==> res \bits64 _k = (_x \bits64 _k) `|<<<|` _r%%64 ] = 1%r.
proof. by move=> Hk; conseq rol_4x_ll (rol_4x_h _k _x _r Hk). qed.
*)

(*
lemma rol_4x_eq _a _x _k:
 0 <= _k < 4 =>
 equiv [ M.keccakf1600_4x_rol ~ Jazz_ref.M.__rol_u64_ref:
         a{1}=_a /\ x{1}=_x
         /\ _a.[_x] \bits64 _k = x{2}
         /\ r{1}=i{2} /\ 0 <= i{2} < 64
         /\ r8{1} = rOL8 /\ r56{1} = rOL56
         ==> res{1} =  \bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
if => //.
auto => /> &1 &2 Hi1 Hi2 _; split.
 by move => _; rewrite rol8P // /ROL_64 /shift_mask /=.
move=> _; split.
 by move => _; rewrite rol56P // /ROL_64 /shift_mask /=.
move=> _.
have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
rewrite ROL_64_val modz_small 1:/#.
move: _k; apply/List.allP; rewrite -iotaredE /=.
by rewrite /VPSRL_4u64 /VPSLL_4u64 /=; smt(W64.orwC rol_or_shft).
qed.
*)

lemma theta_rol_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.keccakf1600_4x_theta_rol ~ Jazz_ref.M.__theta_rol_ref:
         c{1} \a5bits64 _k = c{2}
         /\ r8{1} = rOL8
         /\ r56{1} = rOL56
         ==> res{1} \a5bits64 _k = res{2} ].
proof.
(*
move=> Hk; proc; simplify.
while (={x} /\ 0<=x{2}<=5 /\ #pre /\
       forall i, 0<=i<x{2} => (d{1} \a5bits64 _k).[i] = d{2}.[i]).
wp.
 wp; call (rol_4x_eq _k Hk).
 auto => /> &1 &2 Hx1 _ IH Hx2.
 rewrite !get_setE 1..2:/# /=; split.
  by rewrite a5bits64iE 1:/#.
 move=> _ d1; split; first smt().
 move => i Hi1 Hi2.
 case: (i=x{2}) => E.
  rewrite !get_setE 1..3:/# E /=.
  rewrite a5bits64iE 1:/# get_setE 1:/# /=.
  by rewrite a5bits64iE 1:/#.
 rewrite a5bits64iE 1:/#.
 rewrite !get_setE 1..4:/# /= E /=.
 by rewrite -IH 1:/# a5bits64iE 1:/#.
auto => />; split; first smt().
move=> d1 d2 x ?_??; have ->: x=5 by smt().
by move=> H; apply Array5.ext_eq => /#.
*)
admit.
qed.

(*
lemma rol_sum_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__rol_sum_4x_avx2 ~ M.__rol_sum_ref1:
         a{1} \a25bits64 _k = a{2} /\ d{1} \a5bits64 _k = d{2}
         /\ ={y}
         /\ r8{1} = ROL8
         /\ r56{1} = ROL56
         ==> res{1} \a5bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (={x} /\ 0<=x{2}<=5 /\ #pre /\
       forall i, 0<=i<x{2} => (b{1} \a5bits64 _k).[i] = b{2}.[i]).
 wp; call (rol_4x_eq _k); wp.
 ecall {1} (rhotates_spec_ph x_{1} y_{1}).
 ecall {2} (rhotates_spec_ph x_{2} y_{2}).
 auto => /> &1 &2 Hx1 _ IH Hx2; split; first smt().
 move=> _ _; split.
  by rewrite !get_setE 1..4:/# /= a5bits64iE 1:/# a25bits64iE 1:/# -rhotates_idx_mod64 /#.
 move=> *; split; first smt(). 
 move => i Hi1 Hi2.
 case: (i=x{2}) => E.
  rewrite get_setE 1:/# E /=.
  by rewrite a5bits64iE 1:/# get_setE 1:/# /=.
 rewrite a5bits64iE 1:/#.
 rewrite !get_setE 1..2:/# /= E /=.
 by rewrite -IH 1:/# a5bits64iE 1:/#.
auto => />; split; first smt().
move=> bL bR x ?_??; have ->: x=5 by smt().
by move => H; apply Array5.ext_eq => /#.
qed.

lemma set_row_4x_eq _k _y:
 0 <= _k < 4 =>
 equiv [ M.__set_row_4x_avx2 ~ M.__set_row_ref1:
         (forall i, 0 <= i < 5*y{2} => (e{1} \a25bits64 _k).[i] = e{2}.[i])
         /\ b{1} \a5bits64 _k = b{2}
         /\ ={y} /\ y{2}=_y /\ 0 <= _y < 5 /\ rc{1} \bits64 _k = s_rc{2}
         ==> forall i, 0 <= i < 5*(_y+1) => (res{1} \a25bits64 _k).[i] = res{2}.[i] ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ ={x} /\ 0 <= x{2} <= 5 /\
       forall i, 0 <= i < x{2}+y{2}*5 =>
        (e{1} \a25bits64 _k).[i] = e{2}.[i]).
 wp; ecall {2} (ANDN_64_ph b.[x1]{2} b.[x2]{2}).
 auto => /> &1 &2 Hy1 Hy2 H Hx1 _ IH Hx2; split.
  move=> Ex Ey; split; first smt().
  move => i ??; have ->: i=0 by smt().
  rewrite !a25bits64iE 1:/# !a5bits64iE 1..3:/# !get_setE 1..2:/# /=.
  by rewrite invw_bits64 //.
 move=> Exy; split.
  move=> i Hi1 Hi2.
  rewrite a25bits64iE 1:/# !get_setE 1..2:/# !ifF 1..2:/# -IH 1:/#.
  by rewrite a25bits64iE /#.
 split; first smt().
 move=> i Hi1 Hi2.
 case: (i=x{2}+_y*5) => E.
  rewrite get_setE 1:/# E /= a25bits64iE 1:/# !a5bits64iE 1..3:/#.
  by rewrite get_setE 1:/# /= invw_bits64 //.
 rewrite a25bits64iE 1:/# !get_setE 1..2:/# E /= -IH 1:/#.
 by rewrite a25bits64iE /#.
auto => /> &1 &2 H ??; split; first smt().
move=> eL eR x ? _ _ ??; have ->: x=5 by smt().
by move=> IH /#.
qed.

lemma round_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__round_4x_avx2 ~ M.__round_ref1:
         a{1} \a25bits64 _k = a{2}
         /\ rc{1} \bits64 _k = s_rc{2}
         /\ r8{1} = ROL8
         /\ r56{1} = ROL56
         ==> res{1} \a25bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ ={y} /\ 0 <= y{2} <= 5 /\
       d{1} \a5bits64 _k = d{2} /\
       forall i, 0 <= i < 5*y{2} => (e{1}\a25bits64 _k).[i] = e{2}.[i]).
 exlim y{2} => _y.
 wp; call (set_row_4x_eq _k _y Hk).
 call (rol_sum_4x_eq _k Hk).
 by auto => /> /#.
wp; call (theta_rol_4x_eq _k Hk).
call (theta_sum_4x_eq _k Hk); auto => /> &1 &2; split; first smt().
move=> eL eR y ? _ ??; have ->: y=5 by smt().
by move=> H; apply Array25.ext_eq => i Hi /#.
qed.

lemma keccakf1600_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__keccakf1600_4x_avx2 ~ M.__keccakf1600_ref1:
         a{1} \a25bits64 _k = a{2}
         ==> res{1} \a25bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ r8{1}=ROL8 /\ r56{1}=ROL56 /\
       rC{1} \a24bits64 _k = s_RC{2} /\
       to_uint c{1}=32*to_uint c{2} /\
       2 %| to_uint c{2} /\ 2 <= to_uint c{2} <= 24).
 wp; call (round_4x_eq _k Hk).
 wp; call (round_4x_eq _k Hk).
 auto => /> &1 &2; rewrite !ultE !of_uintK /= => Ec Hcdiv Hc1 _ _ Hc2.
 rewrite !Ec; split.
  by rewrite get256_init256 1:/# a24bits64iE /#.
 move => _; split.
  by rewrite (:32*to_uint c{2}+32=32*(to_uint c{2}+1)) 1:/# get256_init256 1:/# a24bits64iE /#.
 by move => _; rewrite !to_uintD_small /#.
wp; call (round_4x_eq _k Hk).
wp; call (round_4x_eq _k Hk).
auto; move: Hk => /> Hk1 Hk2.
have Hk: _k \in iota_ 0 4 by smt(mem_iota).
split.
 rewrite {1}(:0=32*0) // get256_init256 1:/# get_of_list //=.
 by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /= !bits64_red 1..4:/# !of_uintK /=.
move=> _; split.
 rewrite {1}(:32=32*1) // get256_init256 1:/# get_of_list //=.
 by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /= !bits64_red 1..4:/# !of_uintK /=.
move=> _; apply Array24.ext_eq => i Hi.
rewrite a24bits64iE 1://.
have: i\in iota_ 0 24 by smt(mem_iota).
move: {Hi} i; rewrite -allP -iotaredE /= !bits64_red // !of_uintK.
by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /=.
qed.
*)
(******************************************************************************
   Lift lane-equivalence into 4-way parallel execution
******************************************************************************)

lemma map_state4x_neq r a:
 r <> map_state4x keccak_f1600_op a
 <=> (r \a25bits64 0) <> keccak_f1600_op (a \a25bits64 0) \/
     (r \a25bits64 1) <> keccak_f1600_op (a \a25bits64 1) \/
     (r \a25bits64 2) <> keccak_f1600_op (a \a25bits64 2) \/
     (r \a25bits64 3) <> keccak_f1600_op (a \a25bits64 3).
proof.
rewrite /map_state4x eq_sym a25pack4_eq -iotaredE /=.
rewrite !(nth_map st0); first 4 by rewrite /a25unpack4 size_map size_iota.
by rewrite /a25unpack4 -iotaredE /= /#.
qed.

lemma _keccakf1600_avx2x4_ll: islossless M._keccakf1600_avx2x4.
proof.
proc; inline __keccakf1600_avx2x4.
admitted.

hoare _keccakf1600_avx2x4_h (_a: state4x):
 M.__keccakf1600_avx2x4 :
 a = _a
 ==> res = map_state4x keccak_f1600_op _a.
proof.
bypr => &m ->.
have ->:
 Pr[ M.__keccakf1600_avx2x4(_a) @ &m
   : res <> map_state4x keccak_f1600_op _a ]
 = Pr[ M.__keccakf1600_avx2x4(_a) @ &m
     : predU
        (predU 
          (fun r=> r \a25bits64 0 <> keccak_f1600_op (_a \a25bits64 0))
          (fun r=> r \a25bits64 1 <> keccak_f1600_op (_a \a25bits64 1)))
        (predU
          (fun r=> r \a25bits64 2 <> keccak_f1600_op (_a \a25bits64 2))
          (fun r=> r \a25bits64 3 <> keccak_f1600_op (_a \a25bits64 3))) res].
 rewrite Pr [mu_eq] 2:/#.
 by move => &hr; rewrite /predU /= map_state4x_neq /#.
have L: forall (p1 p2: state4x -> bool),
 Pr[ M.__keccakf1600_avx2x4(_a) @ &m
   : predU p1 p2 res ] = 0%r
 <=>
 Pr[ M.__keccakf1600_avx2x4(_a) @ &m
   : p1 res ] = 0%r
 /\ Pr[ M.__keccakf1600_avx2x4(_a) @ &m
      : p2 res ] = 0%r.
 move=> p1 p2; rewrite /predU /=.
 rewrite Pr [mu_or].
 have ?: Pr[M.__keccakf1600_avx2x4(_a) @ &m : p1 res /\ p2 res]
         <= Pr[M.__keccakf1600_avx2x4(_a) @ &m : p1 res ].
  by rewrite Pr [mu_sub] /#.
 have ?: Pr[M.__keccakf1600_avx2x4(_a) @ &m : p1 res /\ p2 res]
         <= Pr[M.__keccakf1600_avx2x4(_a) @ &m : p2 res ].
  by rewrite Pr [mu_sub] /#.
 smt(mu_bounded).
rewrite !L /predU /= => {L}.
have: all (fun k => 
            Pr[ M.__keccakf1600_avx2x4(_a) @ &m
              : res \a25bits64 k <> keccak_f1600_op (_a \a25bits64 k)] = 0%r)
          (iota_ 0 4); last by rewrite -iotaredE /=.
apply/List.allP => k /mem_iota /= Hk.
byphoare (: a = _a ==> _) => //.
hoare; simplify.
(*
conseq (keccakf1600_4x_eq k _) (keccakf1600_ref1_h (_a \a25bits64 k)); last smt().
 move=> />.
 by exists (_a \a25bits64 k) => />.
by move=> />.
*)admit.
qed.

lemma keccakf1600_avx2x4_ll: islossless M._keccakf1600_avx2x4.
proof.
admitted.

hoare keccakf1600_avx2x4_h (_a: state4x):
 M._keccakf1600_avx2x4 :
 a = _a
 ==> res = map_state4x keccak_f1600_op _a.
admitted.
