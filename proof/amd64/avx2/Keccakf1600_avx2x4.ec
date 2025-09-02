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


