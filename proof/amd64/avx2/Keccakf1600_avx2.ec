require import AllCore IntDiv List.

from Jasmin require import JModel.


from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600 Keccak1600_arrays.

require import Keccak1600_avx2.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array4 Array5 Array7 Array24 Array25.

require import Avx2_extra.

lemma stavx2_from_st25_iota st rc:
 (stavx2_from_st25 st).[0 <- (stavx2_from_st25 st).[0] `^` VPBROADCAST_4u64 rc]
 = stavx2_from_st25 (st.[0 <- st.[0] `^` rc]).
proof.
apply Array7.ext_eq => i Hi.
rewrite get_setE 1://.
case: (i=0) => [->|E].
 rewrite /stavx2_from_st25 !u256_pack4E !get_of_list 1..2://= /=.
 rewrite /VPBROADCAST_4u64 xorb4u64E /=; congr.
 apply W4u64.Pack.all_eq_eq.
 by rewrite /all_eq /= !nth_mapN2 1..4:// /= -iotaredE /=.
 rewrite /stavx2_from_st25 !get_of_list 1..2:// /= /#.
qed.

lemma stavx2INV_iota st w:
 stavx2INV st =>
 u256_broadcastP w =>
 stavx2INV st.[0 <- st.[0] `^` w].
proof.
move=> Hinv Hb.
rewrite /stavx2INV get_setE 1:// /=.
by apply u256_broadcastP_xor.
qed.

op stavx2_keccak_pround = stF_avx2 keccak_pround_op.

abbrev keccak_round_i i st =
 foldl (fun s i => keccak_round_op rc_spec.[i] s) st (iota_ 0 i).

import BitEncoding BitChunking.

lemma stavx2_bvP (_a: W256.t Array7.t):
 (map
     (fun (temp : bool list) =>
        (of_list W256.zero (map W256.bits2w (chunk 256 temp)))%Array7)
     (chunk 1792 (flatten [flatten (map W256.w2bits (to_list _a))])))
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

(** Actual correctness proof *)

lemma keccakf1600_pround_avx2_ll: islossless M.__keccakf1600_pround_avx2 
by islossless.


hoare keccak_pround_avx2_h _a:
 M.__keccakf1600_pround_avx2 :
 state = _a /\ stavx2INV _a ==> res = stavx2_keccak_pround _a.
proof.
proc.
circuit.
(*
bdep 1792 1792 [_a] [state] [state] stavx2_keccak_pround stavx2INV.
+ move=> |> Hinv.
  rewrite stavx2_bvP allP => l.
  by rewrite mem_seq1.
move => |> Hinv st.
by rewrite !stavx2_bvP /=.
*)
qed.

lemma keccakf1600_avx2_ll': islossless M.__keccakf1600_avx2.
proof.
proc.
wp; while (true) (24-r).
 by move=> z; wp; call keccakf1600_pround_avx2_ll; auto => /> &m H /#.
by wp; call keccakf1600_pround_avx2_ll; auto => /> r H /#.
qed.

hoare keccakf1600_avx2_h' _a:
 M.__keccakf1600_avx2 :
 state = _a /\ stavx2INV _a 
 ==> res = stavx2_from_st25 (keccak_f1600_op (stavx2_to_st25 _a)).
proof.
proc.
wp; while (0 < r <= 24 /\
           round_constants = rc_spec /\
           stavx2INV state /\
           state = stavx2_from_st25 (keccak_round_i r (stavx2_to_st25 _a))).
 wp; ecall (keccak_pround_avx2_h state); auto => |> &m ? _.
 rewrite !stavx2INV_from_st25 /= => Hr; split; first smt().
 rewrite -andaE; split.
  rewrite stavx2INV_iota.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 move=> Hinv; rewrite iotaSr /= 1:/#. 
 rewrite foldl_rcons /stavx2_keccak_pround /=. 
 pose st:= foldl _ _ _.
 rewrite !stavx2_from_st25K stavx2_from_st25_iota; congr.
 by rewrite/keccak_round_op /keccak_iota_op.
wp; ecall (keccak_pround_avx2_h state); auto => |> stINV.
split.
 rewrite stavx2INV_iota /=.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 rewrite /= /stavx2_keccak_pround /keccak_round_op /keccak_iota_op iota1 /=.
 by rewrite stavx2_from_st25_iota get_of_list //.
move => r ???; have ->: r = 24 by smt().
smt().
qed.

phoare keccakf1600_avx2_ph' _a:
 [ M.__keccakf1600_avx2 :
 state = _a /\ stavx2INV _a 
 ==> res = stavx2_from_st25 (keccak_f1600_op (stavx2_to_st25 _a))
 ] = 1%r.
proof. by conseq keccakf1600_avx2_ll' (keccakf1600_avx2_h' _a). qed.

lemma keccakf1600_avx2_ll: islossless M._keccakf1600_avx2.
proof. by proc; call keccakf1600_avx2_ll'. qed.

hoare keccakf1600_avx2_h _a:
 M._keccakf1600_avx2 :
 state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a).
proof.
proc.
ecall (keccakf1600_avx2_h' state); auto => |>; split.
 by rewrite stavx2INV_from_st25.
by move=> ?; rewrite stavx2_from_st25K.
qed.

(* FINAL CORRECTNESS THEOREM *)
phoare keccakf1600_avx2_ph _a:
 [ M._keccakf1600_avx2 :
 state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a)
 ] = 1%r.
proof. by conseq keccakf1600_avx2_ll (keccakf1600_avx2_h _a). qed.


lemma stavx2_pack_ll: islossless M.__stavx2_pack by islossless.


from JazzEC require import WArray200.

op sliceget25_64_256 (st: W64.t Array25.t) (offset: int) : W256.t = 
 if 8 %| offset
 then
  WArray200.get256_direct (WArray200.init64 (fun i => st.[i])) (offset %/ 8)
 else W256.bits2w (take 256 (drop offset (flatten (map W64.w2bits (to_list st))))).

bind op [W64.t & W256.t & Array25.t] sliceget25_64_256 "asliceget".
realize le_size by done.
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget25_64_256 /= => H k kb. 
case (8%| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 64 _). 
+ rewrite allP => x /=; rewrite mapP => He; elim He;smt(W64.size_w2bits).
rewrite (nth_map W64.zero []); 1: smt(Array25.size_to_list).
by rewrite nth_mkseq 1:/# /= bits8E /= initiE /# /=.
qed.

hoare stavx2_pack_h _st:
 M.__stavx2_pack
 : st=_st ==> res = stavx2_from_st25 _st.
proof.
proc.
proc change 2: { state <- state.[0 <- VPBROADCAST_4u64 st.[0]]; }.
 auto => /> &m; congr; congr.
 rewrite get64E pack8E.
 apply W64.ext_eq => i Hi /=.
 by rewrite initiE //= initiE 1:/# initiE 1:/# /= bits8E initiE 1:/# /= /#.
proc change 3: { state <- state.[1 <- sliceget25_64_256 st (1*8*8)]; };
 1: by auto => /#.
proc change 5: { state <- state.[3 <- sliceget25_64_256 st (6*8*8)]; };
 1: by auto => /#.
proc change 7: { state <- state.[4 <- sliceget25_64_256 st (11*8*8)]; };
 1: by auto => /#.
proc change 10: { state <- state.[5 <- sliceget25_64_256 st (16*8*8)]; };
 1: by auto => /#.
proc change 14: { state <- state.[6 <- sliceget25_64_256 st (21*8*8)]; };
 1: by auto => /#.
admit (* ?????
circuit.

tentativas de tornear/perceber problema...
proc change 4: { t128_0 <- W2u64.zeroextu128 st.[5]; }.
 admit.
proc change 6: { t128_1 <- W2u64.zeroextu128 st.[10]; }.
 admit.
circuit.

*).
qed.

phoare stavx2_pack_ph _st:
 [ M.__stavx2_pack
 : st=_st ==> res = stavx2_from_st25 _st
 ] = 1%r.
proof. by conseq stavx2_pack_ll (stavx2_pack_h _st). qed.

lemma stavx2_unpack_ll: islossless M.__stavx2_unpack by islossless.

op sliceset25_64_256 (st: W64.t Array25.t) (offset: int) (bv: W256.t) : W64.t Array25.t =
 if 8%| offset
 then
  stwords
   (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (offset %/ 8) bv)
 else
   Array25.of_list
    witness
    (map W64.bits2w (chunk 64 (take offset (flatten (map W64.w2bits (to_list st)))
     ++ w2bits bv
     ++ drop (offset + 256) (flatten (map W64.w2bits (to_list st)))))).

lemma size_flatten_W64_w2bits (a : W64.t list) :
  (size (flatten (map W64.w2bits (a))))  =  64 * size a.
proof.
  rewrite size_flatten -map_comp /(\o) /=.
  rewrite StdBigop.Bigint.sumzE /= StdBigop.Bigint.BIA.big_mapT /(\o) /=. 
  rewrite StdBigop.Bigint.big_constz count_predT /#.
qed.

bind op [W64.t & W256.t & Array25.t] sliceset25_64_256 "asliceset".
realize le_size by done.
realize bvaslicesetP.
move => arr offset bv H /= k kb; rewrite /sliceset25_64_256 /=. 
case (8 %| offset) => /= *; last first.
+ rewrite of_listK.
   rewrite size_map size_chunk 1:// !size_cat size_take. smt().
    rewrite size_flatten_W64_w2bits size_to_list size_w2bits /= ifT 1:/#.
    by rewrite size_drop 1:/# size_flatten_W64_w2bits size_to_list /#.
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
 

hoare stavx2_unpack_h _st:
 M.__stavx2_unpack
 : state=_st ==> res = stavx2_to_st25 _st.
proof.
proc.
proc change 3: { st <- sliceset25_64_256 st (1*8*8) state.[1]; };
 1: by auto => /#.
proc change 11: { st <- sliceset25_64_256 st (6*8*8) t256_4; };
 1: by auto => /#.
proc change 15: { st <- sliceset25_64_256 st (11*8*8) t256_4; };
 1: by auto => /#.
proc change 18: { st <- sliceset25_64_256 st (16*8*8) t256_4; };
 1: by auto => /#.
proc change 21: { st <- sliceset25_64_256 st (21*8*8) t256_4; };
 1: by auto => /#.
admit (* ??? Exception thrown: EcLib.EcCircuits.MissingOpBody
circuit.
*).
qed.

phoare stavx2_unpack_ph _st:
 [ M.__stavx2_unpack
 : state=_st ==> res = stavx2_to_st25 _st
 ] = 1%r.
proof. by conseq stavx2_unpack_ll (stavx2_unpack_h _st). qed.

lemma keccakf1600_st25_avx2_ll: islossless M._keccakf1600_st25_avx2.
proof.
proc.
call stavx2_unpack_ll.
call keccakf1600_avx2_ll'.
by call stavx2_pack_ll; auto.
qed.

hoare keccakf1600_st25_avx2_h _a:
 M._keccakf1600_st25_avx2 :
 st25=_a ==> res = keccak_f1600_op _a.
proof.
proc.
ecall (stavx2_unpack_h state).
ecall (keccakf1600_avx2_h' state).
ecall (stavx2_pack_h st25).
auto => |>; split => *.
 by rewrite stavx2INV_from_st25.
by rewrite !stavx2_from_st25K.
qed.

phoare keccakf1600_st25_avx2_ph _a:
 [ M._keccakf1600_st25_avx2 :
 st25=_a ==> res = keccak_f1600_op _a
 ] = 1%r.
proof. by conseq keccakf1600_st25_avx2_ll (keccakf1600_st25_avx2_h _a). qed.

