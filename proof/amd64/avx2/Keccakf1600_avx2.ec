require import AllCore IntDiv List.

from Jasmin require import JModel.


from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
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

hoare keccak_pround_avx2_h _a:
 M.__keccakf1600_pround_avx2 :
 state = _a /\ stavx2INV _a ==> res = stavx2_keccak_pround _a.
proof.
(*
proc.
time
bdep 1792 1792 [_a] [state] [state] stavx2_keccak_pround stavx2INV.
+ move=> |> Hinv.
  rewrite stavx2_bvP allP => l.
  by rewrite mem_seq1.
move => |> Hinv st.
by rewrite !stavx2_bvP /=.
*) admit.
qed.

hoare keccakf1600_avx2_h _a:
 M._keccakf1600_avx2 :
 state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a).
proof.
proc; inline 1.
wp; while (0 < r <= 24 /\
           round_constants = rc_spec /\
           stavx2INV state0 /\
           state0 = stavx2_from_st25 (keccak_round_i r _a)).
 wp; ecall (keccak_pround_avx2_h state0); auto => |> &m ? _.
 rewrite !stavx2INV_from_st25 /= => Hr; split; first smt().
 rewrite -andaE; split.
  rewrite stavx2INV_iota.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 move=> Hinv; rewrite (*/=. 1:/#*) iotaSr /= 1:/#. 
 rewrite foldl_rcons /stavx2_keccak_pround /=. 
 pose st:= foldl _ _ _.
 rewrite !stavx2_from_st25K stavx2_from_st25_iota; congr.
 by rewrite/keccak_round_op /keccak_iota_op.
wp; ecall (keccak_pround_avx2_h state); auto => |>.
rewrite !stavx2INV_from_st25 /=; split.
 rewrite stavx2INV_iota.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 rewrite /= /stavx2_keccak_pround !stavx2_from_st25K /keccak_round_op /keccak_iota_op iota1 /=.
 by rewrite stavx2_from_st25_iota get_of_list //.
move => r ???; have ->: r = 24 by smt().
smt().
qed.

lemma keccakf1600_pround_avx2_ll: islossless M.__keccakf1600_pround_avx2 
by islossless.

lemma keccakf1600_avx2_ll: islossless M._keccakf1600_avx2.
proof.
proc; inline 1.
wp; while (true) (24-r).
 by move=> z; wp; call keccakf1600_pround_avx2_ll; auto => /> &m H /#.
by wp; call keccakf1600_pround_avx2_ll; auto => /> r H /#.
qed.

(* FINAL CORRECTNESS THEOREM *)
phoare keccakf1600_avx2_ph _a:
 [ M._keccakf1600_avx2
 : state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a)
 ] = 1%r.
proof. by conseq keccakf1600_avx2_ll (keccakf1600_avx2_h _a). qed.

