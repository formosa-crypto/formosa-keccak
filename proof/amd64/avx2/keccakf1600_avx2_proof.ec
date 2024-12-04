require import AllCore IntDiv List.
from Jasmin require import JModel.
require import Array4 Array5 Array7 Array24 Array25.

from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Bindings.

(***************************************************************)
(***************************************************************)
(* Circuit-friendly versions of the functional spec            *)
(***************************************************************)

abbrev idx (xy: int*int): int = (xy.`1 %% 5) + (5 * (xy.`2 %% 5)).
abbrev invidx (i : int) : int * int = (i %% 5, i %/ 5).

op keccakC (A: W64.t Array25.t) : W64.t Array5.t =
 init_5_64 (fun x => A.[x + 5 * 0] `^` A.[x + 5 * 1] `^` A.[x + 5 * 2] `^` A.[x + 5 * 3] `^` A.[x + 5 * 4]).

lemma keccakCE st:
 keccakC st = keccak_C st.
proof. by rewrite /keccakC /init_5_64 /keccak_C; congr. qed.

op keccakD (C: W64.t Array5.t) : W64.t Array5.t =
 init_5_64 (fun x => C.[(x - 1) %% 5] `^` (rol_64 C.[(x + 1) %% 5] (W64.of_int 1))).

lemma keccakDE st:
 keccakD st = keccak_D st.
proof. by rewrite /keccakD /init_5_64 /keccak_D; congr. qed.

op keccak_theta (A: W64.t Array25.t) : W64.t Array25.t =
 init_25_64 (fun i => A.[i] `^` (keccakD (keccakC A)).[i %% 5]).

lemma keccak_thetaE st:
 keccak_theta st = keccak_theta_op st.
proof.
by rewrite /keccak_theta /init_25_64 /keccak_theta_op keccakCE keccakDE.
qed.

op keccak_rho (A: W64.t Array25.t) : W64.t Array25.t =
 init_25_64 (fun i => rol_64 A.[i] (W64.of_int rhotates.[i])).

lemma keccak_rhoE st:
 keccak_rho st = keccak_rho_op st.
proof.
rewrite /keccak_rho /init_25_64 /keccak_rho_op.
apply Array25.all_eq_eq; rewrite /all_eq => /=.
by rewrite !get_of_list //.
qed.

op keccak_pi (A: W64.t Array25.t) : W64.t Array25.t =
 init_25_64 (fun i => let (x, y) = invidx i in A.[idx (x + 3 * y, x)]).

lemma keccak_piE st:
 keccak_pi st = keccak_pi_op st.
proof. rewrite /keccak_pi /init_25_64 /keccak_pi_op /#. qed.

op keccak_chi (A: W64.t Array25.t) : W64.t Array25.t =
 init_25_64 (fun i => let (x, y) = invidx i in A.[idx (x, y)] `^` (invw A.[idx (x + 1, y)] `&` A.[idx (x + 2, y)])).

lemma keccak_chiE st:
 keccak_chi st = keccak_chi_op st.
proof. by rewrite /keccak_chi /init_25_64 /keccak_chi_op /#. qed.

op keccak_pround (A : W64.t Array25.t) : W64.t Array25.t =
 keccak_chi (keccak_pi (keccak_rho (keccak_theta A))).

lemma keccak_proundE st:
 keccak_pround st
 = keccak_chi_op (keccak_pi_op (keccak_rho_op (keccak_theta_op st))).
proof.
by rewrite /keccak_pround keccak_chiE keccak_piE keccak_rhoE keccak_thetaE.
qed.


(* circuit-friendly state mappings *)

abbrev u256_bits64 (w: W256.t) k : W64.t =
 W64.init (fun i => w.[i+64*k]).

lemma u256_bits64E w k:
 0 <= k < 4 =>
 u256_bits64 w k = w \bits64 k.
proof.
move=> Hk; rewrite /u256_bits64.
apply W64.ext_eq => i Hi.
by rewrite bits64E initiE 1://= initiE 1://= /#.
qed.

op u256_pack4 (w0 w1 w2 w3: W64.t): W256.t =
 W256.init (fun i => if i < 64 then w0.[i]
                     else if i < 128 then w1.[i-64]
                     else if i < 192 then w2.[i-128]
                     else w3.[i-192]).


lemma u256_pack4E w0 w1 w2 w3:
 u256_pack4 w0 w1 w2 w3 = pack4 [w0; w1; w2; w3].
proof.
rewrite /u256_pack4; apply W256.ext_eq => k Hk.
rewrite initiE 1:// pack4E initiE 1:// /=.
rewrite get_of_list 1:/# /=.
case: (k < 64) => C1.
 by rewrite ifT 1:/# modz_small /= /#.
case: (k < 128) => C2.
 by rewrite ifF 1:/# ifT 1:/#; congr; smt().
case: (k < 192) => C3.
 by rewrite ifF 1:/# ifF 1:/# ifT 1:/#; congr; smt().
by rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#; congr => /#.
qed.

op stavx2_from_st25 (st: W64.t Array25.t): W256.t Array7.t =
 Array7.of_list W256.zero
  [ u256_pack4 st.[ 0] st.[ 0] st.[ 0] st.[ 0]
  ; u256_pack4 st.[ 1] st.[ 2] st.[ 3] st.[ 4]
  ; u256_pack4 st.[10] st.[20] st.[ 5] st.[15]
  ; u256_pack4 st.[16] st.[ 7] st.[23] st.[14]
  ; u256_pack4 st.[11] st.[22] st.[ 8] st.[19]
  ; u256_pack4 st.[21] st.[17] st.[13] st.[ 9]
  ; u256_pack4 st.[ 6] st.[12] st.[18] st.[24]
  ].

op stavx2_to_st25 (st: W256.t Array7.t): W64.t Array25.t =
 Array25.of_list W64.zero
  [ u256_bits64 st.[0] 0; u256_bits64 st.[1] 0; u256_bits64 st.[1] 1; u256_bits64 st.[1] 2; u256_bits64 st.[1] 3
  ; u256_bits64 st.[2] 2; u256_bits64 st.[6] 0; u256_bits64 st.[3] 1; u256_bits64 st.[4] 2; u256_bits64 st.[5] 3
  ; u256_bits64 st.[2] 0; u256_bits64 st.[4] 0; u256_bits64 st.[6] 1; u256_bits64 st.[5] 2; u256_bits64 st.[3] 3
  ; u256_bits64 st.[2] 3; u256_bits64 st.[3] 0; u256_bits64 st.[5] 1; u256_bits64 st.[6] 2; u256_bits64 st.[4] 3
  ; u256_bits64 st.[2] 1; u256_bits64 st.[5] 0; u256_bits64 st.[4] 1; u256_bits64 st.[3] 2; u256_bits64 st.[6] 3
  ].

lemma stavx2_from_st25K st:
 stavx2_to_st25 (stavx2_from_st25 st) = st.
proof.
rewrite /stavx2_to_st25 /stavx2_from_st25 !u256_bits64E 1..25:// /=.
rewrite !u256_pack4E /=.
by apply Array25.all_eq_eq; rewrite /all_eq.
qed.

op u256_broadcastP w =
 u256_bits64 w 1 = u256_bits64 w 0
 /\ u256_bits64 w 2 = u256_bits64 w 0
 /\ u256_bits64 w 3 = u256_bits64 w 0.

lemma u256_broadcastP_VPBROADCAST w:
 u256_broadcastP (VPBROADCAST_4u64 w).
proof.
rewrite /VPBROADCAST_4u64 /u256_broadcastP.
by rewrite !u256_bits64E 1..4:// !pack4bE 1..4:// /= -iotaredE /=.
qed.

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

lemma u256_broadcastP_xor w1 w2:
 u256_broadcastP w1 =>
 u256_broadcastP w2 =>
 u256_broadcastP (w1 `^` w2).
proof.
by rewrite /u256_broadcastP !u256_bits64E 1..12:// !xorb64E /#.
qed.

op stavx2INV (st: W256.t Array7.t): bool =
 u256_broadcastP st.[0].

lemma stavx2INV_iota st w:
 stavx2INV st =>
 u256_broadcastP w =>
 stavx2INV st.[0 <- st.[0] `^` w].
proof.
move=> Hinv Hb.
rewrite /stavx2INV get_setE 1:// /=.
by apply u256_broadcastP_xor.
qed.

lemma stavx2INV_from_st25 st:
 stavx2INV (stavx2_from_st25 st).
proof.
by rewrite /stavx2INV /u256_broadcastP !initiE 1:// !u256_bits64E 1..4://= /= !u256_pack4E pack4bE //.
qed.

abbrev stF_avx2 f = fun st => stavx2_from_st25 (f (stavx2_to_st25 st)).

op stavx2_keccak_pround = stF_avx2 keccak_pround.

op stavx2_keccakf1600 = stF_avx2 keccak_f1600_op.

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

require import Keccakf1600_avx2.

hoare keccak_pround_avx2_h _a:
 M.__keccakf1600_pround_avx2 :
 state = _a /\ stavx2INV _a ==> res = stavx2_keccak_pround _a.
proof.
proc.
bdep 1792 1792 [_a] [state] [state] stavx2_keccak_pround stavx2INV.
+ move=> |> Hinv.
  rewrite stavx2_bvP allP => l.
  by rewrite mem_seq1.
move => |> Hinv st.
by rewrite !stavx2_bvP /=.
qed.

hoare keccakf1600_avx2_h _a:
 M._keccakf1600_avx2 :
 state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a).
proof.
proc.
while (to_uint r <= 24 /\
       round_constants = rc_spec /\
       stavx2INV state /\
       state = stavx2_from_st25 (keccak_round_i (to_uint r) _a)).
 wp; ecall (keccak_pround_avx2_h state); auto => |> &m _.
 rewrite ultE !stavx2INV_from_st25 /= => Hr; split.
  by rewrite to_uintD_small /= /#.
 rewrite -andaE; split.
  rewrite stavx2INV_iota.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 move=> Hinv; rewrite to_uintD_small /= 1:/# iotaSr /=.
  smt(W64.to_uint_cmp).
 rewrite foldl_rcons /stavx2_keccak_pround /=. 
 pose st:= foldl _ _ _.
 rewrite !stavx2_from_st25K stavx2_from_st25_iota; congr.
 by rewrite keccak_proundE /keccak_round_op /keccak_iota_op.
wp; ecall (keccak_pround_avx2_h state); auto => |>.
rewrite !stavx2INV_from_st25 /=; split.
 rewrite stavx2INV_iota.
   by rewrite /stavx2_keccak_pround stavx2INV_from_st25.
  by rewrite u256_broadcastP_VPBROADCAST.
 rewrite /=.
 rewrite /stavx2_keccak_pround !stavx2_from_st25K keccak_proundE /keccak_round_op /keccak_iota_op iota1 /=.
 by rewrite stavx2_from_st25_iota get_of_list //.
move => r; rewrite ultE /= => ??; have ->:to_uint r = 24 by smt().
smt().
qed.

lemma keccakf1600_pround_avx2_ll: islossless M.__keccakf1600_pround_avx2 
by islossless.

lemma keccakf1600_avx2_ll: islossless M._keccakf1600_avx2.
proof.
proc.
while (true) (24-to_uint r).
 move=> z; wp; call keccakf1600_pround_avx2_ll; auto => /> &m.
 by rewrite ultE of_uintK /= => H; rewrite to_uintD_small !to_uint1 /#.
wp; call keccakf1600_pround_avx2_ll; auto => /> r H.
by rewrite ultE /= /#.
qed.

(* FINAL CORRECTNESS THEOREM *)
phoare keccakf1600_avx2_ph _a:
 [ M._keccakf1600_avx2
 : state = stavx2_from_st25 _a ==> res = stavx2_from_st25 (keccak_f1600_op _a)
 ] = 1%r.
proof. by conseq keccakf1600_avx2_ll (keccakf1600_avx2_h _a). qed.

