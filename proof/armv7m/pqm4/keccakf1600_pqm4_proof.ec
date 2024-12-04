require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_m4.

import SLH32.

require import Array4 Array5 Array8 Array48 Array24 Array25 Array50.

require import QFABV Bindings.

require import Keccakf1600_pqm4_inlined.

abbrev kECCAK1600_RC =
(Array24.of_list W64.zero
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

abbrev keccakF1600_StatePermute_RoundConstantsWithTerminator =
(Array48.of_list W32.zero
[(W32.of_int 1); (W32.of_int 0); (W32.of_int 0); (W32.of_int 137);
(W32.of_int 0); (W32.of_int (-2147483509)); (W32.of_int 0);
(W32.of_int (-2147450752)); (W32.of_int 1); (W32.of_int 139); (W32.of_int 1);
(W32.of_int 32768); (W32.of_int 1); (W32.of_int (-2147450744));
(W32.of_int 1); (W32.of_int (-2147483518)); (W32.of_int 0); (W32.of_int 11);
(W32.of_int 0); (W32.of_int 10); (W32.of_int 1); (W32.of_int 32898);
(W32.of_int 0); (W32.of_int 32771); (W32.of_int 1); (W32.of_int 32907);
(W32.of_int 1); (W32.of_int (-2147483637)); (W32.of_int 1);
(W32.of_int (-2147483510)); (W32.of_int 1); (W32.of_int (-2147483519));
(W32.of_int 0); (W32.of_int (-2147483519)); (W32.of_int 0);
(W32.of_int (-2147483640)); (W32.of_int 0); (W32.of_int 131); (W32.of_int 0);
(W32.of_int (-2147450877)); (W32.of_int 1); (W32.of_int (-2147450744));
(W32.of_int 0); (W32.of_int (-2147483512)); (W32.of_int 1);
(W32.of_int 32768); (W32.of_int 0); (W32.of_int (-2147450750))]).

op u64_deinterleave (x: W64.t): W32.t * W32.t =
  (W32.init (fun i => x.[2*i]), W32.init (fun i => x.[2*i+1])).

op u32s_interleave (x y: W32.t) =
  W64.init (fun i => if i%%2=0 then x.[i%/2] else y.[i%/2]).


op pqm4_RC (rc: W64.t Array24.t): W32.t Array48.t =
 init_48_32 (fun i => let xy = u64_deinterleave rc.[i%/2]
                      in if i%%2=0 then xy.`1 else xy.`2).

op pqm4_RC_pT (_: W32.t Array48.t)= true.

lemma pqmRC_P:
 keccakF1600_StatePermute_RoundConstantsWithTerminator
 = pqm4_RC kECCAK1600_RC.
proof.

rewrite /pqm4_RC; apply Array48.all_eq_eq.
rewrite /all_eq /init_48_32 /u64_deinterleave /=.
admit(*
by do ! split; apply W32.all_eq_eq; rewrite /all_eq !of_intE /int2bs /mkseq -iotaredE /=.
*).
qed.


op stateTopqm4_op (state:W64.t Array25.t) : W32.t Array50.t =
  init_50_32 (fun i => let xy = u64_deinterleave state.[i%/2]
                       in if i%%2=0 then xy.`1 else xy.`2).

op pqm4Tostate_op (state:W32.t Array50.t) : W64.t Array25.t =
  init_25_64 (fun i => u32s_interleave state.[2*i] state.[2*i+1]).



(***************************************************************)
(***************************************************************)
(* Circuit-friendly versions of the functional spec            *)
(***************************************************************)

from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

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

op keccak_round rc (A : W64.t Array25.t) : W64.t Array25.t =
 keccak_iota_op rc (keccak_chi (keccak_pi (keccak_rho (keccak_theta A)))).

lemma keccak_roundE A rc:
 keccak_round rc A = keccak_round_op rc A.
proof.
by rewrite /keccak_round keccak_chiE keccak_piE keccak_rhoE keccak_thetaE.
qed.

op keccak_4rounds (rc: W64.t Array4.t) A =
 keccak_round rc.[3] (keccak_round rc.[2] (keccak_round rc.[1] (keccak_round rc.[0] A))).

(* OBS: cannot use [foldl] neither [Array24.map] *)
abbrev rc_spec' = Array24.of_list witness 
 [ W64.of_int 1
 ; W64.of_int 32898
 ; W64.of_int 9223372036854808714
 ; W64.of_int 9223372039002292224
 ; W64.of_int 32907
 ; W64.of_int  2147483649
 ; W64.of_int 9223372039002292353
 ; W64.of_int 9223372036854808585
 ; W64.of_int 138; W64.of_int 136
 ; W64.of_int 2147516425
 ; W64.of_int 2147483658
 ; W64.of_int 2147516555
 ; W64.of_int 9223372036854775947
 ; W64.of_int 9223372036854808713
 ; W64.of_int 9223372036854808579
 ; W64.of_int 9223372036854808578
 ; W64.of_int 9223372036854775936
 ; W64.of_int 32778
 ; W64.of_int 9223372039002259466
 ; W64.of_int 9223372039002292353
 ; W64.of_int 9223372036854808704
 ; W64.of_int 2147483649
 ; W64.of_int 9223372039002292232].

lemma rc_specE: rc_spec' = rc_spec by smt().

abbrev keccak_f1600 (A: state) =
 keccak_round rc_spec'.[23]
  (keccak_round rc_spec'.[22]
   (keccak_round rc_spec'.[21]
    (keccak_round rc_spec'.[20]
     (keccak_round rc_spec'.[19]
      (keccak_round rc_spec'.[18]
       (keccak_round rc_spec'.[17]
        (keccak_round rc_spec'.[16]
         (keccak_round rc_spec'.[15]
          (keccak_round rc_spec'.[14]
           (keccak_round rc_spec'.[13]
            (keccak_round rc_spec'.[12]
             (keccak_round rc_spec'.[11]
              (keccak_round rc_spec'.[10]
               (keccak_round rc_spec'.[9]
                (keccak_round rc_spec'.[8]
                 (keccak_round rc_spec'.[7]
                  (keccak_round rc_spec'.[6]
                   (keccak_round rc_spec'.[5]
                    (keccak_round rc_spec'.[4]
                     (keccak_round rc_spec'.[3]
                      (keccak_round rc_spec'.[2]
                       (keccak_round rc_spec'.[1]
                        (keccak_round rc_spec'.[0] A
                        ))))))))))))))))))))))).

lemma keccak_f1600E A: keccak_f1600 A = keccak_f1600_op A.
proof.
by rewrite /keccak_f1600 !keccak_roundE /keccak_f1600_op -rc_specE -iotaredE.
qed.

(* For use with just 4 rounds (not working currently)
   [1600 + 8*32 = 1856 wires]
 *)
op rcToline (rc: W64.t Array4.t): W32.t Array8.t =
 init_8_32 (fun i => let xy = u64_deinterleave rc.[i%/2]
                     in if i%%2=0 then xy.`1 else xy.`2).
op rcFromline (line: W32.t Array8.t): W64.t Array4.t =
 init_4_64 (fun i => u32s_interleave line.[2*i] line.[2*i+1]).
op pqm4rounds_spec (Arc: _*_) =
 stateTopqm4_op (keccak_4rounds (rcFromline Arc.`2) (pqm4Tostate_op Arc.`1)).
op pqm4rounds_pre (_: W32.t Array50.t * W32.t Array8.t) = true.

(* Full keccak permutation (working now) *)
op pqm4permutation_spec A =
 stateTopqm4_op (keccak_f1600 (pqm4Tostate_op A)).
op pqm4permutation_pre (_: W32.t Array50.t) = true.

import BitEncoding BitChunking.
lemma bdep_auxP (_a: W32.t Array50.t):
 (map
     (fun (temp : bool list) =>
        (Array50.of_list W32.zero (map W32.bits2w (chunk 32 temp)))%Array7)
     (chunk 1600 (flatten [flatten (map W32.w2bits (to_list _a))])))
 = [_a].
proof.
rewrite flatten1 chunk_size 1://= /=.
 rewrite (size_flatten_ctt 32).
  by move=> bs /mapP => [[w [_ ->]]].
 by rewrite size_map size_to_list.
rewrite flattenK 1://.
 move=> bs /mapP [l [Hl ->]].
 by rewrite /w2bits size_mkseq.
by rewrite -map_comp /(\o) /= map_id to_listK.
qed.

hoare keccakf_pqm4_h _A:
 M.keccakF1600_StatePermute
 : state = _A
 ==> res = stateTopqm4_op (keccak_f1600_op (pqm4Tostate_op _A)).
proc.
inline*.
bdep 1600 1600 [_A] [state] [state] pqm4permutation_spec pqm4permutation_pre.
+ move => |>.
  by rewrite bdep_auxP allP /#.
move=> |> st.
by rewrite !bdep_auxP /= /pqm4permutation_spec keccak_f1600E /#.
qed.
