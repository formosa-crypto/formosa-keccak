(* -------------------------------------------------------------------- *)
(* Safety of the 4-way Keccak-f[1600] permutations (ref, alt, nat), of the
   permutation dispatcher _keccakf1600_avx2x4, and of the 4-way state
   init and rate bit.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety.
from Jasmin require import JModel_x86 Jcheck JSafety.

(* ref *)

lemma _keccakf1600_4x_pround_ref_proof _e _b_e _a _b_a _r8 _r56 :
      (_keccakf1600_4x_pround_ref_spec _e _b_e _a _b_a _r8 _r56).
proof.
rewrite /_keccakf1600_4x_pround_ref_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __keccakf1600_avx2x4_ref_proof _a _b_a :
      (__keccakf1600_avx2x4_ref_spec _a _b_a).
proof.
rewrite /__keccakf1600_avx2x4_ref_spec; proc.
wp; while ((valid trace___keccakf1600_avx2x4_ref /\ 0 <= c /\ c %% 2 = 0)).
+ (* loop body *)
  wp; ecall (_keccakf1600_4x_pround_ref_proof param_6 b_param_0 param_5 b_param param_4 param_3).
  wp; ecall (_keccakf1600_4x_pround_ref_proof param_2 b_param_1 param_1 ((BArray800.init_arr (W8.of_int 255))) param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _keccakf1600_avx2x4_ref_proof _a _b_a :
      (_keccakf1600_avx2x4_ref_spec _a _b_a).
proof.
rewrite /_keccakf1600_avx2x4_ref_spec; proc.
wp; ecall (__keccakf1600_avx2x4_ref_proof param ((BArray800.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* alt *)

lemma __rol_4u64_rho56_proof _a : (__rol_4u64_rho56_spec _a).
proof.
rewrite /__rol_4u64_rho56_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __rol_4u64_rho8_proof _a : (__rol_4u64_rho8_spec _a).
proof.
rewrite /__rol_4u64_rho8_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __rol_4u64_proof _a _o : (__rol_4u64_spec _a _o).
proof.
rewrite /__rol_4u64_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __prepare_theta_proof _a_4x _b_A_4x :
      (__prepare_theta_spec _a_4x _b_A_4x).
proof.
rewrite /__prepare_theta_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __first_proof _ca _ce _ci _co _cu : (__first_spec _ca _ce _ci _co _cu).
proof.
rewrite /__first_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __second_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce _ci _co _cu _da _de _di _do _du :
      (__second_even_spec _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce 
      _ci _co _cu _da _de _di _do _du).
proof.
rewrite /__second_even_spec; proc.
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __third_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__third_even_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co 
      _cu _da _de _di _do _du).
proof.
rewrite /__third_even_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fourth_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__fourth_even_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co 
      _cu _da _de _di _do _du).
proof.
rewrite /__fourth_even_spec; proc.
wp; ecall (__rol_4u64_proof param_7 param_6).
wp; ecall (__rol_4u64_rho8_proof param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fifth_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__fifth_even_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co 
      _cu _da _de _di _do _du).
proof.
rewrite /__fifth_even_spec; proc.
wp; ecall (__rol_4u64_rho56_proof param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __sixth_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__sixth_even_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co 
      _cu _da _de _di _do _du).
proof.
rewrite /__sixth_even_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __second_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce _ci _co _cu _da _de _di _do _du :
      (__second_odd_spec _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce 
      _ci _co _cu _da _de _di _do _du).
proof.
rewrite /__second_odd_spec; proc.
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __third_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__third_odd_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu 
      _da _de _di _do _du).
proof.
rewrite /__third_odd_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fourth_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__fourth_odd_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co 
      _cu _da _de _di _do _du).
proof.
rewrite /__fourth_odd_spec; proc.
wp; ecall (__rol_4u64_proof param_7 param_6).
wp; ecall (__rol_4u64_rho8_proof param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fifth_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__fifth_odd_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu 
      _da _de _di _do _du).
proof.
rewrite /__fifth_odd_spec; proc.
wp; ecall (__rol_4u64_rho56_proof param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __sixth_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu _da _de _di _do _du :
      (__sixth_odd_spec _a_4x _b_A_4x _e_4x _b_E_4x _ca _ce _ci _co _cu 
      _da _de _di _do _du).
proof.
rewrite /__sixth_odd_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __second_last_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _da _de _di _do _du :
      (__second_last_spec _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _da _de 
      _di _do _du).
proof.
rewrite /__second_last_spec; proc.
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __third_last_proof _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du :
      (__third_last_spec _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du).
proof.
rewrite /__third_last_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fourth_last_proof _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du :
      (__fourth_last_spec _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du).
proof.
rewrite /__fourth_last_spec; proc.
wp; ecall (__rol_4u64_proof param_7 param_6).
wp; ecall (__rol_4u64_rho8_proof param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __fifth_last_proof _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du :
      (__fifth_last_spec _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du).
proof.
rewrite /__fifth_last_spec; proc.
wp; ecall (__rol_4u64_rho56_proof param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __sixth_last_proof _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du :
      (__sixth_last_spec _a_4x _b_A_4x _e_4x _b_E_4x _da _de _di _do _du).
proof.
rewrite /__sixth_last_spec; proc.
wp; ecall (__rol_4u64_proof param_8 param_7).
wp; ecall (__rol_4u64_proof param_6 param_5).
wp; ecall (__rol_4u64_proof param_4 param_3).
wp; ecall (__rol_4u64_proof param_2 param_1).
wp; ecall (__rol_4u64_proof param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _theta_rho_pi_chi_iota_prepare_theta_even_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce _ci _co _cu :
      (_theta_rho_pi_chi_iota_prepare_theta_even_spec _a_4x _b_A_4x _e_4x
      _b_E_4x _rc_index _ca _ce _ci _co _cu).
proof.
rewrite /_theta_rho_pi_chi_iota_prepare_theta_even_spec; proc.
seq 83 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_even /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 160)).
+ (* cut *)
  wp; ecall (__second_even_proof param_16 ((BArray800.init_arr (W8.of_int 255))) param_15 b_param_3 param_14 param_13 param_12 param_11 param_10 param_9 param_8 param_7 param_6 param_5 param_4).
  wp; ecall (__first_proof param_3 param_2 param_1 param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_even /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 320)).
+ (* cut *)
  wp; ecall (__third_even_proof param_28 ((BArray800.init_arr (W8.of_int 255))) param_27 b_param_2 param_26 param_25 param_24 param_23 param_22 param_21 param_20 param_19 param_18 param_17).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_even /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 480)).
+ (* cut *)
  wp; ecall (__fourth_even_proof param_40 ((BArray800.init_arr (W8.of_int 255))) param_39 b_param_1 param_38 param_37 param_36 param_35 param_34 param_33 param_32 param_31 param_30 param_29).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_even /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 640)).
+ (* cut *)
  wp; ecall (__fifth_even_proof param_52 ((BArray800.init_arr (W8.of_int 255))) param_51 b_param_0 param_50 param_49 param_48 param_47 param_46 param_45 param_44 param_43 param_42 param_41).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
wp; ecall (__sixth_even_proof param_64 ((BArray800.init_arr (W8.of_int 255))) param_63 b_param param_62 param_61 param_60 param_59 param_58 param_57 param_56 param_55 param_54 param_53).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _theta_rho_pi_chi_iota_prepare_theta_odd_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce _ci _co _cu :
      (_theta_rho_pi_chi_iota_prepare_theta_odd_spec _a_4x _b_A_4x _e_4x
      _b_E_4x _rc_index _ca _ce _ci _co _cu).
proof.
rewrite /_theta_rho_pi_chi_iota_prepare_theta_odd_spec; proc.
seq 83 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_odd /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 160)).
+ (* cut *)
  wp; ecall (__second_odd_proof param_16 ((BArray800.init_arr (W8.of_int 255))) param_15 b_param_3 param_14 param_13 param_12 param_11 param_10 param_9 param_8 param_7 param_6 param_5 param_4).
  wp; ecall (__first_proof param_3 param_2 param_1 param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_odd /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 320)).
+ (* cut *)
  wp; ecall (__third_odd_proof param_28 ((BArray800.init_arr (W8.of_int 255))) param_27 b_param_2 param_26 param_25 param_24 param_23 param_22 param_21 param_20 param_19 param_18 param_17).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_odd /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 480)).
+ (* cut *)
  wp; ecall (__fourth_odd_proof param_40 ((BArray800.init_arr (W8.of_int 255))) param_39 b_param_1 param_38 param_37 param_36 param_35 param_34 param_33 param_32 param_31 param_30 param_29).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 33 : ((valid trace__theta_rho_pi_chi_iota_prepare_theta_odd /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 640)).
+ (* cut *)
  wp; ecall (__fifth_odd_proof param_52 ((BArray800.init_arr (W8.of_int 255))) param_51 b_param_0 param_50 param_49 param_48 param_47 param_46 param_45 param_44 param_43 param_42 param_41).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
wp; ecall (__sixth_odd_proof param_64 ((BArray800.init_arr (W8.of_int 255))) param_63 b_param param_62 param_61 param_60 param_59 param_58 param_57 param_56 param_55 param_54 param_53).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __theta_rho_pi_chi_iota_proof _a_4x _b_A_4x _e_4x _b_E_4x _rc_index _ca _ce _ci _co _cu :
      (__theta_rho_pi_chi_iota_spec _a_4x _b_A_4x _e_4x _b_E_4x _rc_index 
      _ca _ce _ci _co _cu).
proof.
rewrite /__theta_rho_pi_chi_iota_spec; proc.
seq 68 : ((valid trace___theta_rho_pi_chi_iota /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 160)).
+ (* cut *)
  wp; ecall (__second_last_proof param_11 ((BArray800.init_arr (W8.of_int 255))) param_10 b_param_3 param_9 param_8 param_7 param_6 param_5 param_4).
  wp; ecall (__first_proof param_3 param_2 param_1 param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 18 : ((valid trace___theta_rho_pi_chi_iota /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 320)).
+ (* cut *)
  wp; ecall (__third_last_proof param_18 ((BArray800.init_arr (W8.of_int 255))) param_17 b_param_2 param_16 param_15 param_14 param_13 param_12).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 18 : ((valid trace___theta_rho_pi_chi_iota /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 480)).
+ (* cut *)
  wp; ecall (__fourth_last_proof param_25 ((BArray800.init_arr (W8.of_int 255))) param_24 b_param_1 param_23 param_22 param_21 param_20 param_19).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 18 : ((valid trace___theta_rho_pi_chi_iota /\ BArray800.is_init b_A_4x 0 800 /\ BArray800.is_init b_E_4x 0 640)).
+ (* cut *)
  wp; ecall (__fifth_last_proof param_32 ((BArray800.init_arr (W8.of_int 255))) param_31 b_param_0 param_30 param_29 param_28 param_27 param_26).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
wp; ecall (__sixth_last_proof param_39 ((BArray800.init_arr (W8.of_int 255))) param_38 b_param param_37 param_36 param_35 param_34 param_33).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __keccakf1600_avx2x4_alt_proof _a_4x _b_A_4x :
      (__keccakf1600_avx2x4_alt_spec _a_4x _b_A_4x).
proof.
rewrite /__keccakf1600_avx2x4_alt_spec; proc.
seq 191 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_7 ((BArray800.init_arr (W8.of_int 255))) param_6 b_param param_5 param_4 param_3 param_2 param_1 param_0).
  wp; ecall (__prepare_theta_proof param ((BArray800.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_15 ((BArray800.init_arr (W8.of_int 255))) param_14 ((BArray800.init_arr (W8.of_int 255))) param_13 param_12 param_11 param_10 param_9 param_8).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_23 ((BArray800.init_arr (W8.of_int 255))) param_22 ((BArray800.init_arr (W8.of_int 255))) param_21 param_20 param_19 param_18 param_17 param_16).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_31 ((BArray800.init_arr (W8.of_int 255))) param_30 ((BArray800.init_arr (W8.of_int 255))) param_29 param_28 param_27 param_26 param_25 param_24).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_39 ((BArray800.init_arr (W8.of_int 255))) param_38 ((BArray800.init_arr (W8.of_int 255))) param_37 param_36 param_35 param_34 param_33 param_32).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_47 ((BArray800.init_arr (W8.of_int 255))) param_46 ((BArray800.init_arr (W8.of_int 255))) param_45 param_44 param_43 param_42 param_41 param_40).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_55 ((BArray800.init_arr (W8.of_int 255))) param_54 ((BArray800.init_arr (W8.of_int 255))) param_53 param_52 param_51 param_50 param_49 param_48).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_63 ((BArray800.init_arr (W8.of_int 255))) param_62 ((BArray800.init_arr (W8.of_int 255))) param_61 param_60 param_59 param_58 param_57 param_56).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_71 ((BArray800.init_arr (W8.of_int 255))) param_70 ((BArray800.init_arr (W8.of_int 255))) param_69 param_68 param_67 param_66 param_65 param_64).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_79 ((BArray800.init_arr (W8.of_int 255))) param_78 ((BArray800.init_arr (W8.of_int 255))) param_77 param_76 param_75 param_74 param_73 param_72).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_87 ((BArray800.init_arr (W8.of_int 255))) param_86 ((BArray800.init_arr (W8.of_int 255))) param_85 param_84 param_83 param_82 param_81 param_80).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_95 ((BArray800.init_arr (W8.of_int 255))) param_94 ((BArray800.init_arr (W8.of_int 255))) param_93 param_92 param_91 param_90 param_89 param_88).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_103 ((BArray800.init_arr (W8.of_int 255))) param_102 ((BArray800.init_arr (W8.of_int 255))) param_101 param_100 param_99 param_98 param_97 param_96).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_111 ((BArray800.init_arr (W8.of_int 255))) param_110 ((BArray800.init_arr (W8.of_int 255))) param_109 param_108 param_107 param_106 param_105 param_104).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_119 ((BArray800.init_arr (W8.of_int 255))) param_118 ((BArray800.init_arr (W8.of_int 255))) param_117 param_116 param_115 param_114 param_113 param_112).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_127 ((BArray800.init_arr (W8.of_int 255))) param_126 ((BArray800.init_arr (W8.of_int 255))) param_125 param_124 param_123 param_122 param_121 param_120).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_135 ((BArray800.init_arr (W8.of_int 255))) param_134 ((BArray800.init_arr (W8.of_int 255))) param_133 param_132 param_131 param_130 param_129 param_128).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_143 ((BArray800.init_arr (W8.of_int 255))) param_142 ((BArray800.init_arr (W8.of_int 255))) param_141 param_140 param_139 param_138 param_137 param_136).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_151 ((BArray800.init_arr (W8.of_int 255))) param_150 ((BArray800.init_arr (W8.of_int 255))) param_149 param_148 param_147 param_146 param_145 param_144).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_159 ((BArray800.init_arr (W8.of_int 255))) param_158 ((BArray800.init_arr (W8.of_int 255))) param_157 param_156 param_155 param_154 param_153 param_152).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_167 ((BArray800.init_arr (W8.of_int 255))) param_166 ((BArray800.init_arr (W8.of_int 255))) param_165 param_164 param_163 param_162 param_161 param_160).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_odd_proof param_175 ((BArray800.init_arr (W8.of_int 255))) param_174 ((BArray800.init_arr (W8.of_int 255))) param_173 param_172 param_171 param_170 param_169 param_168).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
seq 28 : ((valid trace___keccakf1600_avx2x4_alt /\ BArray800.is_init b_A_4x 0 800)).
+ (* cut *)
  wp; ecall (_theta_rho_pi_chi_iota_prepare_theta_even_proof param_183 ((BArray800.init_arr (W8.of_int 255))) param_182 ((BArray800.init_arr (W8.of_int 255))) param_181 param_180 param_179 param_178 param_177 param_176).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
wp; ecall (__theta_rho_pi_chi_iota_proof param_191 ((BArray800.init_arr (W8.of_int 255))) param_190 ((BArray800.init_arr (W8.of_int 255))) param_189 param_188 param_187 param_186 param_185 param_184).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _keccakf1600_avx2x4_alt_proof _a _b_a :
      (_keccakf1600_avx2x4_alt_spec _a _b_a).
proof.
rewrite /_keccakf1600_avx2x4_alt_spec; proc.
wp; ecall (__keccakf1600_avx2x4_alt_proof param ((BArray800.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* nat *)

lemma __f1600_loopbody_native_proof _st _b_st _rol8 _b_rol8 _rol56 _b_rol56 _rC _b_RC _i _y10 _y14 _y8 _y15 _y9 _y13 _y3 _y7 _y2 :
      (__f1600_loopbody_native_spec _st _b_st _rol8 _b_rol8 _rol56 _b_rol56
      _rC _b_RC _i _y10 _y14 _y8 _y15 _y9 _y13 _y3 _y7 _y2).
proof.
rewrite /__f1600_loopbody_native_spec; proc.
simplify.
wp 300. simplify. wp 290. simplify. wp 280. simplify. wp 270. simplify. wp 260. simplify. wp 250. simplify. wp 240. simplify. wp 230. simplify.
wp 220. simplify. wp 210. simplify. wp 200. simplify. wp 190. simplify. wp 180. simplify. wp 170. simplify. wp 160. simplify. wp 150. simplify.
wp 140. simplify. wp 130. simplify. wp 120. simplify. wp 110. simplify. wp 100. simplify. wp 90. simplify. wp 80. simplify. wp 70. simplify.
wp 60. simplify. wp 50. simplify. wp 40. simplify. wp 30. simplify. wp 20. simplify. wp 10. simplify. wp 0. simplify.
skip; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(W64.of_uintK pow2_64)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(W64.of_uintK pow2_64).
qed.

lemma __regs_fetch_proof _st _b_st : (__regs_fetch_spec _st _b_st).
proof.
rewrite /__regs_fetch_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __regs_unfetch_proof _st _b_st _y10 _y14 _y8 _y15 _y9 _y13 _y3 _y7 _y2 :
      (__regs_unfetch_spec _st _b_st _y10 _y14 _y8 _y15 _y9 _y13 _y3 _y7 _y2).
proof.
rewrite /__regs_unfetch_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __keccakf1600_avx2x4_nat_proof _st _b_st :
      (__keccakf1600_avx2x4_nat_spec _st _b_st).
proof.
rewrite /__keccakf1600_avx2x4_nat_spec; proc.
seq 71 : ((valid trace___keccakf1600_avx2x4_nat /\ 1 <= i <= 24)).
+ (* cut *)
  wp; ecall (__f1600_loopbody_native_proof param_13 ((BArray800.init_arr (W8.of_int 255))) param_12 ((BArray32.init_arr (W8.of_int 255))) param_11 ((BArray32.init_arr (W8.of_int 255))) param_10 ((BArray192.init_arr (W8.of_int 255))) param_9 param_8 param_7 param_6 param_5 param_4 param_3 param_2 param_1 param_0).
  wp; ecall (__regs_fetch_proof param ((BArray800.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
wp; ecall (__regs_unfetch_proof param_23 ((BArray800.init_arr (W8.of_int 255))) param_22 param_21 param_20 param_19 param_18 param_17 param_16 param_15 param_14).
wp; while ((valid trace___keccakf1600_avx2x4_nat /\ 1 <= i <= 24)).
+ (* loop body *)
  wp; ecall (__f1600_loopbody_native_proof param_13 ((BArray800.init_arr (W8.of_int 255))) param_12 ((BArray32.init_arr (W8.of_int 255))) param_11 ((BArray32.init_arr (W8.of_int 255))) param_10 ((BArray192.init_arr (W8.of_int 255))) param_9 param_8 param_7 param_6 param_5 param_4 param_3 param_2 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _keccakf1600_avx2x4_nat_proof _st _b_st :
      (_keccakf1600_avx2x4_nat_spec _st _b_st).
proof.
rewrite /_keccakf1600_avx2x4_nat_spec; proc.
wp; ecall (__keccakf1600_avx2x4_nat_proof param ((BArray800.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* dispatcher, state init, rate bit *)

lemma _keccakf1600_avx2x4_proof _a _b_a : (_keccakf1600_avx2x4_spec _a _b_a).
proof.
rewrite /_keccakf1600_avx2x4_spec; proc.
inline M.__KECCAK_Fx4.
sp 18.
if.
+ (* then *)
  wp; ecall (_keccakf1600_avx2x4_alt_proof param_0 ((BArray800.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  if.
  + (* then *)
    wp; ecall (_keccakf1600_avx2x4_nat_proof param_1 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    wp; ecall (_keccakf1600_avx2x4_ref_proof param_2 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma _keccakf1600_avx2x4__proof _a _b_a :
      (_keccakf1600_avx2x4__spec _a _b_a).
proof.
rewrite /_keccakf1600_avx2x4__spec; proc.
wp; ecall (_keccakf1600_avx2x4_proof param ((BArray800.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __state_init_avx2x4_proof _st _b_st :
      (__state_init_avx2x4_spec _st _b_st).
proof.
rewrite /__state_init_avx2x4_spec; proc.
wp; while ((valid trace___state_init_avx2x4 /\ 0 <= i <= 800 /\ i %% 32 = 0 /\ BArray800.is_init b_st 0 i)).
+ (* loop body *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __addratebit_avx2x4_proof _st _b_st _rATE8 :
      (__addratebit_avx2x4_spec _st _b_st _rATE8).
proof.
rewrite /__addratebit_avx2x4_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.
