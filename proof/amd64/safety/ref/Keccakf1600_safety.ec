(* -------------------------------------------------------------------- *)
(* Safety of the 1-way Keccak-f[1600] permutations (ref, basic, opt, avx2)
   and of the permutation dispatcher _keccakf1600.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety.
from Jasmin require import JModel_x86 Jcheck JSafety.

(* ref *)

lemma __andn_u64_ref_proof _a _b : (__andn_u64_ref_spec _a _b).
proof.
rewrite /__andn_u64_ref_spec; proc.
inline M.__HAS_FEATURE.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __rol_u64_ref_proof _x _i : (__rol_u64_ref_spec _x _i).
proof.
rewrite /__rol_u64_ref_spec; proc.
inline M.__HAS_FEATURE.
sp 10.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __theta_sum_ref_proof _a _b_a : (__theta_sum_ref_spec _a _b_a).
proof.
rewrite /__theta_sum_ref_spec; proc.
seq 7 : ((valid trace___theta_sum_ref /\ 0 <= x <= 5 /\ BArray40.is_init b_c 0 (8 * x)) /\ !((x < 5))).
+ (* loop *)
  wp; while ((valid trace___theta_sum_ref /\ 0 <= x <= 5 /\ BArray40.is_init b_c 0 (8 * x))).
  + (* loop body *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
wp; while ((valid trace___theta_sum_ref /\ 1 <= y <= 5 /\ BArray40.is_init b_c 0 40)).
+ (* loop body *)
  wp; while ((valid trace___theta_sum_ref /\ 0 <= x <= 5 /\ 1 <= y < 5 /\ BArray40.is_init b_c 0 40)).
  + (* loop body *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __theta_rol_ref_proof _c _b_c : (__theta_rol_ref_spec _c _b_c).
proof.
rewrite /__theta_rol_ref_spec; proc.
wp; while ((valid trace___theta_rol_ref /\ 0 <= x <= 5 /\ BArray40.is_init b_d 0 (8 * x))).
+ (* loop body *)
  wp; ecall (__rol_u64_ref_proof param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __rol_sum_ref_proof _a _b_a _d _b_d _y :
      (__rol_sum_ref_spec _a _b_a _d _b_d _y).
proof.
rewrite /__rol_sum_ref_spec; proc.
wp; while ((valid trace___rol_sum_ref /\ 0 <= x <= 5 /\ BArray40.is_init b_b 0 (8 * x))).
+ (* loop body *)
  wp; ecall (__rol_u64_ref_proof param_2 param_1).
  wp; ecall (keccakf1600_rhotates_proof param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __set_row_ref_proof _e _b_e _b _b_b _y :
      (__set_row_ref_spec _e _b_e _b _b_b _y).
proof.
rewrite /__set_row_ref_spec; proc.
wp; while ((valid trace___set_row_ref /\ 0 <= x <= 5 /\ 0 <= y < 5 /\ BArray40.is_init b_b 0 40 /\ BArray200.is_init b_e 0 (y * 5 * 8 + 8 * x))).
+ (* loop body *)
  wp; ecall (__andn_u64_ref_proof param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _pround_ref_proof _e _b_e _a _b_a : (_pround_ref_spec _e _b_e _a _b_a).
proof.
rewrite /_pround_ref_spec; proc.
seq 35 : ((valid trace__pround_ref /\ 0 <= y <= 5 /\ BArray200.is_init b_e 0 (y * 5 * 8))).
+ (* cut *)
  wp; ecall (__theta_rol_ref_proof param_0 ((BArray40.init_arr (W8.of_int 255)))).
  wp; ecall (__theta_sum_ref_proof param ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
wp; while ((valid trace__pround_ref /\ 0 <= y <= 5 /\ BArray200.is_init b_e 0 (y * 5 * 8))).
+ (* loop body *)
  wp; ecall (__set_row_ref_proof param_6 b_param param_5 ((BArray40.init_arr (W8.of_int 255))) param_4).
  wp; ecall (__rol_sum_ref_proof param_3 ((BArray200.init_arr (W8.of_int 255))) param_2 ((BArray40.init_arr (W8.of_int 255))) param_1).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __keccakf1600_ref_proof _a _b_a : (__keccakf1600_ref_spec _a _b_a).
proof.
rewrite /__keccakf1600_ref_spec; proc.
seq 60 : ((valid trace___keccakf1600_ref /\ 0 <= c /\ BArray200.is_init b_a 0 200)).
+ (* cut *)
  wp; ecall (_pround_ref_proof param_2 b_param_0 param_1 b_param).
  wp; ecall (_pround_ref_proof param_0 b_param_1 param ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
wp; while ((valid trace___keccakf1600_ref /\ 0 <= c /\ BArray200.is_init b_a 0 200)).
+ (* loop body *)
  wp; ecall (_pround_ref_proof param_2 b_param_0 param_1 b_param).
  wp; ecall (_pround_ref_proof param_0 b_param_1 param ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_ref_proof _a _b_a : (_keccakf1600_ref_spec _a _b_a).
proof.
rewrite /_keccakf1600_ref_spec; proc.
wp; ecall (__keccakf1600_ref_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_ref__proof _a _b_a : (_keccakf1600_ref__spec _a _b_a).
proof.
rewrite /_keccakf1600_ref__spec; proc.
wp; ecall (_keccakf1600_ref_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

(* basic *)

lemma __pround_basic_inlined_proof _e _b_e _a _b_a :
      (__pround_basic_inlined_spec _e _b_e _a _b_a).
proof.
rewrite /__pround_basic_inlined_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __not_lane_basic_proof _st _b_st _idx :
      (__not_lane_basic_spec _st _b_st _idx).
proof.
rewrite /__not_lane_basic_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __complement_lanes_basic_proof _st _b_st :
      (__complement_lanes_basic_spec _st _b_st).
proof.
rewrite /__complement_lanes_basic_spec; proc.
wp; ecall (__not_lane_basic_proof param_10 ((BArray200.init_arr (W8.of_int 255))) param_9).
wp; ecall (__not_lane_basic_proof param_8 ((BArray200.init_arr (W8.of_int 255))) param_7).
wp; ecall (__not_lane_basic_proof param_6 ((BArray200.init_arr (W8.of_int 255))) param_5).
wp; ecall (__not_lane_basic_proof param_4 ((BArray200.init_arr (W8.of_int 255))) param_3).
wp; ecall (__not_lane_basic_proof param_2 ((BArray200.init_arr (W8.of_int 255))) param_1).
wp; ecall (__not_lane_basic_proof param_0 ((BArray200.init_arr (W8.of_int 255))) param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __keccakf1600_basic_proof _a _b_a : (__keccakf1600_basic_spec _a _b_a).
proof.
rewrite /__keccakf1600_basic_spec; proc.
seq 74 : ((valid trace___keccakf1600_basic /\ 0 <= c /\ BArray200.is_init b_a 0 200)).
+ (* cut *)
  wp; ecall (__pround_basic_inlined_proof param_3 b_param_1 param_2 b_param_0).
  wp; ecall (__pround_basic_inlined_proof param_1 b_param_2 param_0 ((BArray200.init_arr (W8.of_int 255)))).
  wp; ecall (__complement_lanes_basic_proof param ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
wp; ecall (__complement_lanes_basic_proof param_4 b_param).
wp; while ((valid trace___keccakf1600_basic /\ 0 <= c /\ BArray200.is_init b_a 0 200)).
+ (* loop body *)
  wp; ecall (__pround_basic_inlined_proof param_3 b_param_1 param_2 b_param_0).
  wp; ecall (__pround_basic_inlined_proof param_1 b_param_2 param_0 ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_basic_proof _a _b_a : (_keccakf1600_basic_spec _a _b_a).
proof.
rewrite /_keccakf1600_basic_spec; proc.
wp; ecall (__keccakf1600_basic_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_basic__proof _a _b_a : (_keccakf1600_basic__spec _a _b_a).
proof.
rewrite /_keccakf1600_basic__spec; proc.
wp; ecall (_keccakf1600_basic_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

(* opt *)

lemma keccakf1600_opt_loop_body_proof _rax _rbp _rdi _r13 _r10 _r11 _r8 _rsi _r15 _rbx _a _b_a _e _b_e :
      (keccakf1600_opt_loop_body_spec _rax _rbp _rdi _r13 _r10 _r11 _r8 
      _rsi _r15 _rbx _a _b_a _e _b_e).
proof.
rewrite /keccakf1600_opt_loop_body_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(W64.uleE W64.to_uintD_small W64.to_uint_cmp).
qed.

lemma read_regs_opt_proof _a _b_a : (read_regs_opt_spec _a _b_a).
proof.
rewrite /read_regs_opt_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma store_regs_opt_proof _a _b_a _rbp _rdi _r13 _r10 _r11 _r8 _rsi _r15 _rbx :
      (store_regs_opt_spec _a _b_a _rbp _rdi _r13 _r10 _r11 _r8 _rsi 
      _r15 _rbx).
proof.
rewrite /store_regs_opt_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __keccakf1600_opt_proof _a _b_a : (__keccakf1600_opt_spec _a _b_a).
proof.
rewrite /__keccakf1600_opt_spec; proc.
seq 72 : ((valid trace___keccakf1600_opt /\ W64.to_uint rax %% 2 = 0 /\ W64.to_uint rax <= 24)).
+ (* cut *)
  wp; ecall (keccakf1600_opt_loop_body_proof param_11 param_10 param_9 param_8 param_7 param_6 param_5 param_4 param_3 param_2 param_1 ((BArray200.init_arr (W8.of_int 255))) param_0 b_param).
  wp; ecall (read_regs_opt_proof param ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(W64.uleE W64.ultE W64.to_uintD_small W64.to_uint_cmp).
wp; ecall (store_regs_opt_proof param_21 ((BArray200.init_arr (W8.of_int 255))) param_20 param_19 param_18 param_17 param_16 param_15 param_14 param_13 param_12).
wp; while ((valid trace___keccakf1600_opt /\ W64.to_uint rax %% 2 = 0 /\ W64.to_uint rax <= 24)).
+ (* loop body *)
  wp; ecall (keccakf1600_opt_loop_body_proof param_11 param_10 param_9 param_8 param_7 param_6 param_5 param_4 param_3 param_2 param_1 ((BArray200.init_arr (W8.of_int 255))) param_0 b_param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(W64.uleE W64.ultE W64.to_uintD_small W64.to_uint_cmp).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(W64.uleE W64.ultE W64.to_uintD_small W64.to_uint_cmp).
qed.

lemma _keccakf1600_opt_proof _a _b_a : (_keccakf1600_opt_spec _a _b_a).
proof.
rewrite /_keccakf1600_opt_spec; proc.
wp; ecall (__keccakf1600_opt_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

(* avx2 *)

lemma __keccakf1600_pround_avx2_proof _state _b_state :
      (__keccakf1600_pround_avx2_spec _state _b_state).
proof.
rewrite /__keccakf1600_pround_avx2_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __keccakf1600_avx2_proof _state _b_state :
      (__keccakf1600_avx2_spec _state _b_state).
proof.
rewrite /__keccakf1600_avx2_spec; proc.
seq 20 : ((valid trace___keccakf1600_avx2 /\ 1 <= r <= 24)).
+ (* cut *)
  wp; ecall (__keccakf1600_pround_avx2_proof param ((BArray224.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
wp; while ((valid trace___keccakf1600_avx2 /\ 1 <= r <= 24)).
+ (* loop body *)
  wp; ecall (__keccakf1600_pround_avx2_proof param ((BArray224.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_avx2_proof _state _b_state :
      (_keccakf1600_avx2_spec _state _b_state).
proof.
rewrite /_keccakf1600_avx2_spec; proc.
wp; ecall (__keccakf1600_avx2_proof param ((BArray224.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __stavx2_pack_proof _st _b_st : (__stavx2_pack_spec _st _b_st).
proof.
rewrite /__stavx2_pack_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma __stavx2_unpack_proof _st _b_st _state _b_state :
      (__stavx2_unpack_spec _st _b_st _state _b_state).
proof.
rewrite /__stavx2_unpack_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600_st25_avx2_proof _st25 _b_st25 :
      (_keccakf1600_st25_avx2_spec _st25 _b_st25).
proof.
rewrite /_keccakf1600_st25_avx2_spec; proc.
wp; ecall (__stavx2_unpack_proof param_2 ((BArray200.init_arr (W8.of_int 255))) param_1 ((BArray224.init_arr (W8.of_int 255)))).
wp; ecall (__keccakf1600_avx2_proof param_0 ((BArray224.init_arr (W8.of_int 255)))).
wp; ecall (__stavx2_pack_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

(* dispatcher *)

lemma _keccakf1600_proof _a _b_a : (_keccakf1600_spec _a _b_a).
proof.
rewrite /_keccakf1600_spec; proc.
inline M.__KECCAK_F.
sp 21.
if.
+ (* then *)
  wp; ecall (_keccakf1600_opt_proof param_0 ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
+ (* else *)
  if.
  + (* then *)
    wp; ecall (_keccakf1600_basic_proof param_1 ((BArray200.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
  + (* else *)
    if.
    + (* then *)
      wp; ecall (_keccakf1600_st25_avx2_proof param_2 ((BArray200.init_arr (W8.of_int 255)))).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
    + (* else *)
      wp; ecall (_keccakf1600_ref_proof param_3 ((BArray200.init_arr (W8.of_int 255)))).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.

lemma _keccakf1600__proof _a _b_a : (_keccakf1600__spec _a _b_a).
proof.
rewrite /_keccakf1600__spec; proc.
wp; ecall (_keccakf1600_proof param ((BArray200.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt().
qed.
