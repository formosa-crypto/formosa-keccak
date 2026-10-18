(* -------------------------------------------------------------------- *)
(* Safety of the 1-way AVX2 (u256[7] state) absorb/squeeze code: state
   helpers, fixed-size memory and array absorb/squeeze.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600_safety.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.

(* AVX2 state helpers *)

lemma __u64_to_u256_proof _x _l : (__u64_to_u256_spec _x _l).
proof.
rewrite /__u64_to_u256_spec; proc.
sp 1.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __state_init_avx2_proof  : (__state_init_avx2_spec).
proof.
rewrite /__state_init_avx2_spec; proc.
wp; while ((valid trace___state_init_avx2 /\ 0 <= i <= 7 /\ BArray224.is_init b_st 0 (32 * i))).
+ (* loop body *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __perm_reg3456_avx2_proof _r3 _r4 _r5 _r6 :
      (__perm_reg3456_avx2_spec _r3 _r4 _r5 _r6).
proof.
rewrite /__perm_reg3456_avx2_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __unperm_reg3456_avx2_proof _st3 _st4 _st5 _st6 :
      (__unperm_reg3456_avx2_spec _st3 _st4 _st5 _st6).
proof.
rewrite /__unperm_reg3456_avx2_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __addstate_r3456_avx2_proof _st _b_st _r3 _r4 _r5 _r6 :
      (__addstate_r3456_avx2_spec _st _b_st _r3 _r4 _r5 _r6).
proof.
rewrite /__addstate_r3456_avx2_spec; proc.
wp; ecall (__perm_reg3456_avx2_proof param_2 param_1 param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __stavx2_pos_avx2_proof _pOS : (__stavx2_pos_avx2_spec _pOS).
proof.
rewrite /__stavx2_pos_avx2_spec; proc.
sp 3.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    if.
    + (* then *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    + (* else *)
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        if.
        + (* then *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
        + (* else *)
          if.
          + (* then *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
          + (* else *)
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
            + (* else *)
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
              + (* else *)
                if.
                + (* then *)
                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                + (* else *)
                  if.
                  + (* then *)
                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                  + (* else *)
                    if.
                    + (* then *)
                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                    + (* else *)
                      if.
                      + (* then *)
                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                      + (* else *)
                        if.
                        + (* then *)
                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                        + (* else *)
                          if.
                          + (* then *)
                            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                          + (* else *)
                            if.
                            + (* then *)
                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                            + (* else *)
                              if.
                              + (* then *)
                                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                              + (* else *)
                                if.
                                + (* then *)
                                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                + (* else *)
                                  if.
                                  + (* then *)
                                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                  + (* else *)
                                    if.
                                    + (* then *)
                                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                    + (* else *)
                                      if.
                                      + (* then *)
                                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                      + (* else *)
                                        if.
                                        + (* then *)
                                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                        + (* else *)
                                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __addratebit_avx2_proof _st _b_st _rATE_8 :
      (__addratebit_avx2_spec _st _b_st _rATE_8).
proof.
rewrite /__addratebit_avx2_spec; proc.
inline M.__stavx2_pos_avx2.
sp 9.
if.
+ (* then *)
  if.
  + (* then *)
    sp 7.
    if.
    + (* then *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    + (* else *)
      wp; ecall (__u64_to_u256_proof param_1 param_0).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    if.
    + (* then *)
      sp 7.
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        wp; ecall (__u64_to_u256_proof param_1 param_0).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    + (* else *)
      if.
      + (* then *)
        sp 7.
        if.
        + (* then *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
        + (* else *)
          wp; ecall (__u64_to_u256_proof param_1 param_0).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        if.
        + (* then *)
          sp 7.
          if.
          + (* then *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
          + (* else *)
            wp; ecall (__u64_to_u256_proof param_1 param_0).
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
        + (* else *)
          if.
          + (* then *)
            sp 7.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
            + (* else *)
              wp; ecall (__u64_to_u256_proof param_1 param_0).
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
          + (* else *)
            if.
            + (* then *)
              sp 7.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
              + (* else *)
                wp; ecall (__u64_to_u256_proof param_1 param_0).
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
            + (* else *)
              if.
              + (* then *)
                sp 7.
                if.
                + (* then *)
                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                + (* else *)
                  wp; ecall (__u64_to_u256_proof param_1 param_0).
                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
              + (* else *)
                if.
                + (* then *)
                  sp 7.
                  if.
                  + (* then *)
                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                  + (* else *)
                    wp; ecall (__u64_to_u256_proof param_1 param_0).
                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                + (* else *)
                  if.
                  + (* then *)
                    sp 7.
                    if.
                    + (* then *)
                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                    + (* else *)
                      wp; ecall (__u64_to_u256_proof param_1 param_0).
                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                  + (* else *)
                    if.
                    + (* then *)
                      sp 7.
                      if.
                      + (* then *)
                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                      + (* else *)
                        wp; ecall (__u64_to_u256_proof param_1 param_0).
                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                    + (* else *)
                      if.
                      + (* then *)
                        sp 7.
                        if.
                        + (* then *)
                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                        + (* else *)
                          wp; ecall (__u64_to_u256_proof param_1 param_0).
                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                      + (* else *)
                        if.
                        + (* then *)
                          sp 7.
                          if.
                          + (* then *)
                            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                          + (* else *)
                            wp; ecall (__u64_to_u256_proof param_1 param_0).
                            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                        + (* else *)
                          if.
                          + (* then *)
                            sp 7.
                            if.
                            + (* then *)
                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                            + (* else *)
                              wp; ecall (__u64_to_u256_proof param_1 param_0).
                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                          + (* else *)
                            if.
                            + (* then *)
                              sp 7.
                              if.
                              + (* then *)
                                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                              + (* else *)
                                wp; ecall (__u64_to_u256_proof param_1 param_0).
                                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                            + (* else *)
                              if.
                              + (* then *)
                                sp 7.
                                if.
                                + (* then *)
                                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                + (* else *)
                                  wp; ecall (__u64_to_u256_proof param_1 param_0).
                                  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                              + (* else *)
                                if.
                                + (* then *)
                                  sp 7.
                                  if.
                                  + (* then *)
                                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                  + (* else *)
                                    wp; ecall (__u64_to_u256_proof param_1 param_0).
                                    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                + (* else *)
                                  if.
                                  + (* then *)
                                    sp 7.
                                    if.
                                    + (* then *)
                                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                    + (* else *)
                                      wp; ecall (__u64_to_u256_proof param_1 param_0).
                                      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                  + (* else *)
                                    if.
                                    + (* then *)
                                      sp 7.
                                      if.
                                      + (* then *)
                                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                      + (* else *)
                                        wp; ecall (__u64_to_u256_proof param_1 param_0).
                                        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                    + (* else *)
                                      if.
                                      + (* then *)
                                        sp 7.
                                        if.
                                        + (* then *)
                                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                        + (* else *)
                                          wp; ecall (__u64_to_u256_proof param_1 param_0).
                                          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                      + (* else *)
                                        if.
                                        + (* then *)
                                          sp 7.
                                          if.
                                          + (* then *)
                                            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                          + (* else *)
                                            wp; ecall (__u64_to_u256_proof param_1 param_0).
                                            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                        + (* else *)
                                          if.
                                          + (* then *)
                                            sp 7.
                                            if.
                                            + (* then *)
                                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                            + (* else *)
                                              wp; ecall (__u64_to_u256_proof param_1 param_0).
                                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                          + (* else *)
                                            sp 5.
                                            if.
                                            + (* then *)
                                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
                                            + (* else *)
                                              wp; ecall (__u64_to_u256_proof param_1 param_0).
                                              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  sp 5.
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    wp; ecall (__u64_to_u256_proof param_1 param_0).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

(* memory absorb/squeeze *)

lemma __addstate_m_avx2_proof _st _b_st _aT _buf __LEN __TRAILB :
      (__addstate_m_avx2_spec _st _b_st _aT _buf __LEN __TRAILB).
proof.
rewrite /__addstate_m_avx2_spec; proc.
sp 6.
seq 1 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 8 <= _aT then _aT else if 8 <= (_aT + __LEN) then 8 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 8 <= _aT then __LEN else if 8 <= (_aT + __LEN) then (_aT + __LEN) - 8 else 0) /\ _TRAILB = (if 8 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 8 <= _aT then __LEN else if 8 <= (_aT + __LEN) then (_aT + __LEN) - 8 else 0)))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_bcast_upto8_at_proof param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
seq 1 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 40 <= _aT then _aT else if 40 <= (_aT + __LEN) then 40 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 40 <= _aT then __LEN else if 40 <= (_aT + __LEN) then (_aT + __LEN) - 40 else 0) /\ _TRAILB = (if 40 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 40 <= _aT then __LEN else if 40 <= (_aT + __LEN) then (_aT + __LEN) - 40 else 0)))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_upto32_at_proof param_8 param_7 param_6 param_5 param_4).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
if.
+ (* then *)
  seq 17 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 48 <= _aT then _aT else if 48 <= (_aT + __LEN) then 48 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 48 <= _aT then __LEN else if 48 <= (_aT + __LEN) then (_aT + __LEN) - 48 else 0) /\ _TRAILB = (if 48 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 48 <= _aT then __LEN else if 48 <= (_aT + __LEN) then (_aT + __LEN) - 48 else 0)))).
  + (* cut *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_13 param_12 param_11 param_10 param_9).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  if.
  + (* then *)
    seq 15 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 80 <= _aT then _aT else if 80 <= (_aT + __LEN) then 80 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 80 <= _aT then __LEN else if 80 <= (_aT + __LEN) then (_aT + __LEN) - 80 else 0) /\ _TRAILB = (if 80 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 80 <= _aT then __LEN else if 80 <= (_aT + __LEN) then (_aT + __LEN) - 80 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto32_at_proof param_18 param_17 param_16 param_15 param_14).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 16 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 88 <= _aT then _aT else if 88 <= (_aT + __LEN) then 88 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 88 <= _aT then __LEN else if 88 <= (_aT + __LEN) then (_aT + __LEN) - 88 else 0) /\ _TRAILB = (if 88 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 88 <= _aT then __LEN else if 88 <= (_aT + __LEN) then (_aT + __LEN) - 88 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_23 param_22 param_21 param_20 param_19).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 15 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 120 <= _aT then _aT else if 120 <= (_aT + __LEN) then 120 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 120 <= _aT then __LEN else if 120 <= (_aT + __LEN) then (_aT + __LEN) - 120 else 0) /\ _TRAILB = (if 120 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 120 <= _aT then __LEN else if 120 <= (_aT + __LEN) then (_aT + __LEN) - 120 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto32_at_proof param_28 param_27 param_26 param_25 param_24).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 16 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 128 <= _aT then _aT else if 128 <= (_aT + __LEN) then 128 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 128 <= _aT then __LEN else if 128 <= (_aT + __LEN) then (_aT + __LEN) - 128 else 0) /\ _TRAILB = (if 128 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 128 <= _aT then __LEN else if 128 <= (_aT + __LEN) then (_aT + __LEN) - 128 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_33 param_32 param_31 param_30 param_29).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 15 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 160 <= _aT then _aT else if 160 <= (_aT + __LEN) then 160 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 160 <= _aT then __LEN else if 160 <= (_aT + __LEN) then (_aT + __LEN) - 160 else 0) /\ _TRAILB = (if 160 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 160 <= _aT then __LEN else if 160 <= (_aT + __LEN) then (_aT + __LEN) - 160 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto32_at_proof param_38 param_37 param_36 param_35 param_34).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 16 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 168 <= _aT then _aT else if 168 <= (_aT + __LEN) then 168 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 168 <= _aT then __LEN else if 168 <= (_aT + __LEN) then (_aT + __LEN) - 168 else 0) /\ _TRAILB = (if 168 <= (_aT + __LEN) then __TRAILB else 0) /\ buf = _buf + (__LEN - (if 168 <= _aT then __LEN else if 168 <= (_aT + __LEN) then (_aT + __LEN) - 168 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_43 param_42 param_41 param_40 param_39).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 13 : ((valid trace___addstate_m_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (if 200 <= _aT then _aT else if 200 <= (_aT + __LEN) then 200 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ buf = _buf + (__LEN - (if 200 <= _aT then __LEN else if 200 <= (_aT + __LEN) then (_aT + __LEN) - 200 else 0)))).
    + (* cut *)
      wp; ecall (__m_ilen_read_upto32_at_proof param_48 param_47 param_46 param_45 param_44).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    wp; ecall (__addstate_r3456_avx2_proof param_53 ((BArray224.init_arr (W8.of_int 255))) param_52 param_51 param_50 param_49).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __absorb_m_avx2_proof _st _b_st _aT _buf __LEN __TRAILB __RATE8 :
      (__absorb_m_avx2_spec _st _b_st _aT _buf __LEN __TRAILB __RATE8).
proof.
rewrite /__absorb_m_avx2_spec; proc.
sp 21.
if.
+ (* then *)
  seq 27 : ((valid trace___absorb_m_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2_proof param_4 ((BArray224.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_m_avx2_proof param_3 ((BArray224.init_arr (W8.of_int 255))) param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  seq 1 : ((valid trace___absorb_m_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_m_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2_proof param_10 ((BArray224.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_m_avx2_proof param_9 ((BArray224.init_arr (W8.of_int 255))) param_8 param_7 param_6 param_5).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  seq 16 : ((valid trace___absorb_m_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_avx2_proof param_15 ((BArray224.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2_proof param_17 ((BArray224.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  seq 15 : ((valid trace___absorb_m_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_avx2_proof param_15 ((BArray224.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2_proof param_17 ((BArray224.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __dumpstate_m_avx2_proof _buf __LEN _st _b_st :
      (__dumpstate_m_avx2_spec _buf __LEN _st _b_st).
proof.
rewrite /__dumpstate_m_avx2_spec; proc.
sp 3.
seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 8 then __LEN else 8) /\ buf = _buf + (if __LEN < 8 then __LEN else 8))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (__m_ilen_write_upto32_proof param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    wp; ecall (__m_ilen_write_upto32_proof param_4 param_3 param_2).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
seq 9 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 40 then __LEN else 40) /\ buf = _buf + (if __LEN < 40 then __LEN else 40))).
+ (* cut *)
  wp; ecall (__m_ilen_write_upto32_proof param_7 param_6 param_5).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
if.
+ (* then *)
  seq 13 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 48 then __LEN else 48) /\ buf = _buf + (if __LEN < 48 then __LEN else 48))).
  + (* cut *)
    wp; ecall (__m_ilen_write_upto8_proof param_10 param_9 param_8).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  if.
  + (* then *)
    seq 14 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 80 then __LEN else 80) /\ buf = _buf + (if __LEN < 80 then __LEN else 80))).
    + (* cut *)
      wp; ecall (__m_ilen_write_upto32_proof param_13 param_12 param_11).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 88 then __LEN else 88) /\ buf = _buf + (if __LEN < 88 then __LEN else 88))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_16 param_15 param_14).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 120 then __LEN else 120) /\ buf = _buf + (if __LEN < 120 then __LEN else 120))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto32_proof param_19 param_18 param_17).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 128 then __LEN else 128) /\ buf = _buf + (if __LEN < 128 then __LEN else 128))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_22 param_21 param_20).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 160 then __LEN else 160) /\ buf = _buf + (if __LEN < 160 then __LEN else 160))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto32_proof param_25 param_24 param_23).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    seq 1 : ((valid trace___dumpstate_m_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ _LEN = __LEN - (if __LEN < 168 then __LEN else 168) /\ buf = _buf + (if __LEN < 168 then __LEN else 168))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_28 param_27 param_26).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    if.
    + (* then *)
      wp; ecall (__m_ilen_write_upto32_proof param_31 param_30 param_29).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

lemma __squeeze_m_avx2_proof _st _b_st _buf __LEN __RATE8 :
      (__squeeze_m_avx2_spec _st _b_st _buf __LEN __RATE8).
proof.
rewrite /__squeeze_m_avx2_spec; proc.
seq 16 : ((valid trace___squeeze_m_avx2 /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + _RATE8 * i) /\ !((i < iTERS))).
+ (* loop *)
  wp; while ((valid trace___squeeze_m_avx2 /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + _RATE8 * i)).
  + (* loop body *)
    wp; ecall (__dumpstate_m_avx2_proof param_2 param_1 param_0 ((BArray224.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2_proof param ((BArray224.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
if.
+ (* then *)
  wp; ecall (__dumpstate_m_avx2_proof param_6 param_5 param_4 ((BArray224.init_arr (W8.of_int 255)))).
  wp; ecall (_keccakf1600_avx2_proof param_3 ((BArray224.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod).
qed.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory KeccakArrayAvx2Safety.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

(* the ui64 range conditions of the model are stated with the literal 2^64-1 *)
lemma _ASIZE_max: _ASIZE <= 18446744073709551615.
proof. smt(_ASIZE_u64 pow2_64). qed.

clone import ByteArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import ReadWriteArraySafety as RW
 with op _ASIZE <- _ASIZE,
      theory A <- A
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

(* The array procedures of Keccak1600_Jazz_ASIZE_safety (extracted at
   _ASIZE = 999), with BArray999 replaced by A and 999 by _ASIZE,
   the subreadwrite callees taken from RW.MM,
   the size-independent callees taken from Keccak1600_Jazz_safety.M, and
   their safety specifications restated over MM. Generated by
   scripts/asize_transform.py --safety; checked by
   ../extracted/Keccak1600_fixedsizes_avx2_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc __addstate_avx2 (st:BArray224.t, b_st:BArray224.t, aT:int,
                        buf:A.t, b_buf:A.t, offset:int,
                        _LEN:int, _TRAILB:int) : BArray224.t * BArray224.t *
                                                 int * int * trace = {
    var aux:BArray224.t;
    var aux_0:BArray224.t;
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    var param:int;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:A.t;
    var result:W256.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var result_3:int;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:A.t;
    var result_4:W256.t;
    var result_5:int;
    var result_6:int;
    var result_7:int;
    var result_8:int;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:int;
    var param_19:A.t;
    var result_9:W64.t;
    var result_10:int;
    var result_11:int;
    var result_12:int;
    var result_13:int;
    var param_20:int;
    var param_21:int;
    var param_22:int;
    var param_23:int;
    var param_24:int;
    var param_25:int;
    var param_26:A.t;
    var result_14:W256.t;
    var result_15:int;
    var result_16:int;
    var result_17:int;
    var result_18:int;
    var param_27:int;
    var param_28:int;
    var param_29:int;
    var param_30:int;
    var param_31:int;
    var param_32:int;
    var param_33:A.t;
    var result_19:W64.t;
    var result_20:int;
    var result_21:int;
    var result_22:int;
    var result_23:int;
    var param_34:int;
    var param_35:int;
    var param_36:int;
    var param_37:int;
    var param_38:int;
    var param_39:int;
    var param_40:A.t;
    var result_24:W256.t;
    var result_25:int;
    var result_26:int;
    var result_27:int;
    var result_28:int;
    var param_41:int;
    var param_42:int;
    var param_43:int;
    var param_44:int;
    var param_45:int;
    var param_46:int;
    var param_47:A.t;
    var result_29:W64.t;
    var result_30:int;
    var result_31:int;
    var result_32:int;
    var result_33:int;
    var param_48:int;
    var param_49:int;
    var param_50:int;
    var param_51:int;
    var param_52:int;
    var param_53:int;
    var param_54:A.t;
    var result_34:W256.t;
    var result_35:int;
    var result_36:int;
    var result_37:int;
    var result_38:int;
    var param_55:int;
    var param_56:int;
    var param_57:int;
    var param_58:int;
    var param_59:int;
    var param_60:int;
    var param_61:A.t;
    var result_39:W64.t;
    var result_40:int;
    var result_41:int;
    var result_42:int;
    var result_43:int;
    var param_62:int;
    var param_63:int;
    var param_64:int;
    var param_65:int;
    var param_66:int;
    var param_67:int;
    var param_68:A.t;
    var result_44:W256.t;
    var result_45:int;
    var result_46:int;
    var result_47:int;
    var result_48:int;
    var param_69:W256.t;
    var param_70:W256.t;
    var param_71:W256.t;
    var param_72:W256.t;
    var param_73:BArray224.t;
    var result_49:BArray224.t;
    var b_result:BArray224.t;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_param_3:A.t;
    var b_param_4:A.t;
    var b_param_5:A.t;
    var b_param_6:A.t;
    var b_param_7:A.t;
    var b_param_8:A.t;
    var trace___addstate_avx2:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_result <- witness;
    param_5 <- witness;
    param_12 <- witness;
    param_19 <- witness;
    param_26 <- witness;
    param_33 <- witness;
    param_40 <- witness;
    param_47 <- witness;
    param_54 <- witness;
    param_61 <- witness;
    param_68 <- witness;
    param_73 <- witness;
    result_49 <- witness;
    trace___addstate_avx2 <- [];
    trace___addstate_avx2 <-
    (trace___addstate_avx2 ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     (((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
      (A.is_init b_buf offset _LEN)) /\
     (BArray224.is_init b_st 0 224)))))]);
    trace___addstate_avx2 <-
    (trace___addstate_avx2 ++
    [(Assert,
     ((((0 <= _TRAILB) /\ (_TRAILB < 256)) /\ (0 <= aT)) /\
     (((aT + _LEN) + ((_TRAILB <> 0) ? 1 : 0)) <= 200)))]);
    trace___addstate_avx2 <-
    (trace___addstate_avx2 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    dELTA <- 0;
    if ((aT < 8)) {
      b_param_8 <- b_buf;
      param_5 <- buf;
      param_4 <- offset;
      param_3 <- dELTA;
      param_2 <- _LEN;
      param_1 <- _TRAILB;
      param_0 <- 0;
      param <- aT;
      (result_3, result_2, result_1, result_0, result, tmp__trace) <@ 
      RW.MM.__a_ilen_read_bcast_upto8_at (param_5, b_param_8, param_4, param_3,
      param_2, param_1, param_0, param);
      trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
      trace___addstate_avx2 <-
      (trace___addstate_avx2 ++
      [(Assert,
       (((param_0 <= param) /\ (param < (param_0 + 8))) ? ((8 <=
                                                           ((param - param_0) +
                                                           param_2)) ? 
                                                          ((((result_3 =
                                                             (param_3 +
                                                             ((param_0 + 8) -
                                                             param))) /\
                                                            (result_2 =
                                                            (param_2 -
                                                            ((param_0 + 8) -
                                                            param)))) /\
                                                           (result_1 =
                                                           param_1)) /\
                                                          (result_0 =
                                                          (param_0 + 8))) : 
                                                          ((((result_3 =
                                                             (param_3 +
                                                             param_2)) /\
                                                            (result_2 = 0)) /\
                                                           (result_1 = 0)) /\
                                                          (result_0 =
                                                          ((param + param_2) +
                                                          ((param_1 <> 0) ? 1 : 0))))) : 
       ((((result_3 = param_3) /\ (result_2 = param_2)) /\
        (result_1 = param_1)) /\
       (result_0 = param))))]);
      dELTA <- result_3;
      _LEN <- result_2;
      _TRAILB <- result_1;
      aT <- result_0;
      r0 <- result;
      st <- (BArray224.set256 st 0 ((BArray224.get256 st 0) `^` r0));
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      b_param_7 <- b_buf;
      param_12 <- buf;
      param_11 <- offset;
      param_10 <- dELTA;
      param_9 <- _LEN;
      param_8 <- _TRAILB;
      param_7 <- 8;
      param_6 <- aT;
      (result_8, result_7, result_6, result_5, result_4, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto32_at (param_12, b_param_7, param_11, param_10,
      param_9, param_8, param_7, param_6);
      trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
      trace___addstate_avx2 <-
      (trace___addstate_avx2 ++
      [(Assert,
       (((param_7 <= param_6) /\ (param_6 < (param_7 + 32))) ? ((32 <=
                                                                ((param_6 -
                                                                 param_7) +
                                                                param_9)) ? 
                                                               ((((result_8 =
                                                                  (param_10 +
                                                                  ((param_7 +
                                                                   32) -
                                                                  param_6))) /\
                                                                 (result_7 =
                                                                 (param_9 -
                                                                 ((param_7 +
                                                                  32) -
                                                                 param_6)))) /\
                                                                (result_6 =
                                                                param_8)) /\
                                                               (result_5 =
                                                               (param_7 + 32))) : 
                                                               ((((result_8 =
                                                                  (param_10 +
                                                                  param_9)) /\
                                                                 (result_7 =
                                                                 0)) /\
                                                                (result_6 =
                                                                0)) /\
                                                               (result_5 =
                                                               ((param_6 +
                                                                param_9) +
                                                               ((param_8 <>
                                                                0) ? 1 : 0))))) : 
       ((((result_8 = param_10) /\ (result_7 = param_9)) /\
        (result_6 = param_8)) /\
       (result_5 = param_6))))]);
      dELTA <- result_8;
      _LEN <- result_7;
      _TRAILB <- result_6;
      aT <- result_5;
      r1 <- result_4;
      st <- (BArray224.set256 st 1 ((BArray224.get256 st 1) `^` r1));
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      b_param_6 <- b_buf;
      param_19 <- buf;
      param_18 <- offset;
      param_17 <- dELTA;
      param_16 <- _LEN;
      param_15 <- _TRAILB;
      param_14 <- 40;
      param_13 <- aT;
      (result_13, result_12, result_11, result_10, result_9, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_19, b_param_6, param_18, param_17,
      param_16, param_15, param_14, param_13);
      trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
      trace___addstate_avx2 <-
      (trace___addstate_avx2 ++
      [(Assert,
       (((param_14 <= param_13) /\ (param_13 < (param_14 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_13 -
                                                                    param_14) +
                                                                   param_16)) ? 
                                                                  (((
                                                                    (
                                                                    result_13 =
                                                                    (
                                                                    param_17 +
                                                                    (
                                                                    (
                                                                    param_14 +
                                                                    8) -
                                                                    param_13))) /\
                                                                    (
                                                                    result_12 =
                                                                    (
                                                                    param_16 -
                                                                    (
                                                                    (
                                                                    param_14 +
                                                                    8) -
                                                                    param_13)))) /\
                                                                   (result_11 =
                                                                   param_15)) /\
                                                                  (result_10 =
                                                                  (param_14 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_13 =
                                                                    (
                                                                    param_17 +
                                                                    param_16)) /\
                                                                    (
                                                                    result_12 =
                                                                    0)) /\
                                                                   (result_11 =
                                                                   0)) /\
                                                                  (result_10 =
                                                                  ((param_13 +
                                                                   param_16) +
                                                                  ((param_15 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_13 = param_17) /\ (result_12 = param_16)) /\
        (result_11 = param_15)) /\
       (result_10 = param_13))))]);
      dELTA <- result_13;
      _LEN <- result_12;
      _TRAILB <- result_11;
      aT <- result_10;
      t64_2 <- result_9;
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        b_param_5 <- b_buf;
        param_26 <- buf;
        param_25 <- offset;
        param_24 <- dELTA;
        param_23 <- _LEN;
        param_22 <- _TRAILB;
        param_21 <- 48;
        param_20 <- aT;
        (result_18, result_17, result_16, result_15, result_14, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto32_at (param_26, b_param_5, param_25, param_24,
        param_23, param_22, param_21, param_20);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_21 <= param_20) /\ (param_20 < (param_21 + 32))) ? 
         ((32 <= ((param_20 - param_21) + param_23)) ? ((((result_18 =
                                                          (param_24 +
                                                          ((param_21 + 32) -
                                                          param_20))) /\
                                                         (result_17 =
                                                         (param_23 -
                                                         ((param_21 + 32) -
                                                         param_20)))) /\
                                                        (result_16 =
                                                        param_22)) /\
                                                       (result_15 =
                                                       (param_21 + 32))) : 
         ((((result_18 = (param_24 + param_23)) /\ (result_17 = 0)) /\
          (result_16 = 0)) /\
         (result_15 = ((param_20 + param_23) + ((param_22 <> 0) ? 1 : 0))))) : 
         ((((result_18 = param_24) /\ (result_17 = param_23)) /\
          (result_16 = param_22)) /\
         (result_15 = param_20))))]);
        dELTA <- result_18;
        _LEN <- result_17;
        _TRAILB <- result_16;
        aT <- result_15;
        r3 <- result_14;
        b_param_4 <- b_buf;
        param_33 <- buf;
        param_32 <- offset;
        param_31 <- dELTA;
        param_30 <- _LEN;
        param_29 <- _TRAILB;
        param_28 <- 80;
        param_27 <- aT;
        (result_23, result_22, result_21, result_20, result_19, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto8_at (param_33, b_param_4, param_32, param_31,
        param_30, param_29, param_28, param_27);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_28 <= param_27) /\ (param_27 < (param_28 + 8))) ? (
                                                                    (8 <=
                                                                    (
                                                                    (
                                                                    param_27 -
                                                                    param_28) +
                                                                    param_30)) ? 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_23 =
                                                                    (
                                                                    param_31 +
                                                                    (
                                                                    (
                                                                    param_28 +
                                                                    8) -
                                                                    param_27))) /\
                                                                    (
                                                                    result_22 =
                                                                    (
                                                                    param_30 -
                                                                    (
                                                                    (
                                                                    param_28 +
                                                                    8) -
                                                                    param_27)))) /\
                                                                    (
                                                                    result_21 =
                                                                    param_29)) /\
                                                                    (
                                                                    result_20 =
                                                                    (
                                                                    param_28 +
                                                                    8))) : 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_23 =
                                                                    (
                                                                    param_31 +
                                                                    param_30)) /\
                                                                    (
                                                                    result_22 =
                                                                    0)) /\
                                                                    (
                                                                    result_21 =
                                                                    0)) /\
                                                                    (
                                                                    result_20 =
                                                                    (
                                                                    (
                                                                    param_27 +
                                                                    param_30) +
                                                                    (
                                                                    (
                                                                    param_29 <>
                                                                    0) ? 1 : 0))))) : 
         ((((result_23 = param_31) /\ (result_22 = param_30)) /\
          (result_21 = param_29)) /\
         (result_20 = param_27))))]);
        dELTA <- result_23;
        _LEN <- result_22;
        _TRAILB <- result_21;
        aT <- result_20;
        t64_3 <- result_19;
        t128_2 <- (VMOV_64 t64_3);
        b_param_3 <- b_buf;
        param_40 <- buf;
        param_39 <- offset;
        param_38 <- dELTA;
        param_37 <- _LEN;
        param_36 <- _TRAILB;
        param_35 <- 88;
        param_34 <- aT;
        (result_28, result_27, result_26, result_25, result_24, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto32_at (param_40, b_param_3, param_39, param_38,
        param_37, param_36, param_35, param_34);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_35 <= param_34) /\ (param_34 < (param_35 + 32))) ? 
         ((32 <= ((param_34 - param_35) + param_37)) ? ((((result_28 =
                                                          (param_38 +
                                                          ((param_35 + 32) -
                                                          param_34))) /\
                                                         (result_27 =
                                                         (param_37 -
                                                         ((param_35 + 32) -
                                                         param_34)))) /\
                                                        (result_26 =
                                                        param_36)) /\
                                                       (result_25 =
                                                       (param_35 + 32))) : 
         ((((result_28 = (param_38 + param_37)) /\ (result_27 = 0)) /\
          (result_26 = 0)) /\
         (result_25 = ((param_34 + param_37) + ((param_36 <> 0) ? 1 : 0))))) : 
         ((((result_28 = param_38) /\ (result_27 = param_37)) /\
          (result_26 = param_36)) /\
         (result_25 = param_34))))]);
        dELTA <- result_28;
        _LEN <- result_27;
        _TRAILB <- result_26;
        aT <- result_25;
        r4 <- result_24;
        b_param_2 <- b_buf;
        param_47 <- buf;
        param_46 <- offset;
        param_45 <- dELTA;
        param_44 <- _LEN;
        param_43 <- _TRAILB;
        param_42 <- 120;
        param_41 <- aT;
        (result_33, result_32, result_31, result_30, result_29, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto8_at (param_47, b_param_2, param_46, param_45,
        param_44, param_43, param_42, param_41);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_42 <= param_41) /\ (param_41 < (param_42 + 8))) ? (
                                                                    (8 <=
                                                                    (
                                                                    (
                                                                    param_41 -
                                                                    param_42) +
                                                                    param_44)) ? 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_33 =
                                                                    (
                                                                    param_45 +
                                                                    (
                                                                    (
                                                                    param_42 +
                                                                    8) -
                                                                    param_41))) /\
                                                                    (
                                                                    result_32 =
                                                                    (
                                                                    param_44 -
                                                                    (
                                                                    (
                                                                    param_42 +
                                                                    8) -
                                                                    param_41)))) /\
                                                                    (
                                                                    result_31 =
                                                                    param_43)) /\
                                                                    (
                                                                    result_30 =
                                                                    (
                                                                    param_42 +
                                                                    8))) : 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_33 =
                                                                    (
                                                                    param_45 +
                                                                    param_44)) /\
                                                                    (
                                                                    result_32 =
                                                                    0)) /\
                                                                    (
                                                                    result_31 =
                                                                    0)) /\
                                                                    (
                                                                    result_30 =
                                                                    (
                                                                    (
                                                                    param_41 +
                                                                    param_44) +
                                                                    (
                                                                    (
                                                                    param_43 <>
                                                                    0) ? 1 : 0))))) : 
         ((((result_33 = param_45) /\ (result_32 = param_44)) /\
          (result_31 = param_43)) /\
         (result_30 = param_41))))]);
        dELTA <- result_33;
        _LEN <- result_32;
        _TRAILB <- result_31;
        aT <- result_30;
        t64_4 <- result_29;
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        b_param_1 <- b_buf;
        param_54 <- buf;
        param_53 <- offset;
        param_52 <- dELTA;
        param_51 <- _LEN;
        param_50 <- _TRAILB;
        param_49 <- 128;
        param_48 <- aT;
        (result_38, result_37, result_36, result_35, result_34, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto32_at (param_54, b_param_1, param_53, param_52,
        param_51, param_50, param_49, param_48);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_49 <= param_48) /\ (param_48 < (param_49 + 32))) ? 
         ((32 <= ((param_48 - param_49) + param_51)) ? ((((result_38 =
                                                          (param_52 +
                                                          ((param_49 + 32) -
                                                          param_48))) /\
                                                         (result_37 =
                                                         (param_51 -
                                                         ((param_49 + 32) -
                                                         param_48)))) /\
                                                        (result_36 =
                                                        param_50)) /\
                                                       (result_35 =
                                                       (param_49 + 32))) : 
         ((((result_38 = (param_52 + param_51)) /\ (result_37 = 0)) /\
          (result_36 = 0)) /\
         (result_35 = ((param_48 + param_51) + ((param_50 <> 0) ? 1 : 0))))) : 
         ((((result_38 = param_52) /\ (result_37 = param_51)) /\
          (result_36 = param_50)) /\
         (result_35 = param_48))))]);
        dELTA <- result_38;
        _LEN <- result_37;
        _TRAILB <- result_36;
        aT <- result_35;
        r5 <- result_34;
        b_param_0 <- b_buf;
        param_61 <- buf;
        param_60 <- offset;
        param_59 <- dELTA;
        param_58 <- _LEN;
        param_57 <- _TRAILB;
        param_56 <- 160;
        param_55 <- aT;
        (result_43, result_42, result_41, result_40, result_39, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto8_at (param_61, b_param_0, param_60, param_59,
        param_58, param_57, param_56, param_55);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_56 <= param_55) /\ (param_55 < (param_56 + 8))) ? (
                                                                    (8 <=
                                                                    (
                                                                    (
                                                                    param_55 -
                                                                    param_56) +
                                                                    param_58)) ? 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_43 =
                                                                    (
                                                                    param_59 +
                                                                    (
                                                                    (
                                                                    param_56 +
                                                                    8) -
                                                                    param_55))) /\
                                                                    (
                                                                    result_42 =
                                                                    (
                                                                    param_58 -
                                                                    (
                                                                    (
                                                                    param_56 +
                                                                    8) -
                                                                    param_55)))) /\
                                                                    (
                                                                    result_41 =
                                                                    param_57)) /\
                                                                    (
                                                                    result_40 =
                                                                    (
                                                                    param_56 +
                                                                    8))) : 
                                                                    (
                                                                    (
                                                                    (
                                                                    (
                                                                    result_43 =
                                                                    (
                                                                    param_59 +
                                                                    param_58)) /\
                                                                    (
                                                                    result_42 =
                                                                    0)) /\
                                                                    (
                                                                    result_41 =
                                                                    0)) /\
                                                                    (
                                                                    result_40 =
                                                                    (
                                                                    (
                                                                    param_55 +
                                                                    param_58) +
                                                                    (
                                                                    (
                                                                    param_57 <>
                                                                    0) ? 1 : 0))))) : 
         ((((result_43 = param_59) /\ (result_42 = param_58)) /\
          (result_41 = param_57)) /\
         (result_40 = param_55))))]);
        dELTA <- result_43;
        _LEN <- result_42;
        _TRAILB <- result_41;
        aT <- result_40;
        t64_5 <- result_39;
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        b_param <- b_buf;
        param_68 <- buf;
        param_67 <- offset;
        param_66 <- dELTA;
        param_65 <- _LEN;
        param_64 <- _TRAILB;
        param_63 <- 168;
        param_62 <- aT;
        (result_48, result_47, result_46, result_45, result_44, tmp__trace) <@ 
        RW.MM.__a_ilen_read_upto32_at (param_68, b_param, param_67, param_66,
        param_65, param_64, param_63, param_62);
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert,
         (((param_63 <= param_62) /\ (param_62 < (param_63 + 32))) ? 
         ((32 <= ((param_62 - param_63) + param_65)) ? ((((result_48 =
                                                          (param_66 +
                                                          ((param_63 + 32) -
                                                          param_62))) /\
                                                         (result_47 =
                                                         (param_65 -
                                                         ((param_63 + 32) -
                                                         param_62)))) /\
                                                        (result_46 =
                                                        param_64)) /\
                                                       (result_45 =
                                                       (param_63 + 32))) : 
         ((((result_48 = (param_66 + param_65)) /\ (result_47 = 0)) /\
          (result_46 = 0)) /\
         (result_45 = ((param_62 + param_65) + ((param_64 <> 0) ? 1 : 0))))) : 
         ((((result_48 = param_66) /\ (result_47 = param_65)) /\
          (result_46 = param_64)) /\
         (result_45 = param_62))))]);
        dELTA <- result_48;
        aT <- result_45;
        r6 <- result_44;
        param_73 <- st;
        param_72 <- r3;
        param_71 <- r4;
        param_70 <- r5;
        param_69 <- r6;
        (aux, aux_0, tmp__trace) <@ M.__addstate_r3456_avx2 (param_73,
        (BArray224.init_arr (W8.of_int 255)), param_72, param_71, param_70,
        param_69);
        result_49 <- aux;
        b_result <- aux_0;
        trace___addstate_avx2 <- (trace___addstate_avx2 ++ tmp__trace);
        trace___addstate_avx2 <-
        (trace___addstate_avx2 ++
        [(Assert, (BArray224.is_init b_result 0 224))]);
        st <- result_49;
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st <- (BArray224.set256 st 2 ((BArray224.get256 st 2) `^` r2));
    } else {
      
    }
    trace___addstate_avx2 <-
    (trace___addstate_avx2 ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___addstate_avx2 <-
    (trace___addstate_avx2 ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    b_st <- (BArray224.init_arr (W8.of_int 255));
    return (st, b_st, aT, offset, trace___addstate_avx2);
  }
  proc __absorb_avx2 (st:BArray224.t, b_st:BArray224.t, aT:int,
                      buf:A.t, b_buf:A.t, _TRAILB:int,
                      _RATE8:int) : BArray224.t * BArray224.t * int * trace = {
    var aux:BArray224.t;
    var aux_0:BArray224.t;
    var aux_1:int;
    var aux_2:int;
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var param:int;
    var param_0:int;
    var param_1:int;
    var param_2:A.t;
    var param_3:int;
    var param_4:BArray224.t;
    var result:int;
    var result_0:int;
    var result_1:BArray224.t;
    var param_5:BArray224.t;
    var result_2:BArray224.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:A.t;
    var param_10:int;
    var param_11:BArray224.t;
    var result_3:int;
    var result_4:int;
    var result_5:BArray224.t;
    var param_12:BArray224.t;
    var result_6:BArray224.t;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var param_16:A.t;
    var param_17:int;
    var param_18:BArray224.t;
    var result_7:int;
    var result_8:int;
    var result_9:BArray224.t;
    var param_19:int;
    var param_20:BArray224.t;
    var result_10:BArray224.t;
    var b_result:BArray224.t;
    var b_result_0:BArray224.t;
    var b_result_1:BArray224.t;
    var b_result_2:BArray224.t;
    var b_result_3:BArray224.t;
    var b_result_4:BArray224.t;
    var trace___absorb_avx2:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_16 <- witness;
    param_18 <- witness;
    param_20 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_9 <- witness;
    result_10 <- witness;
    trace___absorb_avx2 <- [];
    trace___absorb_avx2 <-
    (trace___absorb_avx2 ++
    [(Assert,
     ((((((((0 < _RATE8) /\ (_RATE8 < 200)) /\ (0 <= _TRAILB)) /\
         (_TRAILB < 256)) /\
        (0 <= aT)) /\
       (aT < _RATE8)) /\
      (A.is_init b_buf 0 _ASIZE)) /\
     (BArray224.is_init b_st 0 224)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      param_4 <- st;
      param_3 <- aT;
      param_2 <- buf;
      param_1 <- offset;
      param_0 <- (_RATE8 - aT);
      param <- 0;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2 (param_4,
      (BArray224.init_arr (W8.of_int 255)), param_3, param_2,
      (A.init_arr (W8.of_int 255)), param_1, param_0, param);
      result_1 <- aux;
      b_result_4 <- aux_0;
      result_0 <- aux_1;
      result <- aux_2;
      trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
      trace___absorb_avx2 <-
      (trace___absorb_avx2 ++
      [(Assert,
       (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
       (((0 <= (param_1 + param_0)) /\
        ((param_1 + param_0) <= 18446744073709551615)) /\
       (((BArray224.is_init b_result_4 0 224) /\
        (result_0 = ((param_3 + param_0) + ((param <> 0) ? 1 : 0)))) /\
       (result = (param_1 + param_0))))))]);
      trace___absorb_avx2 <-
      (trace___absorb_avx2 ++
      [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
      st <- result_1;
      offset <- result;
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      param_5 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2 (param_5,
      (BArray224.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_3 <- aux_0;
      trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
      trace___absorb_avx2 <-
      (trace___absorb_avx2 ++
      [(Assert, (BArray224.is_init b_result_3 0 224))]);
      st <- result_2;
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      trace___absorb_avx2 <-
      (trace___absorb_avx2 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_11 <- st;
        param_10 <- 0;
        param_9 <- buf;
        param_8 <- offset;
        param_7 <- _RATE8;
        param_6 <- 0;
        (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2 (param_11,
        (BArray224.init_arr (W8.of_int 255)), param_10, param_9,
        (A.init_arr (W8.of_int 255)), param_8, param_7, param_6);
        result_5 <- aux;
        b_result_2 <- aux_0;
        result_4 <- aux_1;
        result_3 <- aux_2;
        trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
        trace___absorb_avx2 <-
        (trace___absorb_avx2 ++
        [(Assert,
         (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
         (((0 <= (param_8 + param_7)) /\
          ((param_8 + param_7) <= 18446744073709551615)) /\
         (((BArray224.is_init b_result_2 0 224) /\
          (result_4 = ((param_10 + param_7) + ((param_6 <> 0) ? 1 : 0)))) /\
         (result_3 = (param_8 + param_7))))))]);
        trace___absorb_avx2 <-
        (trace___absorb_avx2 ++
        [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
        st <- result_5;
        offset <- result_3;
        param_12 <- st;
        (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2 (param_12,
        (BArray224.init_arr (W8.of_int 255)));
        result_6 <- aux;
        b_result_1 <- aux_0;
        trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
        trace___absorb_avx2 <-
        (trace___absorb_avx2 ++
        [(Assert, (BArray224.is_init b_result_1 0 224))]);
        st <- result_6;
        trace___absorb_avx2 <-
        (trace___absorb_avx2 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_avx2 <-
        (trace___absorb_avx2 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    param_18 <- st;
    param_17 <- aT;
    param_16 <- buf;
    param_15 <- offset;
    param_14 <- _LEN;
    param_13 <- _TRAILB;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2 (param_18,
    (BArray224.init_arr (W8.of_int 255)), param_17, param_16,
    (A.init_arr (W8.of_int 255)), param_15, param_14, param_13);
    result_9 <- aux;
    b_result_0 <- aux_0;
    result_8 <- aux_1;
    result_7 <- aux_2;
    trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
    trace___absorb_avx2 <-
    (trace___absorb_avx2 ++
    [(Assert,
     (((0 <= param_14) /\ (param_14 <= 18446744073709551615)) /\
     (((0 <= (param_15 + param_14)) /\
      ((param_15 + param_14) <= 18446744073709551615)) /\
     (((BArray224.is_init b_result_0 0 224) /\
      (result_8 = ((param_17 + param_14) + ((param_13 <> 0) ? 1 : 0)))) /\
     (result_7 = (param_15 + param_14))))))]);
    trace___absorb_avx2 <-
    (trace___absorb_avx2 ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    st <- result_9;
    aT <- result_8;
    if ((_TRAILB <> 0)) {
      param_20 <- st;
      param_19 <- _RATE8;
      (aux, aux_0, tmp__trace) <@ M.__addratebit_avx2 (param_20,
      (BArray224.init_arr (W8.of_int 255)), param_19);
      result_10 <- aux;
      b_result <- aux_0;
      trace___absorb_avx2 <- (trace___absorb_avx2 ++ tmp__trace);
      trace___absorb_avx2 <-
      (trace___absorb_avx2 ++ [(Assert, (BArray224.is_init b_result 0 224))]);
      st <- result_10;
    } else {
      
    }
    b_st <- (BArray224.init_arr (W8.of_int 255));
    return (st, b_st, aT, trace___absorb_avx2);
  }
  proc __dumpstate_avx2 (buf:A.t, b_buf:A.t, offset:int,
                         _LEN:int, st:BArray224.t, b_st:BArray224.t) : 
  A.t * A.t * int * trace = {
    var dELTA:int;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var param:W256.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result:int;
    var result_0:int;
    var result_1:A.t;
    var param_4:W256.t;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var param_8:A.t;
    var result_2:int;
    var result_3:int;
    var result_4:A.t;
    var param_9:W256.t;
    var param_10:int;
    var param_11:int;
    var param_12:int;
    var param_13:A.t;
    var result_5:int;
    var result_6:int;
    var result_7:A.t;
    var param_14:W64.t;
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:A.t;
    var result_8:int;
    var result_9:int;
    var result_10:A.t;
    var param_19:W256.t;
    var param_20:int;
    var param_21:int;
    var param_22:int;
    var param_23:A.t;
    var result_11:int;
    var result_12:int;
    var result_13:A.t;
    var param_24:W64.t;
    var param_25:int;
    var param_26:int;
    var param_27:int;
    var param_28:A.t;
    var result_14:int;
    var result_15:int;
    var result_16:A.t;
    var param_29:W256.t;
    var param_30:int;
    var param_31:int;
    var param_32:int;
    var param_33:A.t;
    var result_17:int;
    var result_18:int;
    var result_19:A.t;
    var param_34:W64.t;
    var param_35:int;
    var param_36:int;
    var param_37:int;
    var param_38:A.t;
    var result_20:int;
    var result_21:int;
    var result_22:A.t;
    var param_39:W256.t;
    var param_40:int;
    var param_41:int;
    var param_42:int;
    var param_43:A.t;
    var result_23:int;
    var result_24:int;
    var result_25:A.t;
    var param_44:W64.t;
    var param_45:int;
    var param_46:int;
    var param_47:int;
    var param_48:A.t;
    var result_26:int;
    var result_27:int;
    var result_28:A.t;
    var param_49:W256.t;
    var param_50:int;
    var param_51:int;
    var param_52:int;
    var param_53:A.t;
    var result_29:int;
    var result_30:int;
    var result_31:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var b_result_0:A.t;
    var b_param_0:A.t;
    var b_result_1:A.t;
    var b_param_1:A.t;
    var b_result_2:A.t;
    var b_param_2:A.t;
    var b_result_3:A.t;
    var b_param_3:A.t;
    var b_result_4:A.t;
    var b_param_4:A.t;
    var b_result_5:A.t;
    var b_param_5:A.t;
    var b_result_6:A.t;
    var b_param_6:A.t;
    var b_result_7:A.t;
    var b_param_7:A.t;
    var b_result_8:A.t;
    var b_param_8:A.t;
    var b_result_9:A.t;
    var b_param_9:A.t;
    var trace___dumpstate_avx2:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_param_9 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_result_8 <- witness;
    b_result_9 <- witness;
    param_3 <- witness;
    param_8 <- witness;
    param_13 <- witness;
    param_18 <- witness;
    param_23 <- witness;
    param_28 <- witness;
    param_33 <- witness;
    param_38 <- witness;
    param_43 <- witness;
    param_48 <- witness;
    param_53 <- witness;
    result_1 <- witness;
    result_4 <- witness;
    result_7 <- witness;
    result_10 <- witness;
    result_13 <- witness;
    result_16 <- witness;
    result_19 <- witness;
    result_22 <- witness;
    result_25 <- witness;
    result_28 <- witness;
    result_31 <- witness;
    trace___dumpstate_avx2 <- [];
    trace___dumpstate_avx2 <-
    (trace___dumpstate_avx2 ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     ((((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
       (BArray224.is_init b_st 0 224)) /\
      (_LEN <= 200)) /\
     (A.is_init b_buf 0 offset)))))]);
    trace___dumpstate_avx2 <-
    (trace___dumpstate_avx2 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    dELTA <- 0;
    if ((8 <= _LEN)) {
      b_param_8 <- b_buf;
      param_3 <- buf;
      param_2 <- offset;
      param_1 <- dELTA;
      param_0 <- 8;
      param <- (BArray224.get256 st 0);
      (result_1, b_result_8, result_0, result, tmp__trace) <@ RW.MM.__a_ilen_write_upto32 (
      param_3, b_param_8, param_2, param_1, param_0, param);
      trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
      trace___dumpstate_avx2 <-
      (trace___dumpstate_avx2 ++
      [(Assert,
       (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
       (((0 <= (param_2 + param_1)) /\
        ((param_2 + param_1) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                      param_0 : 32))) /\
        (((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                      param_0 : 32)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_2 + param_1) +
         ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                      param_0 : 32)))) /\
        (((param_2 + param_1) +
         ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                      param_0 : 32))) <=
        18446744073709551615)) /\
       (((result_0 =
         (param_1 +
         ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                      param_0 : 32)))) /\
        (result =
        (param_0 -
        ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                     param_0 : 32))))) /\
       (A.is_init b_result_8 0
       ((param_2 + param_1) +
       ((((param_0 < 32) ? param_0 : 32) < 0) ? 0 : ((param_0 < 32) ? 
                                                    param_0 : 32)))
       )))))))]);
      b_buf <- b_result_8;
      buf <- result_1;
      dELTA <- result_0;
      _LEN <- (_LEN - 8);
    } else {
      b_param_9 <- b_buf;
      param_8 <- buf;
      param_7 <- offset;
      param_6 <- dELTA;
      param_5 <- _LEN;
      param_4 <- (BArray224.get256 st 0);
      (result_4, b_result_9, result_3, result_2, tmp__trace) <@ RW.MM.__a_ilen_write_upto32 (
      param_8, b_param_9, param_7, param_6, param_5, param_4);
      trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
      trace___dumpstate_avx2 <-
      (trace___dumpstate_avx2 ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                      param_5 : 32))) /\
        (((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                      param_5 : 32)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_7 + param_6) +
         ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                      param_5 : 32)))) /\
        (((param_7 + param_6) +
         ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                      param_5 : 32))) <=
        18446744073709551615)) /\
       (((result_3 =
         (param_6 +
         ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                      param_5 : 32)))) /\
        (result_2 =
        (param_5 -
        ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                     param_5 : 32))))) /\
       (A.is_init b_result_9 0
       ((param_7 + param_6) +
       ((((param_5 < 32) ? param_5 : 32) < 0) ? 0 : ((param_5 < 32) ? 
                                                    param_5 : 32)))
       )))))))]);
      b_buf <- b_result_9;
      buf <- result_4;
      dELTA <- result_3;
      _LEN <- result_2;
    }
    b_param_7 <- b_buf;
    param_13 <- buf;
    param_12 <- offset;
    param_11 <- dELTA;
    param_10 <- _LEN;
    param_9 <- (BArray224.get256 st 1);
    (result_7, b_result_7, result_6, result_5, tmp__trace) <@ RW.MM.__a_ilen_write_upto32 (
    param_13, b_param_7, param_12, param_11, param_10, param_9);
    trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
    trace___dumpstate_avx2 <-
    (trace___dumpstate_avx2 ++
    [(Assert,
     (((0 <= param_11) /\ (param_11 <= 18446744073709551615)) /\
     (((0 <= (param_12 + param_11)) /\
      ((param_12 + param_11) <= 18446744073709551615)) /\
     (((0 <=
       ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                      param_10 : 32))) /\
      (((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                      param_10 : 32)) <=
      18446744073709551615)) /\
     (((0 <=
       ((param_12 + param_11) +
       ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                      param_10 : 32)))) /\
      (((param_12 + param_11) +
       ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                      param_10 : 32))) <=
      18446744073709551615)) /\
     (((result_6 =
       (param_11 +
       ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                      param_10 : 32)))) /\
      (result_5 =
      (param_10 -
      ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                     param_10 : 32))))) /\
     (A.is_init b_result_7 0
     ((param_12 + param_11) +
     ((((param_10 < 32) ? param_10 : 32) < 0) ? 0 : ((param_10 < 32) ? 
                                                    param_10 : 32)))
     )))))))]);
    b_buf <- b_result_7;
    buf <- result_7;
    dELTA <- result_6;
    _LEN <- result_5;
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 (BArray224.get256 st 2) (W8.of_int 1));
      t128_0 <- (truncateu128 (BArray224.get256 st 2));
      t <- (MOVV_64 (truncateu64 t128_1));
      b_param_6 <- b_buf;
      param_18 <- buf;
      param_17 <- offset;
      param_16 <- dELTA;
      param_15 <- _LEN;
      param_14 <- t;
      (result_10, b_result_6, result_9, result_8, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_18, b_param_6, param_17, param_16, param_15, param_14);
      trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
      trace___dumpstate_avx2 <-
      (trace___dumpstate_avx2 ++
      [(Assert,
       (((0 <= param_16) /\ (param_16 <= 18446744073709551615)) /\
       (((0 <= (param_17 + param_16)) /\
        ((param_17 + param_16) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) /\
        (((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_17 + param_16) +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)))) /\
        (((param_17 + param_16) +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) <=
        18446744073709551615)) /\
       (((result_9 =
         (param_16 +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)))) /\
        (result_8 =
        (param_15 -
        ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                     param_15 : 8))))) /\
       (A.is_init b_result_6 0
       ((param_17 + param_16) +
       ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                    param_15 : 8)))
       )))))))]);
      b_buf <- b_result_6;
      buf <- result_10;
      dELTA <- result_9;
      _LEN <- result_8;
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 (BArray224.get256 st 3) (BArray224.get256 st 4)
        (W8.of_int 240));
        t256_1 <-
        (VPBLEND_8u32 (BArray224.get256 st 4) (BArray224.get256 st 3)
        (W8.of_int 240));
        t256_2 <-
        (VPBLEND_8u32 (BArray224.get256 st 5) (BArray224.get256 st 6)
        (W8.of_int 240));
        t256_3 <-
        (VPBLEND_8u32 (BArray224.get256 st 6) (BArray224.get256 st 5)
        (W8.of_int 240));
        t256_4 <- (VPBLEND_8u32 t256_0 t256_3 (W8.of_int 195));
        b_param_5 <- b_buf;
        param_23 <- buf;
        param_22 <- offset;
        param_21 <- dELTA;
        param_20 <- _LEN;
        param_19 <- t256_4;
        (result_13, b_result_5, result_12, result_11, tmp__trace) <@ 
        RW.MM.__a_ilen_write_upto32 (param_23, b_param_5, param_22, param_21,
        param_20, param_19);
        trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
        trace___dumpstate_avx2 <-
        (trace___dumpstate_avx2 ++
        [(Assert,
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_22 + param_21)) /\
          ((param_22 + param_21) <= 18446744073709551615)) /\
         (((0 <=
           ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                          param_20 : 32))) /\
          (((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                          param_20 : 32)) <=
          18446744073709551615)) /\
         (((0 <=
           ((param_22 + param_21) +
           ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                          param_20 : 32)))) /\
          (((param_22 + param_21) +
           ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                          param_20 : 32))) <=
          18446744073709551615)) /\
         (((result_12 =
           (param_21 +
           ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                          param_20 : 32)))) /\
          (result_11 =
          (param_20 -
          ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                         param_20 : 32))))) /\
         (A.is_init b_result_5 0
         ((param_22 + param_21) +
         ((((param_20 < 32) ? param_20 : 32) < 0) ? 0 : ((param_20 < 32) ? 
                                                        param_20 : 32)))
         )))))))]);
        b_buf <- b_result_5;
        buf <- result_13;
        dELTA <- result_12;
        _LEN <- result_11;
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          b_param_4 <- b_buf;
          param_28 <- buf;
          param_27 <- offset;
          param_26 <- dELTA;
          param_25 <- _LEN;
          param_24 <- t;
          (result_16, b_result_4, result_15, result_14, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto8 (param_28, b_param_4, param_27, param_26,
          param_25, param_24);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_26) /\ (param_26 <= 18446744073709551615)) /\
           (((0 <= (param_27 + param_26)) /\
            ((param_27 + param_26) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                          param_25 : 8))) /\
            (((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                          param_25 : 8)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_27 + param_26) +
             ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                          param_25 : 8)))) /\
            (((param_27 + param_26) +
             ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                          param_25 : 8))) <=
            18446744073709551615)) /\
           (((result_15 =
             (param_26 +
             ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                          param_25 : 8)))) /\
            (result_14 =
            (param_25 -
            ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                         param_25 : 8))))) /\
           (A.is_init b_result_4 0
           ((param_27 + param_26) +
           ((((param_25 < 8) ? param_25 : 8) < 0) ? 0 : ((param_25 < 8) ? 
                                                        param_25 : 8)))
           )))))))]);
          b_buf <- b_result_4;
          buf <- result_16;
          dELTA <- result_15;
          _LEN <- result_14;
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <- (VPBLEND_8u32 t256_3 t256_1 (W8.of_int 195));
          b_param_3 <- b_buf;
          param_33 <- buf;
          param_32 <- offset;
          param_31 <- dELTA;
          param_30 <- _LEN;
          param_29 <- t256_4;
          (result_19, b_result_3, result_18, result_17, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto32 (param_33, b_param_3, param_32, param_31,
          param_30, param_29);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_31) /\ (param_31 <= 18446744073709551615)) /\
           (((0 <= (param_32 + param_31)) /\
            ((param_32 + param_31) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                            param_30 : 32))) /\
            (((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                            param_30 : 32)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_32 + param_31) +
             ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                            param_30 : 32)))) /\
            (((param_32 + param_31) +
             ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                            param_30 : 32))) <=
            18446744073709551615)) /\
           (((result_18 =
             (param_31 +
             ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                            param_30 : 32)))) /\
            (result_17 =
            (param_30 -
            ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                           param_30 : 32))))) /\
           (A.is_init b_result_3 0
           ((param_32 + param_31) +
           ((((param_30 < 32) ? param_30 : 32) < 0) ? 0 : ((param_30 < 32) ? 
                                                          param_30 : 32)))
           )))))))]);
          b_buf <- b_result_3;
          buf <- result_19;
          dELTA <- result_18;
          _LEN <- result_17;
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          b_param_2 <- b_buf;
          param_38 <- buf;
          param_37 <- offset;
          param_36 <- dELTA;
          param_35 <- _LEN;
          param_34 <- t;
          (result_22, b_result_2, result_21, result_20, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto8 (param_38, b_param_2, param_37, param_36,
          param_35, param_34);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_36) /\ (param_36 <= 18446744073709551615)) /\
           (((0 <= (param_37 + param_36)) /\
            ((param_37 + param_36) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                          param_35 : 8))) /\
            (((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                          param_35 : 8)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_37 + param_36) +
             ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                          param_35 : 8)))) /\
            (((param_37 + param_36) +
             ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                          param_35 : 8))) <=
            18446744073709551615)) /\
           (((result_21 =
             (param_36 +
             ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                          param_35 : 8)))) /\
            (result_20 =
            (param_35 -
            ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                         param_35 : 8))))) /\
           (A.is_init b_result_2 0
           ((param_37 + param_36) +
           ((((param_35 < 8) ? param_35 : 8) < 0) ? 0 : ((param_35 < 8) ? 
                                                        param_35 : 8)))
           )))))))]);
          b_buf <- b_result_2;
          buf <- result_22;
          dELTA <- result_21;
          _LEN <- result_20;
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <- (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 195));
          b_param_1 <- b_buf;
          param_43 <- buf;
          param_42 <- offset;
          param_41 <- dELTA;
          param_40 <- _LEN;
          param_39 <- t256_4;
          (result_25, b_result_1, result_24, result_23, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto32 (param_43, b_param_1, param_42, param_41,
          param_40, param_39);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_41) /\ (param_41 <= 18446744073709551615)) /\
           (((0 <= (param_42 + param_41)) /\
            ((param_42 + param_41) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                            param_40 : 32))) /\
            (((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                            param_40 : 32)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_42 + param_41) +
             ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                            param_40 : 32)))) /\
            (((param_42 + param_41) +
             ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                            param_40 : 32))) <=
            18446744073709551615)) /\
           (((result_24 =
             (param_41 +
             ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                            param_40 : 32)))) /\
            (result_23 =
            (param_40 -
            ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                           param_40 : 32))))) /\
           (A.is_init b_result_1 0
           ((param_42 + param_41) +
           ((((param_40 < 32) ? param_40 : 32) < 0) ? 0 : ((param_40 < 32) ? 
                                                          param_40 : 32)))
           )))))))]);
          b_buf <- b_result_1;
          buf <- result_25;
          dELTA <- result_24;
          _LEN <- result_23;
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          b_param_0 <- b_buf;
          param_48 <- buf;
          param_47 <- offset;
          param_46 <- dELTA;
          param_45 <- _LEN;
          param_44 <- t;
          (result_28, b_result_0, result_27, result_26, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto8 (param_48, b_param_0, param_47, param_46,
          param_45, param_44);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_46) /\ (param_46 <= 18446744073709551615)) /\
           (((0 <= (param_47 + param_46)) /\
            ((param_47 + param_46) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                          param_45 : 8))) /\
            (((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                          param_45 : 8)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_47 + param_46) +
             ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                          param_45 : 8)))) /\
            (((param_47 + param_46) +
             ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                          param_45 : 8))) <=
            18446744073709551615)) /\
           (((result_27 =
             (param_46 +
             ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                          param_45 : 8)))) /\
            (result_26 =
            (param_45 -
            ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                         param_45 : 8))))) /\
           (A.is_init b_result_0 0
           ((param_47 + param_46) +
           ((((param_45 < 8) ? param_45 : 8) < 0) ? 0 : ((param_45 < 8) ? 
                                                        param_45 : 8)))
           )))))))]);
          b_buf <- b_result_0;
          buf <- result_28;
          dELTA <- result_27;
          _LEN <- result_26;
        } else {
          
        }
        if ((0 < _LEN)) {
          t256_4 <- (VPBLEND_8u32 t256_1 t256_2 (W8.of_int 195));
          b_param <- b_buf;
          param_53 <- buf;
          param_52 <- offset;
          param_51 <- dELTA;
          param_50 <- _LEN;
          param_49 <- t256_4;
          (result_31, b_result, result_30, result_29, tmp__trace) <@ 
          RW.MM.__a_ilen_write_upto32 (param_53, b_param, param_52, param_51,
          param_50, param_49);
          trace___dumpstate_avx2 <- (trace___dumpstate_avx2 ++ tmp__trace);
          trace___dumpstate_avx2 <-
          (trace___dumpstate_avx2 ++
          [(Assert,
           (((0 <= param_51) /\ (param_51 <= 18446744073709551615)) /\
           (((0 <= (param_52 + param_51)) /\
            ((param_52 + param_51) <= 18446744073709551615)) /\
           (((0 <=
             ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                            param_50 : 32))) /\
            (((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                            param_50 : 32)) <=
            18446744073709551615)) /\
           (((0 <=
             ((param_52 + param_51) +
             ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                            param_50 : 32)))) /\
            (((param_52 + param_51) +
             ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                            param_50 : 32))) <=
            18446744073709551615)) /\
           (((result_30 =
             (param_51 +
             ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                            param_50 : 32)))) /\
            (result_29 =
            (param_50 -
            ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                           param_50 : 32))))) /\
           (A.is_init b_result 0
           ((param_52 + param_51) +
           ((((param_50 < 32) ? param_50 : 32) < 0) ? 0 : ((param_50 < 32) ? 
                                                          param_50 : 32)))
           )))))))]);
          b_buf <- b_result;
          buf <- result_31;
          dELTA <- result_30;
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    trace___dumpstate_avx2 <-
    (trace___dumpstate_avx2 ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___dumpstate_avx2 <-
    (trace___dumpstate_avx2 ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    return (buf, b_buf, offset, trace___dumpstate_avx2);
  }
  proc __squeeze_avx2 (st:BArray224.t, b_st:BArray224.t, buf:A.t,
                       b_buf:A.t, _RATE8:int) : BArray224.t *
                                                        BArray224.t *
                                                        A.t *
                                                        A.t * trace = {
    var aux:BArray224.t;
    var aux_0:BArray224.t;
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    var param:BArray224.t;
    var result:BArray224.t;
    var param_0:BArray224.t;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result_0:int;
    var result_1:A.t;
    var param_4:BArray224.t;
    var result_2:BArray224.t;
    var param_5:BArray224.t;
    var param_6:int;
    var param_7:int;
    var param_8:A.t;
    var result_3:int;
    var result_4:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var b_result_0:BArray224.t;
    var b_result_1:A.t;
    var b_param_0:A.t;
    var b_result_2:BArray224.t;
    var trace___squeeze_avx2:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    param <- witness;
    param_0 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_8 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_4 <- witness;
    trace___squeeze_avx2 <- [];
    trace___squeeze_avx2 <-
    (trace___squeeze_avx2 ++
    [(Assert,
     (((0 < _RATE8) /\ (_RATE8 < 200)) /\ (BArray224.is_init b_st 0 224)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    i <- 0;
    trace___squeeze_avx2 <-
    (trace___squeeze_avx2 ++
    [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
    while ((i < iTERS)) {
      param <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2 (param,
      (BArray224.init_arr (W8.of_int 255)));
      result <- aux;
      b_result_2 <- aux_0;
      trace___squeeze_avx2 <- (trace___squeeze_avx2 ++ tmp__trace);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, (BArray224.is_init b_result_2 0 224))]);
      st <- result;
      b_param_0 <- b_buf;
      param_3 <- buf;
      param_2 <- offset;
      param_1 <- _RATE8;
      param_0 <- st;
      (result_1, b_result_1, result_0, tmp__trace) <@ __dumpstate_avx2 (
      param_3, b_param_0, param_2, param_1, param_0,
      (BArray224.init_arr (W8.of_int 255)));
      trace___squeeze_avx2 <- (trace___squeeze_avx2 ++ tmp__trace);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert,
       (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
       (((0 <= (param_2 + param_1)) /\
        ((param_2 + param_1) <= 18446744073709551615)) /\
       (result_0 = (param_2 + param_1)))))]);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert,
       (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
       (((0 <= (param_2 + param_1)) /\
        ((param_2 + param_1) <= 18446744073709551615)) /\
       (A.is_init b_result_1 0 (param_2 + param_1)))))]);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      b_buf <- b_result_1;
      buf <- result_1;
      offset <- result_0;
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
      i <- (i + 1);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
    }
    if ((0 < lO)) {
      param_4 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2 (param_4,
      (BArray224.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_0 <- aux_0;
      trace___squeeze_avx2 <- (trace___squeeze_avx2 ++ tmp__trace);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, (BArray224.is_init b_result_0 0 224))]);
      st <- result_2;
      b_param <- b_buf;
      param_8 <- buf;
      param_7 <- offset;
      param_6 <- lO;
      param_5 <- st;
      (result_4, b_result, result_3, tmp__trace) <@ __dumpstate_avx2 (
      param_8, b_param, param_7, param_6, param_5,
      (BArray224.init_arr (W8.of_int 255)));
      trace___squeeze_avx2 <- (trace___squeeze_avx2 ++ tmp__trace);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (result_3 = (param_7 + param_6)))))]);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (A.is_init b_result 0 (param_7 + param_6)))))]);
      trace___squeeze_avx2 <-
      (trace___squeeze_avx2 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      b_buf <- b_result;
      buf <- result_4;
    } else {
      
    }
    b_st <- (BArray224.init_arr (W8.of_int 255));
    return (st, b_st, buf, b_buf, trace___squeeze_avx2);
  }
}.

(* safety specifications *)

op __addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB =
   hoare [MM.__addstate_avx2 :
   (((__TRAILB = _TRAILB) /\
    ((__LEN = _LEN) /\
    ((_offset = offset) /\
    ((_b_buf = b_buf) /\
    ((_buf = buf) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st)))))))) /\
   ((true /\ (true /\ ((0 <= _offset) /\ (_offset <= 18446744073709551615)))) /\
   ((true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    ((((0 <= __TRAILB) /\ (__TRAILB < 256)) /\ (0 <= _aT)) /\
    (((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)) <= 200)))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
   (((0 <= (_offset + __LEN)) /\ ((_offset + __LEN) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((0 <= _offset) /\ (0 <= __LEN)) /\ ((_offset + __LEN) <= _ASIZE)) /\
    (A.is_init _b_buf _offset __LEN)) /\
   (BArray224.is_init _b_st 0 (7 * 32)))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)))) /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
    (((0 <= (_offset + __LEN)) /\
     ((_offset + __LEN) <= 18446744073709551615)) /\
    (((BArray224.is_init res.`2 0 (7 * 32)) /\
     (res.`3 = ((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)))) /\
    (res.`4 = (_offset + __LEN))))))))))))))))))) /\
   (valid res.`5))].

op __absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8 =
   hoare [MM.__absorb_avx2 :
   (((__RATE8 = _RATE8) /\
    ((__TRAILB = _TRAILB) /\
    ((_b_buf = b_buf) /\
    ((_buf = buf) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   ((((((((0 < __RATE8) /\ (__RATE8 < 200)) /\ (0 <= __TRAILB)) /\
       (__TRAILB < 256)) /\
      (0 <= _aT)) /\
     (_aT < __RATE8)) /\
    (A.is_init _b_buf 0 _ASIZE)) /\
   (BArray224.is_init _b_st 0 (7 * 32))))))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    ((BArray224.is_init res.`2 0 (7 * 32)) /\
    (res.`3 = (((_aT + _ASIZE) %% __RATE8) + ((__TRAILB <> 0) ? 1 : 0)))))))) /\
   (valid res.`4))].

op __dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st =
   hoare [MM.__dumpstate_avx2 :
   (((_b_st = b_st) /\
    ((_st = st) /\
    ((__LEN = _LEN) /\
    ((_offset = offset) /\ ((_b_buf = b_buf) /\ (_buf = buf)))))) /\
   ((true /\ (true /\ ((0 <= _offset) /\ (_offset <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
   (((0 <= (_offset + __LEN)) /\ ((_offset + __LEN) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   ((((((0 <= _offset) /\ (0 <= __LEN)) /\ ((_offset + __LEN) <= _ASIZE)) /\
     (BArray224.is_init _b_st 0 (7 * 32))) /\
    (__LEN <= 200)) /\
   (A.is_init _b_buf 0 _offset)))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)))) /\
    ((true /\
     (true /\
     (true /\
     (true /\
     (true /\
     (true /\
     (true /\
     (true /\
     (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
     (((0 <= (_offset + __LEN)) /\
      ((_offset + __LEN) <= 18446744073709551615)) /\
     (A.is_init res.`2 0 (_offset + __LEN)))))))))))) /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
    (((0 <= (_offset + __LEN)) /\
     ((_offset + __LEN) <= 18446744073709551615)) /\
    (res.`3 = (_offset + __LEN))))))))))))))) /\
   (valid res.`4))].

op __squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8 =
   hoare [MM.__squeeze_avx2 :
   (((__RATE8 = _RATE8) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   (true /\
   (true /\
   (((0 < __RATE8) /\ (__RATE8 < 200)) /\
   (BArray224.is_init _b_st 0 (7 * 32)))))) ==>
   (((A.is_init res.`4 0 _ASIZE) /\
    (BArray224.is_init res.`2 0 (7 * 32))) /\
   (valid res.`5))].

lemma __addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (__addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB).
proof.
rewrite /__addstate_avx2_spec; proc.
sp 28.
seq 1 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 8 <= _aT then _aT else if 8 <= (_aT + __LEN) then 8 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 8 <= _aT then __LEN else if 8 <= (_aT + __LEN) then (_aT + __LEN) - 8 else 0) /\ _TRAILB = (if 8 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 8 <= _aT then __LEN else if 8 <= (_aT + __LEN) then (_aT + __LEN) - 8 else 0))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_bcast_upto8_at_proof param_5 b_param_8 param_4 param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
seq 1 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 40 <= _aT then _aT else if 40 <= (_aT + __LEN) then 40 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 40 <= _aT then __LEN else if 40 <= (_aT + __LEN) then (_aT + __LEN) - 40 else 0) /\ _TRAILB = (if 40 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 40 <= _aT then __LEN else if 40 <= (_aT + __LEN) then (_aT + __LEN) - 40 else 0))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_upto32_at_proof param_12 b_param_7 param_11 param_10 param_9 param_8 param_7 param_6).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
if.
+ (* then *)
  seq 18 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 48 <= _aT then _aT else if 48 <= (_aT + __LEN) then 48 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 48 <= _aT then __LEN else if 48 <= (_aT + __LEN) then (_aT + __LEN) - 48 else 0) /\ _TRAILB = (if 48 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 48 <= _aT then __LEN else if 48 <= (_aT + __LEN) then (_aT + __LEN) - 48 else 0))).
  + (* cut *)
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_19 b_param_6 param_18 param_17 param_16 param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    seq 16 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 80 <= _aT then _aT else if 80 <= (_aT + __LEN) then 80 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 80 <= _aT then __LEN else if 80 <= (_aT + __LEN) then (_aT + __LEN) - 80 else 0) /\ _TRAILB = (if 80 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 80 <= _aT then __LEN else if 80 <= (_aT + __LEN) then (_aT + __LEN) - 80 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto32_at_proof param_26 b_param_5 param_25 param_24 param_23 param_22 param_21 param_20).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 17 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 88 <= _aT then _aT else if 88 <= (_aT + __LEN) then 88 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 88 <= _aT then __LEN else if 88 <= (_aT + __LEN) then (_aT + __LEN) - 88 else 0) /\ _TRAILB = (if 88 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 88 <= _aT then __LEN else if 88 <= (_aT + __LEN) then (_aT + __LEN) - 88 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto8_at_proof param_33 b_param_4 param_32 param_31 param_30 param_29 param_28 param_27).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 16 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 120 <= _aT then _aT else if 120 <= (_aT + __LEN) then 120 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 120 <= _aT then __LEN else if 120 <= (_aT + __LEN) then (_aT + __LEN) - 120 else 0) /\ _TRAILB = (if 120 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 120 <= _aT then __LEN else if 120 <= (_aT + __LEN) then (_aT + __LEN) - 120 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto32_at_proof param_40 b_param_3 param_39 param_38 param_37 param_36 param_35 param_34).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 17 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 128 <= _aT then _aT else if 128 <= (_aT + __LEN) then 128 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 128 <= _aT then __LEN else if 128 <= (_aT + __LEN) then (_aT + __LEN) - 128 else 0) /\ _TRAILB = (if 128 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 128 <= _aT then __LEN else if 128 <= (_aT + __LEN) then (_aT + __LEN) - 128 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto8_at_proof param_47 b_param_2 param_46 param_45 param_44 param_43 param_42 param_41).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 16 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 160 <= _aT then _aT else if 160 <= (_aT + __LEN) then 160 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 160 <= _aT then __LEN else if 160 <= (_aT + __LEN) then (_aT + __LEN) - 160 else 0) /\ _TRAILB = (if 160 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 160 <= _aT then __LEN else if 160 <= (_aT + __LEN) then (_aT + __LEN) - 160 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto32_at_proof param_54 b_param_1 param_53 param_52 param_51 param_50 param_49 param_48).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 17 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 168 <= _aT then _aT else if 168 <= (_aT + __LEN) then 168 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ _LEN = (if 168 <= _aT then __LEN else if 168 <= (_aT + __LEN) then (_aT + __LEN) - 168 else 0) /\ _TRAILB = (if 168 <= (_aT + __LEN) then __TRAILB else 0) /\ dELTA = __LEN - (if 168 <= _aT then __LEN else if 168 <= (_aT + __LEN) then (_aT + __LEN) - 168 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto8_at_proof param_61 b_param_0 param_60 param_59 param_58 param_57 param_56 param_55).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 14 : ((valid trace___addstate_avx2 /\ 0 <= _aT /\ 0 <= __LEN /\ 0 <= __TRAILB < 256 /\ _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ offset = _offset /\ aT = (if 200 <= _aT then _aT else if 200 <= (_aT + __LEN) then 200 else (_aT + __LEN) + (if __TRAILB <> 0 then 1 else 0)) /\ dELTA = __LEN - (if 200 <= _aT then __LEN else if 200 <= (_aT + __LEN) then (_aT + __LEN) - 200 else 0))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_read_upto32_at_proof param_68 b_param param_67 param_66 param_65 param_64 param_63 param_62).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    wp; ecall (__addstate_r3456_avx2_proof param_73 ((BArray224.init_arr (W8.of_int 255))) param_72 param_71 param_70 param_69).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
qed.

lemma __absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (__absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
rewrite /__absorb_avx2_spec; proc.
sp 25.
if.
+ (* then *)
  seq 28 : ((valid trace___absorb_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2_proof param_5 ((BArray224.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_avx2_proof param_4 ((BArray224.init_arr (W8.of_int 255))) param_3 param_2 ((A.init_arr (W8.of_int 255))) param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  seq 1 : ((valid trace___absorb_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2_proof param_12 ((BArray224.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_avx2_proof param_11 ((BArray224.init_arr (W8.of_int 255))) param_10 param_9 ((A.init_arr (W8.of_int 255))) param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  seq 17 : ((valid trace___absorb_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_avx2_proof param_18 ((BArray224.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2_proof param_20 ((BArray224.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  seq 16 : ((valid trace___absorb_avx2 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_avx2_proof param_18 ((BArray224.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2_proof param_20 ((BArray224.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
qed.

lemma __dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (__dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
rewrite /__dumpstate_avx2_spec; proc.
sp 48.
seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 8 then __LEN else 8) /\ dELTA = (if __LEN < 8 then __LEN else 8) /\ A.is_init b_buf 0 (_offset + dELTA))).
+ (* join *)
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_write_upto32_proof param_3 b_param_8 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    wp; ecall (RW.__a_ilen_write_upto32_proof param_8 b_param_9 param_7 param_6 param_5 param_4).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
seq 13 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 40 then __LEN else 40) /\ dELTA = (if __LEN < 40 then __LEN else 40) /\ A.is_init b_buf 0 (_offset + dELTA))).
+ (* cut *)
  wp; ecall (RW.__a_ilen_write_upto32_proof param_13 b_param_7 param_12 param_11 param_10 param_9).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
if.
+ (* then *)
  seq 17 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 48 then __LEN else 48) /\ dELTA = (if __LEN < 48 then __LEN else 48) /\ A.is_init b_buf 0 (_offset + dELTA))).
  + (* cut *)
    wp; ecall (RW.__a_ilen_write_upto8_proof param_18 b_param_6 param_17 param_16 param_15 param_14).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    seq 18 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 80 then __LEN else 80) /\ dELTA = (if __LEN < 80 then __LEN else 80) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* cut *)
      wp; ecall (RW.__a_ilen_write_upto32_proof param_23 b_param_5 param_22 param_21 param_20 param_19).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 88 then __LEN else 88) /\ dELTA = (if __LEN < 88 then __LEN else 88) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_28 b_param_4 param_27 param_26 param_25 param_24).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 120 then __LEN else 120) /\ dELTA = (if __LEN < 120 then __LEN else 120) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto32_proof param_33 b_param_3 param_32 param_31 param_30 param_29).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 128 then __LEN else 128) /\ dELTA = (if __LEN < 128 then __LEN else 128) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_38 b_param_2 param_37 param_36 param_35 param_34).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 160 then __LEN else 160) /\ dELTA = (if __LEN < 160 then __LEN else 160) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto32_proof param_43 b_param_1 param_42 param_41 param_40 param_39).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    seq 1 : ((valid trace___dumpstate_avx2 /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ _LEN = __LEN - (if __LEN < 168 then __LEN else 168) /\ dELTA = (if __LEN < 168 then __LEN else 168) /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* join *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_48 b_param_0 param_47 param_46 param_45 param_44).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      wp; ecall (RW.__a_ilen_write_upto32_proof param_53 b_param param_52 param_51 param_50 param_49).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
qed.

lemma __squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (__squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
rewrite /__squeeze_avx2_spec; proc.
seq 25 : ((valid trace___squeeze_avx2 /\ _LEN = _ASIZE /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ offset = _RATE8 * i /\ A.is_init b_buf 0 offset) /\ !((i < iTERS))).
+ (* loop *)
  wp; while ((valid trace___squeeze_avx2 /\ _LEN = _ASIZE /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ offset = _RATE8 * i /\ A.is_init b_buf 0 offset)).
  + (* loop body *)
    wp; ecall (__dumpstate_avx2_proof param_3 b_param_0 param_2 param_1 param_0 ((BArray224.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2_proof param ((BArray224.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
if.
+ (* then *)
  wp; ecall (__dumpstate_avx2_proof param_8 b_param param_7 param_6 param_5 ((BArray224.init_arr (W8.of_int 255)))).
  wp; ecall (_keccakf1600_avx2_proof param_4 ((BArray224.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(divz_eq modzDr modz_ge0 ltz_pmod _ASIZE_ge0 _ASIZE_max).
qed.

end KeccakArrayAvx2Safety.
