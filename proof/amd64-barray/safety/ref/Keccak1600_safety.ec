(* -------------------------------------------------------------------- *)
(* Safety of the ref (1-way, u64[25] state) absorb/squeeze code:
   fixed-size memory/array absorb and squeeze, and the streaming
   (init/absorb/squeeze/finish "updstate") API.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600_safety.
require import SBArray208_200.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.

(* state init, rate bit, memory absorb/squeeze *)

lemma __state_init_proof _st _b_st : (__state_init_spec _st _b_st).
proof.
rewrite /__state_init_spec; proc.
inline M.__HAS_FEATURE.
sp 10.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  wp; while ((valid trace___state_init /\ 0 <= i <= 25 /\ BArray200.is_init b_st 0 (8 * i))).
  + (* loop body *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __addratebit_proof _st _b_st __RATE8 :
      (__addratebit_spec _st _b_st __RATE8).
proof.
rewrite /__addratebit_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __addstate_m_proof _st _b_st _aT _buf __LEN __TRAILB :
      (__addstate_m_spec _st _b_st _aT _buf __LEN __TRAILB).
proof.
rewrite /__addstate_m_spec; proc.
inline M.__HAS_FEATURE.
sp 12.
if.
+ (* then *)
  seq 19 : ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ buf = _buf + (__LEN - _LEN))).
  + (* cut *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_5 param_4 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    seq 3 : ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ buf = _buf + (__LEN - _LEN) + 32 * i) /\ !((i < inc))).
    + (* loop *)
      wp; while ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ buf = _buf + (__LEN - _LEN) + 32 * i)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      sp 9.
      if.
      + (* then *)
        sp 10.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      if.
      + (* then *)
        sp 10.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 4 : ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ aT <= at <= aT + (_LEN %/ 8) * 8 /\ (at - aT) %% 8 = 0 /\ buf = _buf + (__LEN - _LEN) + (at - aT)) /\ !((at < (aT + ((_LEN %/ 8) * 8))))).
    + (* loop *)
      wp; while ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ aT <= at <= aT + (_LEN %/ 8) * 8 /\ (at - aT) %% 8 = 0 /\ buf = _buf + (__LEN - _LEN) + (at - aT))).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  if.
  + (* then *)
    seq 3 : ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ buf = _buf + (__LEN - _LEN) + 32 * i) /\ !((i < inc))).
    + (* loop *)
      wp; while ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ buf = _buf + (__LEN - _LEN) + 32 * i)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      sp 9.
      if.
      + (* then *)
        sp 10.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      if.
      + (* then *)
        sp 10.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 4 : ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ aT <= at <= aT + (_LEN %/ 8) * 8 /\ (at - aT) %% 8 = 0 /\ buf = _buf + (__LEN - _LEN) + (at - aT)) /\ !((at < (aT + ((_LEN %/ 8) * 8))))).
    + (* loop *)
      wp; while ((valid trace___addstate_m /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ aT <= at <= aT + (_LEN %/ 8) * 8 /\ (at - aT) %% 8 = 0 /\ buf = _buf + (__LEN - _LEN) + (at - aT))).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __absorb_m_proof _st _b_st _aT _buf __LEN __TRAILB __RATE8 :
      (__absorb_m_spec _st _b_st _aT _buf __LEN __TRAILB __RATE8).
proof.
rewrite /__absorb_m_spec; proc.
sp 21.
if.
+ (* then *)
  seq 27 : ((valid trace___absorb_m /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_proof param_4 ((BArray200.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_m_proof param_3 ((BArray200.init_arr (W8.of_int 255))) param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace___absorb_m /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_m /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_proof param_10 ((BArray200.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_m_proof param_9 ((BArray200.init_arr (W8.of_int 255))) param_8 param_7 param_6 param_5).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 17 : ((valid trace___absorb_m /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0) /\ buf = _buf + __LEN)).
  + (* cut *)
    wp; ecall (__addstate_m_proof param_15 ((BArray200.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_proof param_17 ((BArray200.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 16 : ((valid trace___absorb_m /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0) /\ buf = _buf + __LEN)).
  + (* cut *)
    wp; ecall (__addstate_m_proof param_15 ((BArray200.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_proof param_17 ((BArray200.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __dumpstate_m_proof _buf __LEN _st _b_st :
      (__dumpstate_m_spec _buf __LEN _st _b_st).
proof.
rewrite /__dumpstate_m_spec; proc.
inline M.__HAS_FEATURE.
sp 12.
if.
+ (* then *)
  seq 3 : ((valid trace___dumpstate_m /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ inc = _LEN %/ 32 /\ 0 <= j <= inc /\ buf = _buf + 32 * j) /\ !((j < inc))).
  + (* loop *)
    wp; while ((valid trace___dumpstate_m /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ inc = _LEN %/ 32 /\ 0 <= j <= inc /\ buf = _buf + 32 * j)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    sp 7.
    if.
    + (* then *)
      sp 7.
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    if.
    + (* then *)
      sp 7.
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      if.
      + (* then *)
        wp; ecall (__m_ilen_write_upto8_proof param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 3 : ((valid trace___dumpstate_m /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= i <= _LEN %/ 8 /\ buf = _buf + 8 * i) /\ !((i < (_LEN %/ 8)))).
  + (* loop *)
    wp; while ((valid trace___dumpstate_m /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= i <= _LEN %/ 8 /\ buf = _buf + 8 * i)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_ilen_write_upto8_proof param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __squeeze_m_proof _st _b_st _buf __LEN __RATE8 :
      (__squeeze_m_spec _st _b_st _buf __LEN __RATE8).
proof.
rewrite /__squeeze_m_spec; proc.
seq 14 : ((valid trace___squeeze_m /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= i <= _LEN %/ _RATE8 /\ buf = _buf + _RATE8 * i) /\ !((i < (_LEN %/ _RATE8)))).
+ (* loop *)
  wp; while ((valid trace___squeeze_m /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= i <= _LEN %/ _RATE8 /\ buf = _buf + _RATE8 * i)).
  + (* loop body *)
    wp; ecall (__dumpstate_m_proof param_2 param_1 param_0 ((BArray200.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_proof param ((BArray200.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
if.
+ (* then *)
  wp; ecall (__dumpstate_m_proof param_6 param_5 param_4 ((BArray200.init_arr (W8.of_int 255)))).
  wp; ecall (_keccakf1600_proof param_3 ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

(* memory streaming API *)

lemma _init_updstate_proof _st _b_st _r64 _trailb :
      (_init_updstate_spec _st _b_st _r64 _trailb).
proof.
rewrite /_init_updstate_spec; proc.
wp; ecall (__state_init_proof param b_param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _finish_updstate_proof _st _b_st : (_finish_updstate_spec _st _b_st).
proof.
rewrite /_finish_updstate_spec; proc.
wp; ecall (_ststatus_data_proof param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma ststatus_updstate_proof _status _b_status _st _b_st :
      (ststatus_updstate_spec _status _b_status _st _b_st).
proof.
rewrite /ststatus_updstate_spec; proc.
wp; ecall (_ststatus_data_proof param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma init_updstate_proof _st _b_st _r64 _trailb :
      (init_updstate_spec _st _b_st _r64 _trailb).
proof.
rewrite /init_updstate_spec; proc.
wp; ecall (_init_updstate_proof param_1 b_param param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma finish_updstate_proof _st _b_st : (finish_updstate_spec _st _b_st).
proof.
rewrite /finish_updstate_spec; proc.
wp; ecall (_finish_updstate_proof param ((BArray208.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _add_m_updstate_proof _st _b_st _at _buf _upto :
      (_add_m_updstate_spec _st _b_st _at _buf _upto).
proof.
rewrite /_add_m_updstate_spec; proc.
inline M.__HAS_FEATURE.
sp 17.
if.
+ (* then *)
  seq 24 : ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at)).
  + (* cut *)
    wp; ecall (__m_rlen_read_upto8_proof param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    seq 3 : ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      sp 13.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 3 : ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  sp 1.
  if.
  + (* then *)
    seq 3 : ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      sp 13.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 3 : ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _absorb_m_updstate_proof _st _b_st _buf _len :
      (_absorb_m_updstate_spec _st _b_st _buf _len).
proof.
rewrite /_absorb_m_updstate_spec; proc.
seq 30 : ((valid trace__absorb_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* cut *)
  wp; ecall (_ststatus_data_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
wp; ecall (_add_m_updstate_proof param_8 b_param param_7 param_6 param_5).
wp; while ((valid trace__absorb_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* loop body *)
  wp; ecall (_keccakf1600_proof param_4 ((BArray200.init_arr (W8.of_int 255)))).
  wp; ecall (_add_m_updstate_proof param_3 b_param_0 param_2 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _dump_m_updstate_proof _buf _st _b_st _at _upto :
      (_dump_m_updstate_spec _buf _st _b_st _at _upto).
proof.
rewrite /_dump_m_updstate_spec; proc.
inline M.__HAS_FEATURE.
sp 17.
if.
+ (* then *)
  seq 23 : ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at)).
  + (* cut *)
    wp; ecall (__m_rlen_write_upto8_proof param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    seq 3 : ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      sp 11.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 3 : ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  sp 1.
  if.
  + (* then *)
    seq 3 : ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    sp 2.
    if.
    + (* then *)
      sp 11.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    seq 3 : ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_m_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ _at <= at <= upto /\ buf = _buf + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    if.
    + (* then *)
      wp; ecall (__m_rlen_write_upto8_proof param_6 param_5 param_4).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _squeeze_m_updstate_proof _st _b_st _buf _len :
      (_squeeze_m_updstate_spec _st _b_st _buf _len).
proof.
rewrite /_squeeze_m_updstate_spec; proc.
seq 29 : ((valid trace__squeeze_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ buf = _buf /\ len = _len /\ 0 <= _len <= 18446744073709551360 /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* cut *)
  wp; ecall (_ststatus_data_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
if.
+ (* then *)
  seq 12 : ((valid trace__squeeze_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* cut *)
    wp; ecall (_keccakf1600_proof param_0 b_param_2).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  wp; ecall (_dump_m_updstate_proof param_9 param_8 b_param param_7 param_6).
  wp; while ((valid trace__squeeze_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* loop body *)
    wp; ecall (_keccakf1600_proof param_5 b_param_0).
    wp; ecall (_dump_m_updstate_proof param_4 param_3 b_param_1 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  wp; ecall (_dump_m_updstate_proof param_9 param_8 b_param param_7 param_6).
  wp; while ((valid trace__squeeze_m_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* loop body *)
    wp; ecall (_keccakf1600_proof param_5 b_param_0).
    wp; ecall (_dump_m_updstate_proof param_4 param_3 b_param_1 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma absorb_m_updstate_proof _st _b_st _buf _len :
      (absorb_m_updstate_spec _st _b_st _buf _len).
proof.
rewrite /absorb_m_updstate_spec; proc.
wp; ecall (_absorb_m_updstate_proof param_1 ((BArray208.init_arr (W8.of_int 255))) param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma squeeze_m_updstate_proof _st _b_st _buf _len :
      (squeeze_m_updstate_spec _st _b_st _buf _len).
proof.
rewrite /squeeze_m_updstate_spec; proc.
wp; ecall (_squeeze_m_updstate_proof param_1 ((BArray208.init_arr (W8.of_int 255))) param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory KeccakArrayRefSafety.

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
   ../extracted/Keccak1600_fixedsizes_ref_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc __addstate (st:BArray200.t, b_st:BArray200.t, aT:int, buf:A.t,
                   b_buf:A.t, offset:int, _LEN:int, _TRAILB:int) : 
  BArray200.t * BArray200.t * int * int * trace = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var t256:W256.t;
    var i:int;
    var t128:W128.t;
    var at:int;
    var param:int;
    var param_0:int;
    var result:bool;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:int;
    var param_6:int;
    var param_7:A.t;
    var result_0:W64.t;
    var result_1:int;
    var result_2:int;
    var result_3:int;
    var result_4:int;
    var param_8:int;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:int;
    var param_13:int;
    var param_14:A.t;
    var result_5:W64.t;
    var result_6:int;
    var result_7:int;
    var result_8:int;
    var result_9:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var trace___addstate:trace;
    b_param <- witness;
    b_param_0 <- witness;
    param_7 <- witness;
    param_14 <- witness;
    trace___addstate <- [];
    trace___addstate <-
    (trace___addstate ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     (((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
      (A.is_init b_buf offset _LEN)) /\
     (BArray200.is_init b_st 0 200)))))]);
    trace___addstate <-
    (trace___addstate ++
    [(Assert,
     ((((0 <= _TRAILB) /\ (_TRAILB < 256)) /\ (0 <= aT)) /\
     (((aT + _LEN) + ((_TRAILB <> 0) ? 1 : 0)) <= 200)))]);
    trace___addstate <-
    (trace___addstate ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    param_0 <- 4;
    param <- 7;
    (result, tmp__trace) <@ M.__HAS_FEATURE (param_0, param);
    trace___addstate <- (trace___addstate ++ tmp__trace);
    hAS_AVX2 <- result;
    dELTA <- 0;
    if (((aT %% 8) <> 0)) {
      aT8 <- (8 * (aT %/ 8));
      b_param_0 <- b_buf;
      param_7 <- buf;
      param_6 <- offset;
      param_5 <- dELTA;
      param_4 <- _LEN;
      param_3 <- _TRAILB;
      param_2 <- aT8;
      param_1 <- aT;
      (result_4, result_3, result_2, result_1, result_0, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_7, b_param_0, param_6, param_5, param_4,
      param_3, param_2, param_1);
      trace___addstate <- (trace___addstate ++ tmp__trace);
      trace___addstate <-
      (trace___addstate ++
      [(Assert,
       (((param_2 <= param_1) /\ (param_1 < (param_2 + 8))) ? ((8 <=
                                                               ((param_1 -
                                                                param_2) +
                                                               param_4)) ? 
                                                              ((((result_4 =
                                                                 (param_5 +
                                                                 ((param_2 +
                                                                  8) -
                                                                 param_1))) /\
                                                                (result_3 =
                                                                (param_4 -
                                                                ((param_2 +
                                                                 8) -
                                                                param_1)))) /\
                                                               (result_2 =
                                                               param_3)) /\
                                                              (result_1 =
                                                              (param_2 + 8))) : 
                                                              ((((result_4 =
                                                                 (param_5 +
                                                                 param_4)) /\
                                                                (result_3 =
                                                                0)) /\
                                                               (result_2 = 0)) /\
                                                              (result_1 =
                                                              ((param_1 +
                                                               param_4) +
                                                              ((param_3 <> 0) ? 1 : 0))))) : 
       ((((result_4 = param_5) /\ (result_3 = param_4)) /\
        (result_2 = param_3)) /\
       (result_1 = param_1))))]);
      dELTA <- result_4;
      _LEN <- result_3;
      _TRAILB <- result_2;
      aT <- result_1;
      w <- result_0;
      trace___addstate <-
      (trace___addstate ++ [(Assert, ((0 <= aT8) /\ ((aT8 + 8) <= 200)))]);
      trace___addstate <-
      (trace___addstate ++ [(Assert, ((0 <= aT8) /\ ((aT8 + 8) <= 200)))]);
      st <- (BArray200.set64d st aT8 ((BArray200.get64d st aT8) `^` w));
    } else {
      
    }
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      i <- 0;
      while ((i < inc)) {
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 32) <= _ASIZE)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 32))]);
        t256 <- (A.get256d buf (offset + dELTA));
        dELTA <- (dELTA + 32);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + (32 * i))) /\ (((aT + (32 * i)) + 32) <= 200)))]);
        t256 <- (t256 `^` (BArray200.get256d st (aT + (32 * i))));
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + (32 * i))) /\ (((aT + (32 * i)) + 32) <= 200)))]);
        st <- (BArray200.set256d st (aT + (32 * i)) t256);
        i <- (i + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 16) <= _ASIZE)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 16))]);
        t128 <- (A.get128d buf (offset + dELTA));
        dELTA <- (dELTA + 16);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + ((_LEN %/ 32) * 32))) /\
         (((aT + ((_LEN %/ 32) * 32)) + 16) <= 200)))]);
        t128 <- (t128 `^` (BArray200.get128d st (aT + ((_LEN %/ 32) * 32))));
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + ((_LEN %/ 32) * 32))) /\
         (((aT + ((_LEN %/ 32) * 32)) + 16) <= 200)))]);
        st <- (BArray200.set128d st (aT + ((_LEN %/ 32) * 32)) t128);
      } else {
        
      }
      if ((8 <= (_LEN %% 16))) {
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 8))]);
        w <- (A.get64d buf (offset + dELTA));
        dELTA <- (dELTA + 8);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + ((_LEN %/ 16) * 16))) /\
         (((aT + ((_LEN %/ 16) * 16)) + 8) <= 200)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (aT + ((_LEN %/ 16) * 16))) /\
         (((aT + ((_LEN %/ 16) * 16)) + 8) <= 200)))]);
        st <-
        (BArray200.set64d st (aT + ((_LEN %/ 16) * 16))
        ((BArray200.get64d st (aT + ((_LEN %/ 16) * 16))) `^` w));
      } else {
        
      }
    } else {
      trace___addstate <-
      (trace___addstate ++
      [(Assert, ((0 <= (aT %/ 8)) /\ ((aT %/ 8) <= 18446744073709551615)))]);
      at <- (aT %/ 8);
      trace___addstate <-
      (trace___addstate ++
      [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
      trace___addstate <-
      (trace___addstate ++
      [(Assert,
       ((0 <= (offset + dELTA)) /\
       ((offset + dELTA) <= 18446744073709551615)))]);
      offset <- (offset + dELTA);
      dELTA <- 0;
      trace___addstate <-
      (trace___addstate ++
      [(Assert,
       ((0 <= ((aT %/ 8) + (_LEN %/ 8))) /\
       (((aT %/ 8) + (_LEN %/ 8)) <= 18446744073709551615)))]);
      while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
        trace___addstate <-
        (trace___addstate ++ [(Assert, (A.is_init b_buf offset 8))]);
        w <- (A.get64d buf offset);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= (offset + 8)) /\ ((offset + 8) <= 18446744073709551615)))]);
        offset <- (offset + 8);
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        st <- (BArray200.set64 st at ((BArray200.get64 st at) `^` w));
        trace___addstate <-
        (trace___addstate ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        at <- (at + 1);
        trace___addstate <-
        (trace___addstate ++
        [(Assert,
         ((0 <= ((aT %/ 8) + (_LEN %/ 8))) /\
         (((aT %/ 8) + (_LEN %/ 8)) <= 18446744073709551615)))]);
      }
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      aT8 <- aT;
      b_param <- b_buf;
      param_14 <- buf;
      param_13 <- offset;
      param_12 <- dELTA;
      param_11 <- _LEN;
      param_10 <- _TRAILB;
      param_9 <- aT;
      param_8 <- aT;
      (result_9, result_8, result_7, result_6, result_5, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_14, b_param, param_13, param_12,
      param_11, param_10, param_9, param_8);
      trace___addstate <- (trace___addstate ++ tmp__trace);
      trace___addstate <-
      (trace___addstate ++
      [(Assert,
       (((param_9 <= param_8) /\ (param_8 < (param_9 + 8))) ? ((8 <=
                                                               ((param_8 -
                                                                param_9) +
                                                               param_11)) ? 
                                                              ((((result_9 =
                                                                 (param_12 +
                                                                 ((param_9 +
                                                                  8) -
                                                                 param_8))) /\
                                                                (result_8 =
                                                                (param_11 -
                                                                ((param_9 +
                                                                 8) -
                                                                param_8)))) /\
                                                               (result_7 =
                                                               param_10)) /\
                                                              (result_6 =
                                                              (param_9 + 8))) : 
                                                              ((((result_9 =
                                                                 (param_12 +
                                                                 param_11)) /\
                                                                (result_8 =
                                                                0)) /\
                                                               (result_7 = 0)) /\
                                                              (result_6 =
                                                              ((param_8 +
                                                               param_11) +
                                                              ((param_10 <>
                                                               0) ? 1 : 0))))) : 
       ((((result_9 = param_12) /\ (result_8 = param_11)) /\
        (result_7 = param_10)) /\
       (result_6 = param_8))))]);
      dELTA <- result_9;
      aT <- result_6;
      w <- result_5;
      trace___addstate <-
      (trace___addstate ++ [(Assert, ((0 <= aT8) /\ ((aT8 + 8) <= 200)))]);
      trace___addstate <-
      (trace___addstate ++ [(Assert, ((0 <= aT8) /\ ((aT8 + 8) <= 200)))]);
      st <- (BArray200.set64d st aT8 ((BArray200.get64d st aT8) `^` w));
    } else {
      
    }
    trace___addstate <-
    (trace___addstate ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___addstate <-
    (trace___addstate ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    b_st <- (BArray200.init_arr (W8.of_int 255));
    return (st, b_st, aT, offset, trace___addstate);
  }
  proc __absorb (st:BArray200.t, b_st:BArray200.t, aT:int, buf:A.t,
                 b_buf:A.t, _TRAILB:int, _RATE8:int) : BArray200.t *
                                                               BArray200.t *
                                                               int * trace = {
    var aux:BArray200.t;
    var aux_0:BArray200.t;
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
    var param_4:BArray200.t;
    var result:int;
    var result_0:int;
    var result_1:BArray200.t;
    var param_5:BArray200.t;
    var result_2:BArray200.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:A.t;
    var param_10:int;
    var param_11:BArray200.t;
    var result_3:int;
    var result_4:int;
    var result_5:BArray200.t;
    var param_12:BArray200.t;
    var result_6:BArray200.t;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var param_16:A.t;
    var param_17:int;
    var param_18:BArray200.t;
    var result_7:int;
    var result_8:int;
    var result_9:BArray200.t;
    var param_19:int;
    var param_20:BArray200.t;
    var result_10:BArray200.t;
    var b_result:BArray200.t;
    var b_result_0:BArray200.t;
    var b_result_1:BArray200.t;
    var b_result_2:BArray200.t;
    var b_result_3:BArray200.t;
    var b_result_4:BArray200.t;
    var trace___absorb:trace;
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
    trace___absorb <- [];
    trace___absorb <-
    (trace___absorb ++
    [(Assert,
     ((((((((0 < _RATE8) /\ (_RATE8 < 200)) /\ (0 <= _TRAILB)) /\
         (_TRAILB < 256)) /\
        (0 <= aT)) /\
       (aT < _RATE8)) /\
      (A.is_init b_buf 0 _ASIZE)) /\
     (BArray200.is_init b_st 0 200)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      param_4 <- st;
      param_3 <- aT;
      param_2 <- buf;
      param_1 <- offset;
      param_0 <- (_RATE8 - aT);
      param <- 0;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate (param_4,
      (BArray200.init_arr (W8.of_int 255)), param_3, param_2,
      (A.init_arr (W8.of_int 255)), param_1, param_0, param);
      result_1 <- aux;
      b_result_4 <- aux_0;
      result_0 <- aux_1;
      result <- aux_2;
      trace___absorb <- (trace___absorb ++ tmp__trace);
      trace___absorb <-
      (trace___absorb ++
      [(Assert,
       (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
       (((0 <= (param_1 + param_0)) /\
        ((param_1 + param_0) <= 18446744073709551615)) /\
       (((BArray200.is_init b_result_4 0 200) /\
        (result_0 = ((param_3 + param_0) + ((param <> 0) ? 1 : 0)))) /\
       (result = (param_1 + param_0))))))]);
      trace___absorb <-
      (trace___absorb ++
      [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
      st <- result_1;
      offset <- result;
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      param_5 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_5,
      (BArray200.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_3 <- aux_0;
      trace___absorb <- (trace___absorb ++ tmp__trace);
      trace___absorb <-
      (trace___absorb ++ [(Assert, (BArray200.is_init b_result_3 0 200))]);
      st <- result_2;
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      trace___absorb <-
      (trace___absorb ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_11 <- st;
        param_10 <- 0;
        param_9 <- buf;
        param_8 <- offset;
        param_7 <- _RATE8;
        param_6 <- 0;
        (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate (param_11,
        (BArray200.init_arr (W8.of_int 255)), param_10, param_9,
        (A.init_arr (W8.of_int 255)), param_8, param_7, param_6);
        result_5 <- aux;
        b_result_2 <- aux_0;
        result_4 <- aux_1;
        result_3 <- aux_2;
        trace___absorb <- (trace___absorb ++ tmp__trace);
        trace___absorb <-
        (trace___absorb ++
        [(Assert,
         (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
         (((0 <= (param_8 + param_7)) /\
          ((param_8 + param_7) <= 18446744073709551615)) /\
         (((BArray200.is_init b_result_2 0 200) /\
          (result_4 = ((param_10 + param_7) + ((param_6 <> 0) ? 1 : 0)))) /\
         (result_3 = (param_8 + param_7))))))]);
        trace___absorb <-
        (trace___absorb ++
        [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
        st <- result_5;
        offset <- result_3;
        (* Erased call to spill *)
        param_12 <- st;
        (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_12,
        (BArray200.init_arr (W8.of_int 255)));
        result_6 <- aux;
        b_result_1 <- aux_0;
        trace___absorb <- (trace___absorb ++ tmp__trace);
        trace___absorb <-
        (trace___absorb ++ [(Assert, (BArray200.is_init b_result_1 0 200))]);
        st <- result_6;
        (* Erased call to unspill *)
        trace___absorb <-
        (trace___absorb ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb <-
        (trace___absorb ++
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
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate (param_18,
    (BArray200.init_arr (W8.of_int 255)), param_17, param_16,
    (A.init_arr (W8.of_int 255)), param_15, param_14, param_13);
    result_9 <- aux;
    b_result_0 <- aux_0;
    result_8 <- aux_1;
    result_7 <- aux_2;
    trace___absorb <- (trace___absorb ++ tmp__trace);
    trace___absorb <-
    (trace___absorb ++
    [(Assert,
     (((0 <= param_14) /\ (param_14 <= 18446744073709551615)) /\
     (((0 <= (param_15 + param_14)) /\
      ((param_15 + param_14) <= 18446744073709551615)) /\
     (((BArray200.is_init b_result_0 0 200) /\
      (result_8 = ((param_17 + param_14) + ((param_13 <> 0) ? 1 : 0)))) /\
     (result_7 = (param_15 + param_14))))))]);
    trace___absorb <-
    (trace___absorb ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    st <- result_9;
    aT <- result_8;
    if ((_TRAILB <> 0)) {
      param_20 <- st;
      param_19 <- _RATE8;
      (aux, aux_0, tmp__trace) <@ M.__addratebit (param_20,
      (BArray200.init_arr (W8.of_int 255)), param_19);
      result_10 <- aux;
      b_result <- aux_0;
      trace___absorb <- (trace___absorb ++ tmp__trace);
      trace___absorb <-
      (trace___absorb ++ [(Assert, (BArray200.is_init b_result 0 200))]);
      st <- result_10;
    } else {
      
    }
    b_st <- (BArray200.init_arr (W8.of_int 255));
    return (st, b_st, aT, trace___absorb);
  }
  proc __dumpstate (buf:A.t, b_buf:A.t, offset:int, _LEN:int,
                    st:BArray200.t, b_st:BArray200.t) : A.t *
                                                        A.t * int *
                                                        trace = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var t:W64.t;
    var j:int;
    var t256:W256.t;
    var t128:W128.t;
    var i:int;
    var param:int;
    var param_0:int;
    var result:bool;
    var param_1:W64.t;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:A.t;
    var result_0:int;
    var result_1:int;
    var result_2:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var trace___dumpstate:trace;
    b_param <- witness;
    b_result <- witness;
    param_5 <- witness;
    result_2 <- witness;
    trace___dumpstate <- [];
    trace___dumpstate <-
    (trace___dumpstate ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     ((((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
       (BArray200.is_init b_st 0 200)) /\
      (_LEN <= 200)) /\
     (A.is_init b_buf 0 offset)))))]);
    trace___dumpstate <-
    (trace___dumpstate ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    param_0 <- 4;
    param <- 7;
    (result, tmp__trace) <@ M.__HAS_FEATURE (param_0, param);
    trace___dumpstate <- (trace___dumpstate ++ tmp__trace);
    hAS_AVX2 <- result;
    dELTA <- 0;
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      j <- 0;
      while ((j < inc)) {
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= (32 * j)) /\ (((32 * j) + 32) <= 200)))]);
        t256 <- (BArray200.get256d st (32 * j));
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 32) <= _ASIZE)))]);
        b_buf <-
        (A.set256d b_buf (offset + dELTA)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        buf <- (A.set256d buf (offset + dELTA) t256);
        dELTA <- (dELTA + 32);
        j <- (j + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= ((_LEN %/ 32) * 32)) /\ ((((_LEN %/ 32) * 32) + 16) <= 200)))]);
        t128 <- (BArray200.get128d st ((_LEN %/ 32) * 32));
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 16) <= _ASIZE)))]);
        b_buf <-
        (A.set128d b_buf (offset + dELTA)
        (W128.of_int 340282366920938463463374607431768211455));
        buf <- (A.set128d buf (offset + dELTA) t128);
        dELTA <- (dELTA + 16);
      } else {
        
      }
      if ((8 <= (_LEN %% 16))) {
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= ((_LEN %/ 16) * 16)) /\ ((((_LEN %/ 16) * 16) + 8) <= 200)))]);
        t <- (BArray200.get64d st ((_LEN %/ 16) * 16));
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
        b_buf <-
        (A.set64d b_buf (offset + dELTA)
        (W64.of_int 18446744073709551615));
        buf <- (A.set64d buf (offset + dELTA) t);
        dELTA <- (dELTA + 8);
      } else {
        
      }
    } else {
      i <- 0;
      trace___dumpstate <-
      (trace___dumpstate ++
      [(Assert,
       ((0 <= (_LEN %/ 8)) /\ ((_LEN %/ 8) <= 18446744073709551615)))]);
      while ((i < (_LEN %/ 8))) {
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 200)))]);
        t <- (BArray200.get64 st i);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
        b_buf <-
        (A.set64d b_buf offset (W64.of_int 18446744073709551615));
        buf <- (A.set64d buf offset t);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (offset + 8)) /\ ((offset + 8) <= 18446744073709551615)))]);
        offset <- (offset + 8);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___dumpstate <-
        (trace___dumpstate ++
        [(Assert,
         ((0 <= (_LEN %/ 8)) /\ ((_LEN %/ 8) <= 18446744073709551615)))]);
      }
    }
    if ((0 < (_LEN %% 8))) {
      trace___dumpstate <-
      (trace___dumpstate ++
      [(Assert,
       ((0 <= ((_LEN %/ 8) * 8)) /\ ((((_LEN %/ 8) * 8) + 8) <= 200)))]);
      t <- (BArray200.get64 st (_LEN %/ 8));
      b_param <- b_buf;
      param_5 <- buf;
      param_4 <- offset;
      param_3 <- dELTA;
      param_2 <- (_LEN %% 8);
      param_1 <- t;
      (result_2, b_result, result_1, result_0, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_5, b_param, param_4, param_3, param_2, param_1);
      trace___dumpstate <- (trace___dumpstate ++ tmp__trace);
      trace___dumpstate <-
      (trace___dumpstate ++
      [(Assert,
       (((0 <= param_3) /\ (param_3 <= 18446744073709551615)) /\
       (((0 <= (param_4 + param_3)) /\
        ((param_4 + param_3) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) /\
        (((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_4 + param_3) +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)))) /\
        (((param_4 + param_3) +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) <=
        18446744073709551615)) /\
       (((result_1 =
         (param_3 +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)))) /\
        (result_0 =
        (param_2 -
        ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? param_2 : 8))))) /\
       (A.is_init b_result 0
       ((param_4 + param_3) +
       ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? param_2 : 8)))
       )))))))]);
      b_buf <- b_result;
      buf <- result_2;
      dELTA <- result_1;
    } else {
      
    }
    trace___dumpstate <-
    (trace___dumpstate ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___dumpstate <-
    (trace___dumpstate ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    return (buf, b_buf, offset, trace___dumpstate);
  }
  proc __squeeze (st:BArray200.t, b_st:BArray200.t, buf:A.t,
                  b_buf:A.t, _RATE8:int) : BArray200.t *
                                                   BArray200.t *
                                                   A.t *
                                                   A.t * trace = {
    var aux:BArray200.t;
    var aux_0:BArray200.t;
    var offset:int;
    var i:int;
    var param:BArray200.t;
    var result:BArray200.t;
    var param_0:BArray200.t;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result_0:int;
    var result_1:A.t;
    var param_4:BArray200.t;
    var result_2:BArray200.t;
    var param_5:BArray200.t;
    var param_6:int;
    var param_7:int;
    var param_8:A.t;
    var result_3:int;
    var result_4:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var b_result_0:BArray200.t;
    var b_result_1:A.t;
    var b_param_0:A.t;
    var b_result_2:BArray200.t;
    var trace___squeeze:trace;
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
    trace___squeeze <- [];
    trace___squeeze <-
    (trace___squeeze ++
    [(Assert,
     (((0 < _RATE8) /\ (_RATE8 < 200)) /\ (BArray200.is_init b_st 0 200)))]);
    offset <- 0;
    i <- 0;
    trace___squeeze <-
    (trace___squeeze ++
    [(Assert,
     ((0 <= (_ASIZE %/ _RATE8)) /\ ((_ASIZE %/ _RATE8) <= 18446744073709551615)))]);
    while ((i < (_ASIZE %/ _RATE8))) {
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
      i <- (i + 1);
      (* Erased call to spill *)
      param <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param,
      (BArray200.init_arr (W8.of_int 255)));
      result <- aux;
      b_result_2 <- aux_0;
      trace___squeeze <- (trace___squeeze ++ tmp__trace);
      trace___squeeze <-
      (trace___squeeze ++ [(Assert, (BArray200.is_init b_result_2 0 200))]);
      st <- result;
      (* Erased call to unspill *)
      b_param_0 <- b_buf;
      param_3 <- buf;
      param_2 <- offset;
      param_1 <- _RATE8;
      param_0 <- st;
      (result_1, b_result_1, result_0, tmp__trace) <@ __dumpstate (param_3,
      b_param_0, param_2, param_1, param_0,
      (BArray200.init_arr (W8.of_int 255)));
      trace___squeeze <- (trace___squeeze ++ tmp__trace);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert,
       (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
       (((0 <= (param_2 + param_1)) /\
        ((param_2 + param_1) <= 18446744073709551615)) /\
       (result_0 = (param_2 + param_1)))))]);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert,
       (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
       (((0 <= (param_2 + param_1)) /\
        ((param_2 + param_1) <= 18446744073709551615)) /\
       (A.is_init b_result_1 0 (param_2 + param_1)))))]);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      b_buf <- b_result_1;
      buf <- result_1;
      offset <- result_0;
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert,
       ((0 <= (_ASIZE %/ _RATE8)) /\ ((_ASIZE %/ _RATE8) <= 18446744073709551615)))]);
    }
    if ((0 < (_ASIZE %% _RATE8))) {
      (* Erased call to spill *)
      param_4 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_4,
      (BArray200.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_0 <- aux_0;
      trace___squeeze <- (trace___squeeze ++ tmp__trace);
      trace___squeeze <-
      (trace___squeeze ++ [(Assert, (BArray200.is_init b_result_0 0 200))]);
      st <- result_2;
      (* Erased call to unspill *)
      b_param <- b_buf;
      param_8 <- buf;
      param_7 <- offset;
      param_6 <- (_ASIZE %% _RATE8);
      param_5 <- st;
      (result_4, b_result, result_3, tmp__trace) <@ __dumpstate (param_8,
      b_param, param_7, param_6, param_5,
      (BArray200.init_arr (W8.of_int 255)));
      trace___squeeze <- (trace___squeeze ++ tmp__trace);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (result_3 = (param_7 + param_6)))))]);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (A.is_init b_result 0 (param_7 + param_6)))))]);
      trace___squeeze <-
      (trace___squeeze ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      b_buf <- b_result;
      buf <- result_4;
    } else {
      
    }
    b_st <- (BArray200.init_arr (W8.of_int 255));
    return (st, b_st, buf, b_buf, trace___squeeze);
  }
}.

(* safety specifications *)

op __addstate_spec _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB =
   hoare [MM.__addstate :
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
   (BArray200.is_init _b_st 0 200))))))))))))))))))))) ==>
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
    (((BArray200.is_init res.`2 0 200) /\
     (res.`3 = ((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)))) /\
    (res.`4 = (_offset + __LEN))))))))))))))))))) /\
   (valid res.`5))].

op __absorb_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8 =
   hoare [MM.__absorb :
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
   (BArray200.is_init _b_st 0 200)))))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    ((BArray200.is_init res.`2 0 200) /\
    (res.`3 = (((_aT + _ASIZE) %% __RATE8) + ((__TRAILB <> 0) ? 1 : 0)))))))) /\
   (valid res.`4))].

op __dumpstate_spec _buf _b_buf _offset __LEN _st _b_st =
   hoare [MM.__dumpstate :
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
     (BArray200.is_init _b_st 0 200)) /\
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

op __squeeze_spec _st _b_st _buf _b_buf __RATE8 =
   hoare [MM.__squeeze :
   (((__RATE8 = _RATE8) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   (true /\
   (true /\
   (((0 < __RATE8) /\ (__RATE8 < 200)) /\ (BArray200.is_init _b_st 0 200))))) ==>
   (((A.is_init res.`4 0 _ASIZE) /\ (BArray200.is_init res.`2 0 200)) /\
   (valid res.`5))].

lemma __addstate_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (__addstate_spec _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB).
proof.
rewrite /__addstate_spec; proc.
inline M.__HAS_FEATURE.
sp 18.
if.
+ (* then *)
  seq 20 : ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ offset = _offset /\ dELTA = __LEN - _LEN)).
  + (* cut *)
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_7 b_param_0 param_6 param_5 param_4 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    seq 3 : ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ dELTA = __LEN - _LEN + 32 * i) /\ !((i < inc))).
    + (* loop *)
      wp; while ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ dELTA = __LEN - _LEN + 32 * i)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      sp 10.
      if.
      + (* then *)
        sp 11.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      if.
      + (* then *)
        sp 11.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 8 : ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ dELTA = 0 /\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\ offset = _offset + (__LEN - _LEN) + 8 * (at - aT %/ 8)) /\ !((at < ((aT %/ 8) + (_LEN %/ 8))))).
    + (* loop *)
      wp; while ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ dELTA = 0 /\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\ offset = _offset + (__LEN - _LEN) + 8 * (at - aT %/ 8))).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  if.
  + (* then *)
    seq 3 : ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ dELTA = __LEN - _LEN + 32 * i) /\ !((i < inc))).
    + (* loop *)
      wp; while ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= i <= inc /\ dELTA = __LEN - _LEN + 32 * i)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      sp 10.
      if.
      + (* then *)
        sp 11.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      if.
      + (* then *)
        sp 11.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        sp 2.
        if.
        + (* then *)
          wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 8 : ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ dELTA = 0 /\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\ offset = _offset + (__LEN - _LEN) + 8 * (at - aT %/ 8)) /\ !((at < ((aT %/ 8) + (_LEN %/ 8))))).
    + (* loop *)
      wp; while ((valid trace___addstate /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ dELTA = 0 /\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\ offset = _offset + (__LEN - _LEN) + 8 * (at - aT %/ 8))).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      wp; ecall (RW.__a_ilen_read_upto8_at_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma __absorb_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (__absorb_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
rewrite /__absorb_spec; proc.
sp 25.
if.
+ (* then *)
  seq 28 : ((valid trace___absorb /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_proof param_5 ((BArray200.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_proof param_4 ((BArray200.init_arr (W8.of_int 255))) param_3 param_2 ((A.init_arr (W8.of_int 255))) param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  seq 1 : ((valid trace___absorb /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_proof param_12 ((BArray200.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_proof param_11 ((BArray200.init_arr (W8.of_int 255))) param_10 param_9 ((A.init_arr (W8.of_int 255))) param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  seq 17 : ((valid trace___absorb /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_proof param_18 ((BArray200.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    wp; ecall (__addratebit_proof param_20 ((BArray200.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  seq 16 : ((valid trace___absorb /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_proof param_18 ((BArray200.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    wp; ecall (__addratebit_proof param_20 ((BArray200.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma __dumpstate_proof _buf _b_buf _offset __LEN _st _b_st :
      (__dumpstate_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
rewrite /__dumpstate_spec; proc.
inline M.__HAS_FEATURE.
sp 17.
if.
+ (* then *)
  seq 3 : ((valid trace___dumpstate /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= j <= inc /\ dELTA = 32 * j /\ A.is_init b_buf 0 (_offset + dELTA)) /\ !((j < inc))).
  + (* loop *)
    wp; while ((valid trace___dumpstate /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ offset = _offset /\ inc = _LEN %/ 32 /\ 0 <= j <= inc /\ dELTA = 32 * j /\ A.is_init b_buf 0 (_offset + dELTA))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    sp 8.
    if.
    + (* then *)
      sp 8.
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_5 b_param param_4 param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_5 b_param param_4 param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    if.
    + (* then *)
      sp 8.
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_5 b_param param_4 param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      if.
      + (* then *)
        wp; ecall (RW.__a_ilen_write_upto8_proof param_5 b_param param_4 param_3 param_2 param_1).
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  seq 3 : ((valid trace___dumpstate /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ dELTA = 0 /\ 0 <= i <= _LEN %/ 8 /\ offset = _offset + 8 * i /\ A.is_init b_buf 0 offset) /\ !((i < (_LEN %/ 8)))).
  + (* loop *)
    wp; while ((valid trace___dumpstate /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ dELTA = 0 /\ 0 <= i <= _LEN %/ 8 /\ offset = _offset + 8 * i /\ A.is_init b_buf 0 offset)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_write_upto8_proof param_5 b_param param_4 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(chunks8 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma __squeeze_proof _st _b_st _buf _b_buf __RATE8 :
      (__squeeze_spec _st _b_st _buf _b_buf __RATE8).
proof.
rewrite /__squeeze_spec; proc.
seq 22 : ((valid trace___squeeze /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ 0 <= i <= _ASIZE %/ _RATE8 /\ offset = _RATE8 * i /\ A.is_init b_buf 0 offset) /\ !((i < (_ASIZE %/ _RATE8)))).
+ (* loop *)
  wp; while ((valid trace___squeeze /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ 0 <= i <= _ASIZE %/ _RATE8 /\ offset = _RATE8 * i /\ A.is_init b_buf 0 offset)).
  + (* loop body *)
    wp; ecall (__dumpstate_proof param_3 b_param_0 param_2 param_1 param_0 ((BArray200.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_proof param ((BArray200.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
if.
+ (* then *)
  wp; ecall (__dumpstate_proof param_8 b_param param_7 param_6 param_5 ((BArray200.init_arr (W8.of_int 255)))).
  wp; ecall (_keccakf1600_proof param_4 ((BArray200.init_arr (W8.of_int 255)))).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

end KeccakArrayRefSafety.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory KeccakUpdstateRefSafety.

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
   ../extracted/Keccak1600_updstate_ref_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc _add_updstate (st:BArray200.t, b_st:BArray200.t, at:int,
                      buf:A.t, b_buf:A.t, off:int, upto:int) : 
  BArray200.t * BArray200.t * int * int * trace = {
    var hAS_AVX2:bool;
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t256:W256.t;
    var t128:W128.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var param:int;
    var param_0:int;
    var result:bool;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result_0:W64.t;
    var result_1:int;
    var param_4:int;
    var param_5:int;
    var param_6:A.t;
    var result_2:W64.t;
    var result_3:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var trace__add_updstate:trace;
    b_param <- witness;
    b_param_0 <- witness;
    param_3 <- witness;
    param_6 <- witness;
    trace__add_updstate <- [];
    trace__add_updstate <-
    (trace__add_updstate ++
    [(Assert,
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (off + (upto - at))) /\
      ((off + (upto - at)) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((((((BArray200.is_init b_st 0 200) /\ (0 <= at)) /\ (at <= upto)) /\
        (upto <= 200)) /\
       (0 <= off)) /\
      ((off + (upto - at)) <= _ASIZE)) /\
     (A.is_init b_buf off (upto - at)))))))]);
    trace__add_updstate <-
    (trace__add_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    trace__add_updstate <-
    (trace__add_updstate ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace__add_updstate <-
    (trace__add_updstate ++
    [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
    param_0 <- 4;
    param <- 7;
    (result, tmp__trace) <@ M.__HAS_FEATURE (param_0, param);
    trace__add_updstate <- (trace__add_updstate ++ tmp__trace);
    hAS_AVX2 <- result;
    trace__add_updstate <-
    (trace__add_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert, ((0 <= (len - at)) /\ ((len - at) <= 18446744073709551615)))]);
      len <- (len - at);
      at <- (at `|>>` 3);
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (at `<<` 3)) /\ ((at `<<` 3) <= 18446744073709551615)))]);
      at <- (at `<<` 3);
      b_param_0 <- b_buf;
      param_3 <- buf;
      param_2 <- off;
      param_1 <- len;
      (result_1, result_0, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_3,
      b_param_0, param_2, param_1);
      trace__add_updstate <- (trace__add_updstate ++ tmp__trace);
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       (((0 <=
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) /\
        (((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_2 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)))) /\
        ((param_2 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) <=
        18446744073709551615)) /\
       (result_1 =
       (param_2 +
       ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? param_1 : 8)))))))]);
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert, ((0 <= result_1) /\ (result_1 <= 18446744073709551615)))]);
      off2 <- result_1;
      t64 <- result_0;
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (len + (W64.to_uint at8))) /\
       ((len + (W64.to_uint at8)) <= 18446744073709551615)))]);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      trace__add_updstate <-
      (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      trace__add_updstate <-
      (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      st <- (BArray200.set64d st at ((BArray200.get64d st at) `^` t64));
      if ((8 <= len)) {
        len <- 8;
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (len - (W64.to_uint at8))) /\
         ((len - (W64.to_uint at8)) <= 18446744073709551615)))]);
        len <- (len - (W64.to_uint at8));
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (off + len)) /\ ((off + len) <= 18446744073709551615)))]);
        off <- (off + len);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= (at + 8)) /\ ((at + 8) <= 18446744073709551615)))]);
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    if (hAS_AVX2) {
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (newat + 32)) /\ ((newat + 32) <= 18446744073709551615)))]);
      newat <- (newat + 32);
      while ((newat <= upto)) {
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 32) <= _ASIZE)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, (A.is_init b_buf off 32))]);
        t256 <- (A.get256d buf off);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (off + 32)) /\ ((off + 32) <= 18446744073709551615)))]);
        off <- (off + 32);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 200)))]);
        t256 <- (t256 `^` (BArray200.get256d st at));
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 200)))]);
        st <- (BArray200.set256d st at t256);
        at <- newat;
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (newat + 32)) /\ ((newat + 32) <= 18446744073709551615)))]);
        newat <- (newat + 32);
      }
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (newat - 16)) /\ ((newat - 16) <= 18446744073709551615)))]);
      newat <- (newat - 16);
      if ((newat <= upto)) {
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 16) <= _ASIZE)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, (A.is_init b_buf off 16))]);
        t128 <- (A.get128d buf off);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (off + 16)) /\ ((off + 16) <= 18446744073709551615)))]);
        off <- (off + 16);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 16) <= 200)))]);
        t128 <- (t128 `^` (BArray200.get128d st at));
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 16) <= 200)))]);
        st <- (BArray200.set128d st at t128);
        at <- newat;
      } else {
        
      }
      newat <- at;
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
      if ((newat <= upto)) {
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, (A.is_init b_buf off 8))]);
        t64 <- (A.get64d buf off);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        st <- (BArray200.set64d st at ((BArray200.get64d st at) `^` t64));
        at <- newat;
      } else {
        
      }
    } else {
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
      while ((newat <= upto)) {
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, (A.is_init b_buf off 8))]);
        t64 <- (A.get64d buf off);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        trace__add_updstate <-
        (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        st <- (BArray200.set64d st at ((BArray200.get64d st at) `^` t64));
        at <- newat;
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__add_updstate <-
        (trace__add_updstate ++
        [(Assert,
         ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
        newat <- (newat + 8);
      }
    }
    if ((at < upto)) {
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      b_param <- b_buf;
      param_6 <- buf;
      param_5 <- off;
      param_4 <- (W64.to_uint upto8);
      (result_3, result_2, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_6,
      b_param, param_5, param_4);
      trace__add_updstate <- (trace__add_updstate ++ tmp__trace);
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert,
       (((0 <=
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8))) /\
        (((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_5 +
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8)))) /\
        ((param_5 +
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8))) <=
        18446744073709551615)) /\
       (result_3 =
       (param_5 +
       ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? param_4 : 8)))))))]);
      trace__add_updstate <-
      (trace__add_updstate ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      off <- result_3;
      t64 <- result_2;
      trace__add_updstate <-
      (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      trace__add_updstate <-
      (trace__add_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      st <- (BArray200.set64d st at ((BArray200.get64d st at) `^` t64));
    } else {
      
    }
    at <- upto;
    b_st <- (BArray200.init_arr (W8.of_int 255));
    return (st, b_st, at, off, trace__add_updstate);
  }
  proc _absorb_updstate (st:BArray208.t, b_st:BArray208.t, buf:A.t,
                         b_buf:A.t, len:int) : BArray208.t *
                                                       BArray208.t * trace = {
    var aux:BArray200.t;
    var aux_0:BArray200.t;
    var aux_1:int;
    var aux_2:int;
    var ststatus:W64.t;
    var stk:BArray200.t;
    var r8:int;
    var at:int;
    var off:int;
    var param:W64.t;
    var result:int;
    var result_0:int;
    var result_1:W8.t;
    var param_0:int;
    var param_1:int;
    var param_2:A.t;
    var param_3:int;
    var param_4:BArray200.t;
    var result_2:int;
    var result_3:int;
    var result_4:BArray200.t;
    var param_5:BArray200.t;
    var result_5:BArray200.t;
    var param_6:int;
    var param_7:int;
    var param_8:A.t;
    var param_9:int;
    var param_10:BArray200.t;
    var result_6:int;
    var result_7:int;
    var result_8:BArray200.t;
    var b_stk:BArray200.t;
    var b_result:BArray200.t;
    var b_param:A.t;
    var b_param_0:BArray200.t;
    var b_result_0:BArray200.t;
    var b_result_1:BArray200.t;
    var b_param_1:A.t;
    var b_param_2:BArray200.t;
    var trace__absorb_updstate:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_stk <- witness;
    param_2 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_8 <- witness;
    param_10 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_8 <- witness;
    stk <- witness;
    trace__absorb_updstate <- [];
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert,
     (((((BArray208.is_init b_st 0 208) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
      (len <= 18446744073709551360)) /\
     (A.is_init b_buf 0 len)))]);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    ststatus <- (BArray208.get64 st 25);
    param <- ststatus;
    (result_1, result_0, result, tmp__trace) <@ M._ststatus_data (param);
    trace__absorb_updstate <- (trace__absorb_updstate ++ tmp__trace);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert,
     (((((0 < result_0) /\ (result_0 <= 200)) /\ ((result_0 %% 8) = 0)) /\
      (0 <= result)) /\
     (result < result_0)))]);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
    r8 <- result_0;
    at <- result;
    b_stk <- (SBArray208_200.get_sub64 b_st 0);
    stk <- (SBArray208_200.get_sub64 st 0);
    (* Erased call to spill *)
    off <- 0;
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= (len + at)) /\ ((len + at) <= 18446744073709551615)))]);
    len <- (len + at);
    while ((r8 <= len)) {
      b_param_2 <- b_stk;
      param_4 <- stk;
      param_3 <- at;
      b_param_1 <- b_buf;
      param_2 <- buf;
      param_1 <- off;
      param_0 <- r8;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_updstate (param_4,
      b_param_2, param_3, param_2, b_param_1, param_1, param_0);
      result_4 <- aux;
      b_result_1 <- aux_0;
      result_3 <- aux_1;
      result_2 <- aux_2;
      trace__absorb_updstate <- (trace__absorb_updstate ++ tmp__trace);
      trace__absorb_updstate <-
      (trace__absorb_updstate ++
      [(Assert,
       (((0 <= (param_0 - param_3)) /\
        ((param_0 - param_3) <= 18446744073709551615)) /\
       (((0 <= (param_1 + (param_0 - param_3))) /\
        ((param_1 + (param_0 - param_3)) <= 18446744073709551615)) /\
       (((BArray200.is_init b_result_1 0 200) /\ (result_3 = param_0)) /\
       (result_2 = (param_1 + (param_0 - param_3)))))))]);
      trace__absorb_updstate <-
      (trace__absorb_updstate ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      trace__absorb_updstate <-
      (trace__absorb_updstate ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      stk <- result_4;
      at <- result_3;
      off <- result_2;
      (* Erased call to spill *)
      param_5 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_5,
      (BArray200.init_arr (W8.of_int 255)));
      result_5 <- aux;
      b_result_0 <- aux_0;
      trace__absorb_updstate <- (trace__absorb_updstate ++ tmp__trace);
      trace__absorb_updstate <-
      (trace__absorb_updstate ++
      [(Assert, (BArray200.is_init b_result_0 0 200))]);
      b_stk <- (BArray200.init_arr (W8.of_int 255));
      stk <- result_5;
      (* Erased call to unspill *)
      trace__absorb_updstate <-
      (trace__absorb_updstate ++
      [(Assert, ((0 <= (len - r8)) /\ ((len - r8) <= 18446744073709551615)))]);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
    b_param_0 <- b_stk;
    param_10 <- stk;
    param_9 <- at;
    b_param <- b_buf;
    param_8 <- buf;
    param_7 <- off;
    param_6 <- len;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_updstate (param_10,
    b_param_0, param_9, param_8, b_param, param_7, param_6);
    result_8 <- aux;
    b_result <- aux_0;
    result_7 <- aux_1;
    result_6 <- aux_2;
    trace__absorb_updstate <- (trace__absorb_updstate ++ tmp__trace);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert,
     (((0 <= (param_6 - param_9)) /\
      ((param_6 - param_9) <= 18446744073709551615)) /\
     (((0 <= (param_7 + (param_6 - param_9))) /\
      ((param_7 + (param_6 - param_9)) <= 18446744073709551615)) /\
     (((BArray200.is_init b_result 0 200) /\ (result_7 = param_6)) /\
     (result_6 = (param_7 + (param_6 - param_9)))))))]);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
    stk <- result_8;
    at <- result_7;
    b_st <-
    (SBArray208_200.set_sub64 b_st 0 (BArray200.init_arr (W8.of_int 255)));
    st <- (SBArray208_200.set_sub64 st 0 stk);
    trace__absorb_updstate <-
    (trace__absorb_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    b_st <- (BArray208.set8d b_st 200 (W8.of_int 255));
    st <- (BArray208.set8d st 200 (truncateu8 (W64.of_int at)));
    return (st, b_st, trace__absorb_updstate);
  }
  proc _dump_updstate (buf:A.t, b_buf:A.t, off:int,
                       st:BArray200.t, b_st:BArray200.t, at:int, upto:int) : 
  A.t * A.t * int * int * trace = {
    var hAS_AVX2:bool;
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t256:W256.t;
    var t128:W128.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var param:int;
    var param_0:int;
    var result:bool;
    var param_1:int;
    var param_2:W64.t;
    var param_3:int;
    var param_4:A.t;
    var result_0:int;
    var result_1:A.t;
    var param_5:int;
    var param_6:W64.t;
    var param_7:int;
    var param_8:A.t;
    var result_2:int;
    var result_3:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var b_result_0:A.t;
    var b_param_0:A.t;
    var trace__dump_updstate:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param_4 <- witness;
    param_8 <- witness;
    result_1 <- witness;
    result_3 <- witness;
    trace__dump_updstate <- [];
    trace__dump_updstate <-
    (trace__dump_updstate ++
    [(Assert,
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (off + (upto - at))) /\
      ((off + (upto - at)) <= 18446744073709551615)) /\
     (((((((BArray200.is_init b_st 0 200) /\ (0 <= at)) /\ (at <= upto)) /\
        (upto <= 200)) /\
       (0 <= off)) /\
      ((off + (upto - at)) <= _ASIZE)) /\
     (A.is_init b_buf 0 off)))))]);
    trace__dump_updstate <-
    (trace__dump_updstate ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace__dump_updstate <-
    (trace__dump_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    trace__dump_updstate <-
    (trace__dump_updstate ++
    [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
    param_0 <- 4;
    param <- 7;
    (result, tmp__trace) <@ M.__HAS_FEATURE (param_0, param);
    trace__dump_updstate <- (trace__dump_updstate ++ tmp__trace);
    hAS_AVX2 <- result;
    trace__dump_updstate <-
    (trace__dump_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert, ((0 <= (len - at)) /\ ((len - at) <= 18446744073709551615)))]);
      len <- (len - at);
      at <- (at `|>>` 3);
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (at `<<` 3)) /\ ((at `<<` 3) <= 18446744073709551615)))]);
      at <- (at `<<` 3);
      trace__dump_updstate <-
      (trace__dump_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      t64 <- (BArray200.get64d st at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      b_param_0 <- b_buf;
      param_4 <- buf;
      param_3 <- off;
      param_2 <- t64;
      param_1 <- len;
      (result_1, b_result_0, result_0, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_4, b_param_0, param_3, param_2, param_1);
      trace__dump_updstate <- (trace__dump_updstate ++ tmp__trace);
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       (((0 <=
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) /\
        (((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_3 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)))) /\
        ((param_3 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) /\
        (((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_3 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8)))) /\
        ((param_3 +
         ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? 
                                                    param_1 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_0 0
        (param_3 +
        ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? param_1 : 8)))
        ) /\
       (result_0 =
       (param_3 +
       ((((param_1 < 8) ? param_1 : 8) < 0) ? 0 : ((param_1 < 8) ? param_1 : 8))))))))))]);
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      b_buf <- b_result_0;
      buf <- result_1;
      off2 <- result_0;
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (len + (W64.to_uint at8))) /\
       ((len + (W64.to_uint at8)) <= 18446744073709551615)))]);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        len <- 8;
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (len - (W64.to_uint at8))) /\
         ((len - (W64.to_uint at8)) <= 18446744073709551615)))]);
        len <- (len - (W64.to_uint at8));
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (off + len)) /\ ((off + len) <= 18446744073709551615)))]);
        off <- (off + len);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= (at + 8)) /\ ((at + 8) <= 18446744073709551615)))]);
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    if (hAS_AVX2) {
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (newat + 32)) /\ ((newat + 32) <= 18446744073709551615)))]);
      newat <- (newat + 32);
      while ((newat <= upto)) {
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 200)))]);
        t256 <- (BArray200.get256d st at);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 32) <= _ASIZE)))]);
        b_buf <-
        (A.set256d b_buf off
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        buf <- (A.set256d buf off t256);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (off + 32)) /\ ((off + 32) <= 18446744073709551615)))]);
        off <- (off + 32);
        at <- newat;
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (newat + 32)) /\ ((newat + 32) <= 18446744073709551615)))]);
        newat <- (newat + 32);
      }
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (newat - 16)) /\ ((newat - 16) <= 18446744073709551615)))]);
      newat <- (newat - 16);
      if ((newat <= upto)) {
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 16) <= 200)))]);
        t128 <- (BArray200.get128d st at);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 16) <= _ASIZE)))]);
        b_buf <-
        (A.set128d b_buf off
        (W128.of_int 340282366920938463463374607431768211455));
        buf <- (A.set128d buf off t128);
        at <- newat;
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (off + 16)) /\ ((off + 16) <= 18446744073709551615)))]);
        off <- (off + 16);
      } else {
        
      }
      newat <- at;
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
      if ((newat <= upto)) {
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        t64 <- (BArray200.get64d st at);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
        b_buf <-
        (A.set64d b_buf off (W64.of_int 18446744073709551615));
        buf <- (A.set64d buf off t64);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        at <- newat;
      } else {
        
      }
    } else {
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
      while ((newat <= upto)) {
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
        t64 <- (BArray200.get64d st at);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
        b_buf <-
        (A.set64d b_buf off (W64.of_int 18446744073709551615));
        buf <- (A.set64d buf off t64);
        at <- newat;
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__dump_updstate <-
        (trace__dump_updstate ++
        [(Assert,
         ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
        newat <- (newat + 8);
      }
    }
    if ((at < upto)) {
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      trace__dump_updstate <-
      (trace__dump_updstate ++ [(Assert, ((0 <= at) /\ ((at + 8) <= 200)))]);
      t64 <- (BArray200.get64d st at);
      b_param <- b_buf;
      param_8 <- buf;
      param_7 <- off;
      param_6 <- t64;
      param_5 <- (W64.to_uint upto8);
      (result_3, b_result, result_2, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_8, b_param, param_7, param_6, param_5);
      trace__dump_updstate <- (trace__dump_updstate ++ tmp__trace);
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert,
       (((0 <=
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) /\
        (((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_7 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)))) /\
        ((param_7 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) /\
        (((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_7 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)))) /\
        ((param_7 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result 0
        (param_7 +
        ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? param_5 : 8)))
        ) /\
       (result_2 =
       (param_7 +
       ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? param_5 : 8))))))))))]);
      trace__dump_updstate <-
      (trace__dump_updstate ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      b_buf <- b_result;
      buf <- result_3;
      off <- result_2;
    } else {
      
    }
    at <- upto;
    return (buf, b_buf, off, at, trace__dump_updstate);
  }
  proc _squeeze_updstate (st:BArray208.t, b_st:BArray208.t, buf:A.t,
                          b_buf:A.t, len:int) : BArray208.t *
                                                        BArray208.t *
                                                        A.t *
                                                        A.t * trace = {
    var aux:BArray200.t;
    var aux_0:BArray200.t;
    var ststatus:W64.t;
    var stk:BArray200.t;
    var r8:int;
    var at:int;
    var off:int;
    var param:W64.t;
    var result:int;
    var result_0:int;
    var result_1:W8.t;
    var param_0:BArray200.t;
    var result_2:BArray200.t;
    var param_1:int;
    var param_2:int;
    var param_3:BArray200.t;
    var param_4:int;
    var param_5:A.t;
    var result_3:int;
    var result_4:int;
    var result_5:A.t;
    var param_6:BArray200.t;
    var result_6:BArray200.t;
    var param_7:int;
    var param_8:int;
    var param_9:BArray200.t;
    var param_10:int;
    var param_11:A.t;
    var result_7:int;
    var result_8:int;
    var result_9:A.t;
    var b_stk:BArray200.t;
    var b_result:A.t;
    var b_param:BArray200.t;
    var b_param_0:A.t;
    var b_result_0:BArray200.t;
    var b_param_1:BArray200.t;
    var b_result_1:A.t;
    var b_param_2:BArray200.t;
    var b_param_3:A.t;
    var b_result_2:BArray200.t;
    var b_param_4:BArray200.t;
    var trace__squeeze_updstate:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_stk <- witness;
    param_0 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    result_2 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_9 <- witness;
    stk <- witness;
    trace__squeeze_updstate <- [];
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert,
     ((((BArray208.is_init b_st 0 208) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
     (len <= 18446744073709551360)))]);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    ststatus <- (BArray208.get64 st 25);
    param <- ststatus;
    (result_1, result_0, result, tmp__trace) <@ M._ststatus_data (param);
    trace__squeeze_updstate <- (trace__squeeze_updstate ++ tmp__trace);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert,
     (((((0 < result_0) /\ (result_0 <= 200)) /\ ((result_0 %% 8) = 0)) /\
      (0 <= result)) /\
     (result < result_0)))]);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
    r8 <- result_0;
    at <- result;
    b_stk <- (SBArray208_200.get_sub64 b_st 0);
    stk <- (SBArray208_200.get_sub64 st 0);
    (* Erased call to spill *)
    if ((at = 0)) {
      (* Erased call to spill *)
      b_param_4 <- b_stk;
      param_0 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_0, b_param_4);
      result_2 <- aux;
      b_result_2 <- aux_0;
      trace__squeeze_updstate <- (trace__squeeze_updstate ++ tmp__trace);
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert, (BArray200.is_init b_result_2 0 200))]);
      b_stk <- (BArray200.init_arr (W8.of_int 255));
      stk <- result_2;
      (* Erased call to unspill *)
      at <- 0;
    } else {
      
    }
    off <- 0;
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= (len + at)) /\ ((len + at) <= 18446744073709551615)))]);
    len <- (len + at);
    while ((r8 < len)) {
      b_param_3 <- b_buf;
      param_5 <- buf;
      param_4 <- off;
      b_param_2 <- b_stk;
      param_3 <- stk;
      param_2 <- at;
      param_1 <- r8;
      (result_5, b_result_1, result_4, result_3, tmp__trace) <@ _dump_updstate (
      param_5, b_param_3, param_4, param_3, b_param_2, param_2, param_1);
      trace__squeeze_updstate <- (trace__squeeze_updstate ++ tmp__trace);
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert,
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((A.is_init b_result_1 0 (param_4 + (param_1 - param_2))) /\
        (result_4 = (param_4 + (param_1 - param_2)))) /\
       (result_3 = param_1)))))))]);
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      b_buf <- b_result_1;
      buf <- result_5;
      off <- result_4;
      at <- result_3;
      (* Erased call to spill *)
      b_param_1 <- b_stk;
      param_6 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600 (param_6, b_param_1);
      result_6 <- aux;
      b_result_0 <- aux_0;
      trace__squeeze_updstate <- (trace__squeeze_updstate ++ tmp__trace);
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert, (BArray200.is_init b_result_0 0 200))]);
      b_stk <- (BArray200.init_arr (W8.of_int 255));
      stk <- result_6;
      (* Erased call to unspill *)
      trace__squeeze_updstate <-
      (trace__squeeze_updstate ++
      [(Assert, ((0 <= (len - r8)) /\ ((len - r8) <= 18446744073709551615)))]);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    b_param_0 <- b_buf;
    param_11 <- buf;
    param_10 <- off;
    b_param <- b_stk;
    param_9 <- stk;
    param_8 <- at;
    param_7 <- len;
    (result_9, b_result, result_8, result_7, tmp__trace) <@ _dump_updstate (
    param_11, b_param_0, param_10, param_9, b_param, param_8, param_7);
    trace__squeeze_updstate <- (trace__squeeze_updstate ++ tmp__trace);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert,
     (((0 <= (param_7 - param_8)) /\
      ((param_7 - param_8) <= 18446744073709551615)) /\
     (((0 <= (param_10 + (param_7 - param_8))) /\
      ((param_10 + (param_7 - param_8)) <= 18446744073709551615)) /\
     (((0 <= (param_7 - param_8)) /\
      ((param_7 - param_8) <= 18446744073709551615)) /\
     (((0 <= (param_10 + (param_7 - param_8))) /\
      ((param_10 + (param_7 - param_8)) <= 18446744073709551615)) /\
     (((A.is_init b_result 0 (param_10 + (param_7 - param_8))) /\
      (result_8 = (param_10 + (param_7 - param_8)))) /\
     (result_7 = param_7)))))))]);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    b_buf <- b_result;
    buf <- result_9;
    at <- result_7;
    (* Erased call to unspill *)
    b_st <- (SBArray208_200.set_sub64 b_st 0 b_stk);
    st <- (SBArray208_200.set_sub64 st 0 stk);
    trace__squeeze_updstate <-
    (trace__squeeze_updstate ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    b_st <- (BArray208.set8d b_st 200 (W8.of_int 255));
    st <- (BArray208.set8d st 200 (truncateu8 (W64.of_int at)));
    return (st, b_st, buf, b_buf, trace__squeeze_updstate);
  }
  proc absorb_updstate (st:BArray208.t, b_st:BArray208.t, buf:A.t,
                        b_buf:A.t, len:int) : BArray208.t *
                                                      BArray208.t * trace = {
    var aux:BArray208.t;
    var aux_0:BArray208.t;
    var param:int;
    var param_0:A.t;
    var param_1:BArray208.t;
    var result:BArray208.t;
    var b_result:BArray208.t;
    var b_param:A.t;
    var trace_absorb_updstate:trace;
    b_param <- witness;
    b_result <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_absorb_updstate <- [];
    trace_absorb_updstate <-
    (trace_absorb_updstate ++
    [(Assert,
     (((((BArray208.is_init b_st 0 208) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
      (len <= 18446744073709551360)) /\
     (A.is_init b_buf 0 len)))]);
    trace_absorb_updstate <-
    (trace_absorb_updstate ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    st <- st;
    b_buf <- b_buf;
    buf <- buf;
    len <- len;
    param_1 <- st;
    b_param <- b_buf;
    param_0 <- buf;
    param <- len;
    (aux, aux_0, tmp__trace) <@ _absorb_updstate (param_1,
    (BArray208.init_arr (W8.of_int 255)), param_0, b_param, param);
    result <- aux;
    b_result <- aux_0;
    trace_absorb_updstate <- (trace_absorb_updstate ++ tmp__trace);
    trace_absorb_updstate <-
    (trace_absorb_updstate ++ [(Assert, (BArray208.is_init b_result 0 208))]);
    st <- result;
    b_st <- (BArray208.init_arr (W8.of_int 255));
    return (st, b_st, trace_absorb_updstate);
  }
  proc squeeze_updstate (st:BArray208.t, b_st:BArray208.t, buf:A.t,
                         b_buf:A.t, len:int) : BArray208.t *
                                                       BArray208.t *
                                                       A.t *
                                                       A.t * trace = {
    var aux:BArray208.t;
    var aux_0:BArray208.t;
    var aux_1:A.t;
    var aux_2:A.t;
    var param:int;
    var param_0:A.t;
    var param_1:BArray208.t;
    var result:A.t;
    var result_0:BArray208.t;
    var b_result:A.t;
    var b_result_0:BArray208.t;
    var b_param:A.t;
    var trace_squeeze_updstate:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_squeeze_updstate <- [];
    trace_squeeze_updstate <-
    (trace_squeeze_updstate ++
    [(Assert,
     ((((BArray208.is_init b_st 0 208) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
     (len <= 18446744073709551360)))]);
    trace_squeeze_updstate <-
    (trace_squeeze_updstate ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    st <- st;
    b_buf <- b_buf;
    buf <- buf;
    len <- len;
    param_1 <- st;
    b_param <- b_buf;
    param_0 <- buf;
    param <- len;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _squeeze_updstate (param_1,
    (BArray208.init_arr (W8.of_int 255)), param_0, b_param, param);
    result_0 <- aux;
    b_result_0 <- aux_0;
    result <- aux_1;
    b_result <- aux_2;
    trace_squeeze_updstate <- (trace_squeeze_updstate ++ tmp__trace);
    trace_squeeze_updstate <-
    (trace_squeeze_updstate ++
    [(Assert,
     ((BArray208.is_init b_result_0 0 208) /\
     (A.is_init b_result 0 param)))]);
    st <- result_0;
    b_buf <- b_result;
    buf <- result;
    b_st <- (BArray208.init_arr (W8.of_int 255));
    return (st, b_st, buf, b_buf, trace_squeeze_updstate);
  }
}.

(* safety specifications *)

op _add_updstate_spec _st _b_st _at _buf _b_buf _off _upto =
   hoare [MM._add_updstate :
   (((_upto = upto) /\
    ((_off = off) /\
    ((_b_buf = b_buf) /\
    ((_buf = buf) /\ ((_at = at) /\ ((_b_st = b_st) /\ (_st = st))))))) /\
   ((true /\ (true /\ ((0 <= _upto) /\ (_upto <= 18446744073709551615)))) /\
   ((true /\ (true /\ ((0 <= _off) /\ (_off <= 18446744073709551615)))) /\
   ((true /\ (true /\ ((0 <= _at) /\ (_at <= 18446744073709551615)))) /\
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
   (((0 <= 200) /\ (200 <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   (((0 <= (_off + (_upto - _at))) /\
    ((_off + (_upto - _at)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   (((((((BArray200.is_init _b_st 0 200) /\ (0 <= _at)) /\ (_at <= _upto)) /\
      (_upto <= 200)) /\
     (0 <= _off)) /\
    ((_off + (_upto - _at)) <= _ASIZE)) /\
   (A.is_init _b_buf _off (_upto - _at))))))))))))))))))))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)))) /\
    ((true /\ (true /\ ((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)))) /\
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
    (true /\
    (true /\
    (true /\
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    (((BArray200.is_init res.`2 0 200) /\ (res.`3 = _upto)) /\
    (res.`4 = (_off + (_upto - _at)))))))))))))))))))))))) /\
   (valid res.`5))].

op _absorb_updstate_spec _st _b_st _buf _b_buf _len =
   hoare [MM._absorb_updstate :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((0 <= 18446744073709551360) /\
    (18446744073709551360 <= 18446744073709551615)) /\
   (((((BArray208.is_init _b_st 0 208) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
    (_len <= 18446744073709551360)) /\
   (A.is_init _b_buf 0 _len))))))))))) ==>
   ((BArray208.is_init res.`2 0 208) /\ (valid res.`3))].

op _dump_updstate_spec _buf _b_buf _off _st _b_st _at _upto =
   hoare [MM._dump_updstate :
   (((_upto = upto) /\
    ((_at = at) /\
    ((_b_st = b_st) /\
    ((_st = st) /\ ((_off = off) /\ ((_b_buf = b_buf) /\ (_buf = buf))))))) /\
   ((true /\ (true /\ ((0 <= _upto) /\ (_upto <= 18446744073709551615)))) /\
   ((true /\ (true /\ ((0 <= _at) /\ (_at <= 18446744073709551615)))) /\
   ((true /\ (true /\ ((0 <= _off) /\ (_off <= 18446744073709551615)))) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= 200) /\ (200 <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   (((0 <= (_off + (_upto - _at))) /\
    ((_off + (_upto - _at)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((BArray200.is_init _b_st 0 200) /\ (0 <= _at)) /\ (_at <= _upto)) /\
      (_upto <= 200)) /\
     (0 <= _off)) /\
    ((_off + (_upto - _at)) <= _ASIZE)) /\
   (A.is_init _b_buf 0 _off))))))))))))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)))) /\
    ((true /\ (true /\ ((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)))) /\
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
    (true /\
    (true /\
    (true /\
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    (((A.is_init res.`2 0 (_off + (_upto - _at))) /\
     (res.`3 = (_off + (_upto - _at)))) /\
    (res.`4 = _upto))))))))))))))))))))))))))))))))))))) /\
   (valid res.`5))].

op _squeeze_updstate_spec _st _b_st _buf _b_buf _len =
   hoare [MM._squeeze_updstate :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((0 <= 18446744073709551360) /\
    (18446744073709551360 <= 18446744073709551615)) /\
   ((((BArray208.is_init _b_st 0 208) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
   (_len <= 18446744073709551360)))))))))) ==>
   ((true /\
    ((BArray208.is_init res.`2 0 208) /\ (A.is_init res.`4 0 _len))) /\
   (valid res.`5))].

op absorb_updstate_spec _st _b_st _buf _b_buf _len =
   hoare [MM.absorb_updstate :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((0 <= 18446744073709551360) /\
    (18446744073709551360 <= 18446744073709551615)) /\
   (((((BArray208.is_init _b_st 0 208) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
    (_len <= 18446744073709551360)) /\
   (A.is_init _b_buf 0 _len))))))))))) ==>
   ((BArray208.is_init res.`2 0 208) /\ (valid res.`3))].

op squeeze_updstate_spec _st _b_st _buf _b_buf _len =
   hoare [MM.squeeze_updstate :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((0 <= 18446744073709551360) /\
    (18446744073709551360 <= 18446744073709551615)) /\
   ((((BArray208.is_init _b_st 0 208) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
   (_len <= 18446744073709551360)))))))))) ==>
   ((true /\
    ((BArray208.is_init res.`2 0 208) /\ (A.is_init res.`4 0 _len))) /\
   (valid res.`5))].

lemma _add_updstate_proof _st _b_st _at _buf _b_buf _off _upto :
      (_add_updstate_spec _st _b_st _at _buf _b_buf _off _upto).
proof.
rewrite /_add_updstate_spec; proc.
inline M.__HAS_FEATURE.
sp 21.
if.
+ (* then *)
  seq 26 : ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at)).
  + (* cut *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_3 b_param_0 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    seq 3 : ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      sp 13.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 3 : ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  sp 1.
  if.
  + (* then *)
    seq 3 : ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      sp 13.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 3 : ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__add_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ A.is_init b_buf _off (_upto - _at) /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      wp; ecall (RW.__a_rlen_read_upto8_proof param_6 b_param param_5 param_4).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma _absorb_updstate_proof _st _b_st _buf _b_buf _len :
      (_absorb_updstate_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /_absorb_updstate_spec; proc.
seq 34 : ((valid trace__absorb_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* cut *)
  wp; ecall (_ststatus_data_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
wp; ecall (_add_updstate_proof param_10 b_param_0 param_9 param_8 b_param param_7 param_6).
wp; while ((valid trace__absorb_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 _len /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* loop body *)
  wp; ecall (_keccakf1600_proof param_5 ((BArray200.init_arr (W8.of_int 255)))).
  wp; ecall (_add_updstate_proof param_4 b_param_2 param_3 param_2 b_param_1 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma _dump_updstate_proof _buf _b_buf _off _st _b_st _at _upto :
      (_dump_updstate_spec _buf _b_buf _off _st _b_st _at _upto).
proof.
rewrite /_dump_updstate_spec; proc.
inline M.__HAS_FEATURE.
sp 25.
if.
+ (* then *)
  seq 27 : ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at)).
  + (* cut *)
    wp; ecall (RW.__a_rlen_write_upto8_proof param_4 b_param_0 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  if.
  + (* then *)
    seq 3 : ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      sp 11.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 3 : ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  sp 1.
  if.
  + (* then *)
    seq 3 : ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 32) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 32)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    sp 2.
    if.
    + (* then *)
      sp 11.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      sp 3.
      if.
      + (* then *)
        sp 8.
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  + (* else *)
    seq 3 : ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 8) /\ !((newat <= upto))).
    + (* loop *)
      wp; while ((valid trace__dump_updstate /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ A.is_init b_buf 0 off /\ newat = at + 8)).
      + (* loop body *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
      (* before the loop *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    if.
    + (* then *)
      wp; ecall (RW.__a_rlen_write_upto8_proof param_8 b_param param_7 param_6 param_5).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
    + (* else *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma _squeeze_updstate_proof _st _b_st _buf _b_buf _len :
      (_squeeze_updstate_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /_squeeze_updstate_spec; proc.
seq 36 : ((valid trace__squeeze_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ len = _len /\ 0 <= _len <= _ASIZE /\ _len <= 18446744073709551360 /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
+ (* cut *)
  wp; ecall (_ststatus_data_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
if.
+ (* then *)
  seq 13 : ((valid trace__squeeze_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 off /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* cut *)
    wp; ecall (_keccakf1600_proof param_0 b_param_4).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  wp; ecall (_dump_updstate_proof param_11 b_param_0 param_10 param_9 b_param param_8 param_7).
  wp; while ((valid trace__squeeze_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 off /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* loop body *)
    wp; ecall (_keccakf1600_proof param_6 b_param_1).
    wp; ecall (_dump_updstate_proof param_5 b_param_3 param_4 param_3 b_param_2 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
+ (* else *)
  wp; ecall (_dump_updstate_proof param_11 b_param_0 param_10 param_9 b_param param_8 param_7).
  wp; while ((valid trace__squeeze_updstate /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 off /\ BArray208.is_init b_st 0 208 /\ BArray200.is_init b_stk 0 200)).
  + (* loop body *)
    wp; ecall (_keccakf1600_proof param_6 b_param_1).
    wp; ecall (_dump_updstate_proof param_5 b_param_3 param_4 param_3 b_param_2 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set BArray200.get_of_list nth_map nth_iota size_map size_iota divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma absorb_updstate_proof _st _b_st _buf _b_buf _len :
      (absorb_updstate_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /absorb_updstate_spec; proc.
wp; ecall (_absorb_updstate_proof param_1 ((BArray208.init_arr (W8.of_int 255))) param_0 b_param param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

lemma squeeze_updstate_proof _st _b_st _buf _b_buf _len :
      (squeeze_updstate_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /squeeze_updstate_spec; proc.
wp; ecall (_squeeze_updstate_proof param_1 ((BArray208.init_arr (W8.of_int 255))) param_0 b_param param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_max).
qed.

end KeccakUpdstateRefSafety.
