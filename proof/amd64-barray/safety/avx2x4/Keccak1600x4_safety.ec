(* -------------------------------------------------------------------- *)
(* Safety of the 4-way (u256[25] state) absorb/squeeze code: fixed-size
   memory and array absorb (4 buffers or broadcast) and squeeze, and the
   streaming (init/absorb/squeeze/finish "updstate") API.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600x4_safety.
require import SBArray808_800.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.

(* memory absorb/squeeze *)

lemma __addstate_m_bcast_avx2x4_proof _st _b_st _aT _buf __LEN __TRAILB :
      (__addstate_m_bcast_avx2x4_spec _st _b_st _aT _buf __LEN __TRAILB).
proof.
rewrite /__addstate_m_bcast_avx2x4_spec; proc.
sp 5.
if.
+ (* then *)
  seq 23 : ((valid trace___addstate_m_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
  + (* cut *)
    wp; ecall (__m_ilen_read_bcast_upto8_at_proof param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace___addstate_m_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8)) /\ !((at < (32 * ((aT %/ 8) + (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_m_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  sp 2.
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_bcast_upto8_at_proof param_8 param_7 param_6 param_5 param_4).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 4 : ((valid trace___addstate_m_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8)) /\ !((at < (32 * ((aT %/ 8) + (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_m_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  sp 2.
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_bcast_upto8_at_proof param_8 param_7 param_6 param_5 param_4).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __absorb_m_bcast_avx2x4_proof _st _b_st _aT _buf __LEN __TRAILB __RATE8 :
      (__absorb_m_bcast_avx2x4_spec _st _b_st _aT _buf __LEN __TRAILB 
      __RATE8).
proof.
rewrite /__absorb_m_bcast_avx2x4_spec; proc.
sp 21.
if.
+ (* then *)
  seq 27 : ((valid trace___absorb_m_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_4 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_m_bcast_avx2x4_proof param_3 ((BArray800.init_arr (W8.of_int 255))) param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace___absorb_m_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_m_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2x4_proof param_10 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_m_bcast_avx2x4_proof param_9 ((BArray800.init_arr (W8.of_int 255))) param_8 param_7 param_6 param_5).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 16 : ((valid trace___absorb_m_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_bcast_avx2x4_proof param_15 ((BArray800.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_17 ((BArray800.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 15 : ((valid trace___absorb_m_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_bcast_avx2x4_proof param_15 ((BArray800.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_17 ((BArray800.init_arr (W8.of_int 255))) param_16).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __addstate_m_avx2x4_proof _st _b_st _aT _buf0 _buf1 _buf2 _buf3 __LEN __TRAILB :
      (__addstate_m_avx2x4_spec _st _b_st _aT _buf0 _buf1 _buf2 _buf3 
      __LEN __TRAILB).
proof.
rewrite /__addstate_m_avx2x4_spec; proc.
sp 8.
if.
+ (* then *)
  seq 67 : ((valid trace___addstate_m_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ buf0 = _buf0 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf1 = _buf1 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf2 = _buf2 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf3 = _buf3 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
  + (* cut *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_18 param_17 param_16 param_15 param_14).
    wp; ecall (__m_ilen_read_upto8_at_proof param_13 param_12 param_11 param_10 param_9).
    wp; ecall (__m_ilen_read_upto8_at_proof param_8 param_7 param_6 param_5 param_4).
    wp; ecall (__m_ilen_read_upto8_at_proof param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace___addstate_m_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ buf0 = _buf0 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf1 = _buf1 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf2 = _buf2 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf3 = _buf3 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))) /\ !((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_m_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ buf0 = _buf0 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf1 = _buf1 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf2 = _buf2 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf3 = _buf3 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  sp 2.
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_38 param_37 param_36 param_35 param_34).
    wp; ecall (__m_ilen_read_upto8_at_proof param_33 param_32 param_31 param_30 param_29).
    wp; ecall (__m_ilen_read_upto8_at_proof param_28 param_27 param_26 param_25 param_24).
    wp; ecall (__m_ilen_read_upto8_at_proof param_23 param_22 param_21 param_20 param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 4 : ((valid trace___addstate_m_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ buf0 = _buf0 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf1 = _buf1 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf2 = _buf2 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf3 = _buf3 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))) /\ !((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_m_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ buf0 = _buf0 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf1 = _buf1 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf2 = _buf2 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)) /\ buf3 = _buf3 + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  sp 2.
  if.
  + (* then *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_38 param_37 param_36 param_35 param_34).
    wp; ecall (__m_ilen_read_upto8_at_proof param_33 param_32 param_31 param_30 param_29).
    wp; ecall (__m_ilen_read_upto8_at_proof param_28 param_27 param_26 param_25 param_24).
    wp; ecall (__m_ilen_read_upto8_at_proof param_23 param_22 param_21 param_20 param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __absorb_m_avx2x4_proof _st _b_st _aT _buf0 _buf1 _buf2 _buf3 __LEN __TRAILB __RATE8 :
      (__absorb_m_avx2x4_spec _st _b_st _aT _buf0 _buf1 _buf2 _buf3 __LEN
      __TRAILB __RATE8).
proof.
rewrite /__absorb_m_avx2x4_spec; proc.
sp 24.
if.
+ (* then *)
  seq 39 : ((valid trace___absorb_m_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf0 = _buf0 + (__RATE8 - _aT) + _RATE8 * i /\ buf1 = _buf1 + (__RATE8 - _aT) + _RATE8 * i /\ buf2 = _buf2 + (__RATE8 - _aT) + _RATE8 * i /\ buf3 = _buf3 + (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_7 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_m_avx2x4_proof param_6 ((BArray800.init_arr (W8.of_int 255))) param_5 param_4 param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace___absorb_m_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf0 = _buf0 + (__RATE8 - _aT) + _RATE8 * i /\ buf1 = _buf1 + (__RATE8 - _aT) + _RATE8 * i /\ buf2 = _buf2 + (__RATE8 - _aT) + _RATE8 * i /\ buf3 = _buf3 + (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_m_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + __LEN /\ aT = 0 /\ _LEN = __LEN - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ buf0 = _buf0 + (__RATE8 - _aT) + _RATE8 * i /\ buf1 = _buf1 + (__RATE8 - _aT) + _RATE8 * i /\ buf2 = _buf2 + (__RATE8 - _aT) + _RATE8 * i /\ buf3 = _buf3 + (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2x4_proof param_16 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_m_avx2x4_proof param_15 ((BArray800.init_arr (W8.of_int 255))) param_14 param_13 param_12 param_11 param_10 param_9 param_8).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 25 : ((valid trace___absorb_m_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_avx2x4_proof param_24 ((BArray800.init_arr (W8.of_int 255))) param_23 param_22 param_21 param_20 param_19 param_18 param_17).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_26 ((BArray800.init_arr (W8.of_int 255))) param_25).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 24 : ((valid trace___absorb_m_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= __LEN /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ aT = (_aT + __LEN) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_m_avx2x4_proof param_24 ((BArray800.init_arr (W8.of_int 255))) param_23 param_22 param_21 param_20 param_19 param_18 param_17).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_26 ((BArray800.init_arr (W8.of_int 255))) param_25).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __dumpstate_m_avx2x4_proof _buf0 _buf1 _buf2 _buf3 __LEN _st _b_st :
      (__dumpstate_m_avx2x4_spec _buf0 _buf1 _buf2 _buf3 __LEN _st _b_st).
proof.
rewrite /__dumpstate_m_avx2x4_spec; proc.
seq 9 : ((valid trace___dumpstate_m_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 0 <= i <= 32 * (_LEN %/ 32) /\ i %% 32 = 0 /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i) /\ !((i < (32 * (_LEN %/ 32))))).
+ (* loop *)
  wp; while ((valid trace___dumpstate_m_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 0 <= i <= 32 * (_LEN %/ 32) /\ i %% 32 = 0 /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i)).
  + (* loop body *)
    wp; ecall (__4u64x4_u256x4_proof param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
seq 2 : ((valid trace___dumpstate_m_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\ i %% 8 = 0 /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i) /\ !((i < (8 * (_LEN %/ 8))))).
+ (* loop *)
  wp; while ((valid trace___dumpstate_m_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\ i %% 8 = 0 /\ buf0 = _buf0 + i /\ buf1 = _buf1 + i /\ buf2 = _buf2 + i /\ buf3 = _buf3 + i)).
  + (* loop body *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
if.
+ (* then *)
  wp; ecall (__m_ilen_write_upto8_proof param_14 param_13 param_12).
  wp; ecall (__m_ilen_write_upto8_proof param_11 param_10 param_9).
  wp; ecall (__m_ilen_write_upto8_proof param_8 param_7 param_6).
  wp; ecall (__m_ilen_write_upto8_proof param_5 param_4 param_3).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma __squeeze_m_avx2x4_proof _st _b_st _buf0 _buf1 _buf2 _buf3 __LEN __RATE8 :
      (__squeeze_m_avx2x4_spec _st _b_st _buf0 _buf1 _buf2 _buf3 __LEN
      __RATE8).
proof.
rewrite /__squeeze_m_avx2x4_spec; proc.
sp 16.
if.
+ (* then *)
  seq 3 : ((valid trace___squeeze_m_avx2x4 /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ buf0 = _buf0 + _RATE8 * i /\ buf1 = _buf1 + _RATE8 * i /\ buf2 = _buf2 + _RATE8 * i /\ buf3 = _buf3 + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___squeeze_m_avx2x4 /\ _LEN = __LEN /\ _RATE8 = __RATE8 /\ 0 <= __LEN /\ 0 < __RATE8 < 200 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 __LEN /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 __LEN /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 __LEN /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 __LEN /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ buf0 = _buf0 + _RATE8 * i /\ buf1 = _buf1 + _RATE8 * i /\ buf2 = _buf2 + _RATE8 * i /\ buf3 = _buf3 + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (__dumpstate_m_avx2x4_proof param_5 param_4 param_3 param_2 param_1 param_0 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (_keccakf1600_avx2x4_proof param ((BArray800.init_arr (W8.of_int 255)))).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__dumpstate_m_avx2x4_proof param_12 param_11 param_10 param_9 param_8 param_7 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2x4_proof param_6 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  if.
  + (* then *)
    wp; ecall (__dumpstate_m_avx2x4_proof param_12 param_11 param_10 param_9 param_8 param_7 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2x4_proof param_6 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

(* memory streaming API *)

lemma _init_updstate_avx2x4_proof _st _b_st _r64 _trailb :
      (_init_updstate_avx2x4_spec _st _b_st _r64 _trailb).
proof.
rewrite /_init_updstate_avx2x4_spec; proc.
wp; ecall (__state_init_avx2x4_proof param b_param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _ststatus_data_avx2x4_proof _ststatus :
      (_ststatus_data_avx2x4_spec _ststatus).
proof.
rewrite /_ststatus_data_avx2x4_spec; proc.
auto => &m /= _.
pose x := (ststatus{m} `>>` W8.of_int 8) `&` W64.of_int 255.
pose a := ststatus{m} `&` W64.of_int 255.
have hx : 0 <= to_uint x < 256 by apply to_uint_and255.
have ha : 0 <= to_uint a < 256 by apply to_uint_and255.
have hr: to_uint ((x + W64.one) `<<` W8.of_int 3) = (to_uint x + 1) * 8.
+ rewrite /(`<<`) /= to_uint_shl // to_uintD_small /=; 1: smt().
  by rewrite modz_small; smt().
rewrite !W64.ultE !W64.uleE hr /= -/x -/a /valid /=.
case: (200 < (to_uint x + 1) * 8) => h; rewrite /= ?hr.
+ by case: (200 <= to_uint a) => h' /=; smt(W64.to_uint_cmp).
by case: ((to_uint x + 1) * 8 <= to_uint a) => h' /=; smt(W64.to_uint_cmp).
qed.

lemma _finish_updstate_avx2x4_proof _st _b_st :
      (_finish_updstate_avx2x4_spec _st _b_st).
proof.
rewrite /_finish_updstate_avx2x4_spec; proc.
wp; ecall (_ststatus_data_avx2x4_proof param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma ststatus_updstate_avx2x4_proof _status _b_status _st _b_st :
      (ststatus_updstate_avx2x4_spec _status _b_status _st _b_st).
proof.
rewrite /ststatus_updstate_avx2x4_spec; proc.
wp; ecall (_ststatus_data_avx2x4_proof param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma init_updstate_avx2x4_proof _st _b_st _r64 _trailb :
      (init_updstate_avx2x4_spec _st _b_st _r64 _trailb).
proof.
rewrite /init_updstate_avx2x4_spec; proc.
wp; ecall (_init_updstate_avx2x4_proof param_1 b_param param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma finish_updstate_avx2x4_proof _st _b_st :
      (finish_updstate_avx2x4_spec _st _b_st).
proof.
rewrite /finish_updstate_avx2x4_spec; proc.
wp; ecall (_finish_updstate_avx2x4_proof param ((BArray808.init_arr (W8.of_int 255)))).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _add_m_bcast_updstate_avx2x4_proof _st _b_st _at _buf _upto :
      (_add_m_bcast_updstate_avx2x4_spec _st _b_st _at _buf _upto).
proof.
rewrite /_add_m_bcast_updstate_avx2x4_spec; proc.
sp 8.
if.
+ (* then *)
  seq 33 : ((valid trace__add_m_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ buf = _buf + (at - _at) /\ newat = at + 8)).
  + (* cut *)
    wp; ecall (__m_rlen_read_upto8_proof param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace__add_m_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ buf = _buf + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_m_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ buf = _buf + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_read_upto8_proof param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 4 : ((valid trace__add_m_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ buf = _buf + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_m_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\ buf = _buf + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_read_upto8_proof param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _absorb_m_bcast_updstate_avx2x4_proof _st _b_st _buf _len :
      (_absorb_m_bcast_updstate_avx2x4_spec _st _b_st _buf _len).
proof.
rewrite /_absorb_m_bcast_updstate_avx2x4_spec; proc.
seq 30 : ((valid trace__absorb_m_bcast_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
wp; ecall (_add_m_bcast_updstate_avx2x4_proof param_8 b_param param_7 param_6 param_5).
wp; while ((valid trace__absorb_m_bcast_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf <= buf /\ is_valid ptr_modulus Glob.mem_v _buf _len /\ buf + (len - at) = _buf + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* loop body *)
  wp; ecall (_keccakf1600_avx2x4_proof param_4 ((BArray800.init_arr (W8.of_int 255)))).
  wp; ecall (_add_m_bcast_updstate_avx2x4_proof param_3 b_param_0 param_2 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _add_m_updstate_avx2x4_proof _st _b_st _at _buf0 _buf1 _buf2 _buf3 _upto :
      (_add_m_updstate_avx2x4_spec _st _b_st _at _buf0 _buf1 _buf2 _buf3
      _upto).
proof.
rewrite /_add_m_updstate_avx2x4_spec; proc.
sp 11.
if.
+ (* then *)
  seq 88 : ((valid trace__add_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
  + (* cut *)
    wp; ecall (__m_rlen_read_upto8_proof param_6 param_5).
    wp; ecall (__m_rlen_read_upto8_proof param_4 param_3).
    wp; ecall (__m_rlen_read_upto8_proof param_2 param_1).
    wp; ecall (__m_rlen_read_upto8_proof param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace__add_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_read_upto8_proof param_14 param_13).
    wp; ecall (__m_rlen_read_upto8_proof param_12 param_11).
    wp; ecall (__m_rlen_read_upto8_proof param_10 param_9).
    wp; ecall (__m_rlen_read_upto8_proof param_8 param_7).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 4 : ((valid trace__add_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_read_upto8_proof param_14 param_13).
    wp; ecall (__m_rlen_read_upto8_proof param_12 param_11).
    wp; ecall (__m_rlen_read_upto8_proof param_10 param_9).
    wp; ecall (__m_rlen_read_upto8_proof param_8 param_7).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _absorb_m_updstate_avx2x4_proof _st _b_st _buf0 _buf1 _buf2 _buf3 _len :
      (_absorb_m_updstate_avx2x4_spec _st _b_st _buf0 _buf1 _buf2 _buf3 _len).
proof.
rewrite /_absorb_m_updstate_avx2x4_spec; proc.
seq 33 : ((valid trace__absorb_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf0 <= buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf0 + (len - at) = _buf0 + _len /\ 0 <= _buf1 <= buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf1 + (len - at) = _buf1 + _len /\ 0 <= _buf2 <= buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf2 + (len - at) = _buf2 + _len /\ 0 <= _buf3 <= buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ buf3 + (len - at) = _buf3 + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
wp; ecall (_add_m_updstate_avx2x4_proof param_14 b_param param_13 param_12 param_11 param_10 param_9 param_8).
wp; while ((valid trace__absorb_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf0 <= buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf0 + (len - at) = _buf0 + _len /\ 0 <= _buf1 <= buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf1 + (len - at) = _buf1 + _len /\ 0 <= _buf2 <= buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf2 + (len - at) = _buf2 + _len /\ 0 <= _buf3 <= buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ buf3 + (len - at) = _buf3 + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* loop body *)
  wp; ecall (_keccakf1600_avx2x4_proof param_7 ((BArray800.init_arr (W8.of_int 255)))).
  wp; ecall (_add_m_updstate_avx2x4_proof param_6 b_param_0 param_5 param_4 param_3 param_2 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _dump_m_updstate_avx2x4_proof _buf0 _buf1 _buf2 _buf3 _st _b_st _at _upto :
      (_dump_m_updstate_avx2x4_spec _buf0 _buf1 _buf2 _buf3 _st _b_st 
      _at _upto).
proof.
rewrite /_dump_m_updstate_avx2x4_spec; proc.
sp 11.
if.
+ (* then *)
  seq 72 : ((valid trace__dump_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
  + (* cut *)
    wp; ecall (__m_rlen_write_upto8_proof param_10 param_9 param_8).
    wp; ecall (__m_rlen_write_upto8_proof param_7 param_6 param_5).
    wp; ecall (__m_rlen_write_upto8_proof param_4 param_3 param_2).
    wp; ecall (__m_rlen_write_upto8_proof param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  seq 1 : ((valid trace__dump_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__dump_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_write_upto8_proof param_22 param_21 param_20).
    wp; ecall (__m_rlen_write_upto8_proof param_19 param_18 param_17).
    wp; ecall (__m_rlen_write_upto8_proof param_16 param_15 param_14).
    wp; ecall (__m_rlen_write_upto8_proof param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  seq 4 : ((valid trace__dump_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__dump_m_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= upto /\ (at %% 8 = 0 \/ at = upto) /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 (_upto - _at) /\ buf0 = _buf0 + (at - _at) /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 (_upto - _at) /\ buf1 = _buf1 + (at - _at) /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 (_upto - _at) /\ buf2 = _buf2 + (at - _at) /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 (_upto - _at) /\ buf3 = _buf3 + (at - _at) /\ newat = at + 8)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  if.
  + (* then *)
    wp; ecall (__m_rlen_write_upto8_proof param_22 param_21 param_20).
    wp; ecall (__m_rlen_write_upto8_proof param_19 param_18 param_17).
    wp; ecall (__m_rlen_write_upto8_proof param_16 param_15 param_14).
    wp; ecall (__m_rlen_write_upto8_proof param_13 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma _squeeze_m_updstate_avx2x4_proof _st _b_st _buf0 _buf1 _buf2 _buf3 _len :
      (_squeeze_m_updstate_avx2x4_spec _st _b_st _buf0 _buf1 _buf2 _buf3 
      _len).
proof.
rewrite /_squeeze_m_updstate_avx2x4_spec; proc.
seq 32 : ((valid trace__squeeze_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ len = _len /\ _len <= 18446744073709551360 /\ buf0 = _buf0 /\ 0 <= _buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf1 = _buf1 /\ 0 <= _buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf2 = _buf2 /\ 0 <= _buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf3 = _buf3 /\ 0 <= _buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
if.
+ (* then *)
  seq 11 : ((valid trace__squeeze_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf0 <= buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf0 + (len - at) = _buf0 + _len /\ 0 <= _buf1 <= buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf1 + (len - at) = _buf1 + _len /\ 0 <= _buf2 <= buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf2 + (len - at) = _buf2 + _len /\ 0 <= _buf3 <= buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ buf3 + (len - at) = _buf3 + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_0 b_param_2).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  wp; ecall (_dump_m_updstate_avx2x4_proof param_15 param_14 param_13 param_12 param_11 b_param param_10 param_9).
  wp; while ((valid trace__squeeze_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf0 <= buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf0 + (len - at) = _buf0 + _len /\ 0 <= _buf1 <= buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf1 + (len - at) = _buf1 + _len /\ 0 <= _buf2 <= buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf2 + (len - at) = _buf2 + _len /\ 0 <= _buf3 <= buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ buf3 + (len - at) = _buf3 + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* loop body *)
    wp; ecall (_keccakf1600_avx2x4_proof param_8 b_param_0).
    wp; ecall (_dump_m_updstate_avx2x4_proof param_7 param_6 param_5 param_4 param_3 b_param_1 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
+ (* else *)
  wp; ecall (_dump_m_updstate_avx2x4_proof param_15 param_14 param_13 param_12 param_11 b_param param_10 param_9).
  wp; while ((valid trace__squeeze_m_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= _buf0 <= buf0 /\ is_valid ptr_modulus Glob.mem_v _buf0 _len /\ buf0 + (len - at) = _buf0 + _len /\ 0 <= _buf1 <= buf1 /\ is_valid ptr_modulus Glob.mem_v _buf1 _len /\ buf1 + (len - at) = _buf1 + _len /\ 0 <= _buf2 <= buf2 /\ is_valid ptr_modulus Glob.mem_v _buf2 _len /\ buf2 + (len - at) = _buf2 + _len /\ 0 <= _buf3 <= buf3 /\ is_valid ptr_modulus Glob.mem_v _buf3 _len /\ buf3 + (len - at) = _buf3 + _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* loop body *)
    wp; ecall (_keccakf1600_avx2x4_proof param_8 b_param_0).
    wp; ecall (_dump_m_updstate_avx2x4_proof param_7 param_6 param_5 param_4 param_3 b_param_1 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma absorb_m_bcast_updstate_avx2x4_proof _st _b_st _buf _len :
      (absorb_m_bcast_updstate_avx2x4_spec _st _b_st _buf _len).
proof.
rewrite /absorb_m_bcast_updstate_avx2x4_spec; proc.
wp; ecall (_absorb_m_bcast_updstate_avx2x4_proof param_1 ((BArray808.init_arr (W8.of_int 255))) param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma absorb_m_updstate_avx2x4_proof _st _b_st _buf0 _buf1 _buf2 _buf3 _len :
      (absorb_m_updstate_avx2x4_spec _st _b_st _buf0 _buf1 _buf2 _buf3 _len).
proof.
rewrite /absorb_m_updstate_avx2x4_spec; proc.
wp; ecall (_absorb_m_updstate_avx2x4_proof param_4 ((BArray808.init_arr (W8.of_int 255))) param_3 param_2 param_1 param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

lemma squeeze_m_updstate_avx2x4_proof _st _b_st _buf0 _buf1 _buf2 _buf3 _len :
      (squeeze_m_updstate_avx2x4_spec _st _b_st _buf0 _buf1 _buf2 _buf3 _len).
proof.
rewrite /squeeze_m_updstate_avx2x4_spec; proc.
wp; ecall (_squeeze_m_updstate_avx2x4_proof param_4 ((BArray808.init_arr (W8.of_int 255))) param_3 param_2 param_1 param_0 param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp).
qed.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory KeccakArrayAvx2x4Safety.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

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
   ../extracted/Keccak1600_fixedsizes_avx2x4_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc __addstate_bcast_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                                buf:A.t, b_buf:A.t,
                                offset:int, _LEN:int, _TRAILB:int) : 
  BArray800.t * BArray800.t * int * int * trace = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
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
    var b_param:A.t;
    var b_param_0:A.t;
    var trace___addstate_bcast_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    param_5 <- witness;
    param_12 <- witness;
    trace___addstate_bcast_avx2x4 <- [];
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     (((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
      (A.is_init b_buf offset _LEN)) /\
     (BArray800.is_init b_st 0 800)))))]);
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert,
     ((((0 <= aT) /\ (((aT + _LEN) + ((_TRAILB <> 0) ? 1 : 0)) <= 200)) /\
      (0 <= _TRAILB)) /\
     (_TRAILB < 256)))]);
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      b_param_0 <- b_buf;
      param_5 <- buf;
      param_4 <- offset;
      param_3 <- dELTA;
      param_2 <- _LEN;
      param_1 <- _TRAILB;
      param_0 <- aT;
      param <- aT8;
      (result_3, result_2, result_1, result_0, result, tmp__trace) <@ 
      RW.MM.__a_ilen_read_bcast_upto8_at (param_5, b_param_0, param_4, param_3,
      param_2, param_1, param_0, param);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++ tmp__trace);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
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
      aT8 <- result_0;
      w <- result;
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       ((0 <= ((aT %/ 8) * 32)) /\ ((((aT %/ 8) * 32) + 32) <= 800)))]);
      w <- (w `^` (BArray800.get256 st (aT %/ 8)));
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       ((0 <= ((aT %/ 8) * 32)) /\ ((((aT %/ 8) * 32) + 32) <= 800)))]);
      st <- (BArray800.set256 st (aT %/ 8) w);
      aT <- aT8;
    } else {
      
    }
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert,
     ((0 <= (32 * (aT %/ 8))) /\ ((32 * (aT %/ 8)) <= 18446744073709551615)))]);
    at <- (32 * (aT %/ 8));
    trace___addstate_bcast_avx2x4 <-
    (trace___addstate_bcast_avx2x4 ++
    [(Assert,
     ((0 <= (32 * ((aT %/ 8) + (_LEN %/ 8)))) /\
     ((32 * ((aT %/ 8) + (_LEN %/ 8))) <= 18446744073709551615)))]);
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, (A.is_init b_buf offset 8))]);
      w <- (VPBROADCAST_4u64 (A.get64d buf offset));
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       ((0 <= (offset + 8)) /\ ((offset + 8) <= 18446744073709551615)))]);
      offset <- (offset + 8);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      w <- (w `^` (BArray800.get256d st at));
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      st <- (BArray800.set256d st at w);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= (at + 32)) /\ ((at + 32) <= 18446744073709551615)))]);
      at <- (at + 32);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       ((0 <= (32 * ((aT %/ 8) + (_LEN %/ 8)))) /\
       ((32 * ((aT %/ 8) + (_LEN %/ 8))) <= 18446744073709551615)))]);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      b_param <- b_buf;
      param_12 <- buf;
      param_11 <- offset;
      param_10 <- 0;
      param_9 <- _LEN;
      param_8 <- _TRAILB;
      param_7 <- aT;
      param_6 <- aT;
      (result_8, result_7, result_6, result_5, result_4, tmp__trace) <@ 
      RW.MM.__a_ilen_read_bcast_upto8_at (param_12, b_param, param_11, param_10,
      param_9, param_8, param_7, param_6);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++ tmp__trace);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       (((param_7 <= param_6) /\ (param_6 < (param_7 + 8))) ? ((8 <=
                                                               ((param_6 -
                                                                param_7) +
                                                               param_9)) ? 
                                                              ((((result_8 =
                                                                 (param_10 +
                                                                 ((param_7 +
                                                                  8) -
                                                                 param_6))) /\
                                                                (result_7 =
                                                                (param_9 -
                                                                ((param_7 +
                                                                 8) -
                                                                param_6)))) /\
                                                               (result_6 =
                                                               param_8)) /\
                                                              (result_5 =
                                                              (param_7 + 8))) : 
                                                              ((((result_8 =
                                                                 (param_10 +
                                                                 param_9)) /\
                                                                (result_7 =
                                                                0)) /\
                                                               (result_6 = 0)) /\
                                                              (result_5 =
                                                              ((param_6 +
                                                               param_9) +
                                                              ((param_8 <> 0) ? 1 : 0))))) : 
       ((((result_8 = param_10) /\ (result_7 = param_9)) /\
        (result_6 = param_8)) /\
       (result_5 = param_6))))]);
      dELTA <- result_8;
      aT <- result_5;
      w <- result_4;
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      w <- (w `^` (BArray800.get256d st at));
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      st <- (BArray800.set256d st at w);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
      trace___addstate_bcast_avx2x4 <-
      (trace___addstate_bcast_avx2x4 ++
      [(Assert,
       ((0 <= (offset + dELTA)) /\
       ((offset + dELTA) <= 18446744073709551615)))]);
      offset <- (offset + dELTA);
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, aT, offset, trace___addstate_bcast_avx2x4);
  }
  proc __absorb_bcast_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                              buf:A.t, b_buf:A.t,
                              _TRAILB:int, _RATE8:int) : BArray800.t *
                                                         BArray800.t * int *
                                                         trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
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
    var param_4:BArray800.t;
    var result:int;
    var result_0:int;
    var result_1:BArray800.t;
    var param_5:BArray800.t;
    var result_2:BArray800.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:A.t;
    var param_10:int;
    var param_11:BArray800.t;
    var result_3:int;
    var result_4:int;
    var result_5:BArray800.t;
    var param_12:BArray800.t;
    var result_6:BArray800.t;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var param_16:A.t;
    var param_17:int;
    var param_18:BArray800.t;
    var result_7:int;
    var result_8:int;
    var result_9:BArray800.t;
    var param_19:int;
    var param_20:BArray800.t;
    var result_10:BArray800.t;
    var b_result:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_result_2:BArray800.t;
    var b_result_3:BArray800.t;
    var b_result_4:BArray800.t;
    var trace___absorb_bcast_avx2x4:trace;
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
    trace___absorb_bcast_avx2x4 <- [];
    trace___absorb_bcast_avx2x4 <-
    (trace___absorb_bcast_avx2x4 ++
    [(Assert,
     ((((((((0 <= aT) /\ (aT < _RATE8)) /\ (0 <= _TRAILB)) /\
         (_TRAILB < 256)) /\
        (0 < _RATE8)) /\
       (_RATE8 < 200)) /\
      (A.is_init b_buf 0 _ASIZE)) /\
     (BArray800.is_init b_st 0 800)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      param_4 <- st;
      param_3 <- aT;
      param_2 <- buf;
      param_1 <- offset;
      param_0 <- (_RATE8 - aT);
      param <- 0;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_bcast_avx2x4 (
      param_4, (BArray800.init_arr (W8.of_int 255)), param_3, param_2,
      (A.init_arr (W8.of_int 255)), param_1, param_0, param);
      result_1 <- aux;
      b_result_4 <- aux_0;
      result_0 <- aux_1;
      result <- aux_2;
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++ tmp__trace);
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++
      [(Assert,
       (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
       (((0 <= (param_1 + param_0)) /\
        ((param_1 + param_0) <= 18446744073709551615)) /\
       (((BArray800.is_init b_result_4 0 800) /\
        (result_0 = ((param_3 + param_0) + ((param <> 0) ? 1 : 0)))) /\
       (result = (param_1 + param_0))))))]);
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++
      [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
      st <- result_1;
      offset <- result;
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      param_5 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_5,
      (BArray800.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_3 <- aux_0;
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++ tmp__trace);
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_3 0 800))]);
      st <- result_2;
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_11 <- st;
        param_10 <- 0;
        param_9 <- buf;
        param_8 <- offset;
        param_7 <- _RATE8;
        param_6 <- 0;
        (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_bcast_avx2x4 (
        param_11, (BArray800.init_arr (W8.of_int 255)), param_10, param_9,
        (A.init_arr (W8.of_int 255)), param_8, param_7, param_6);
        result_5 <- aux;
        b_result_2 <- aux_0;
        result_4 <- aux_1;
        result_3 <- aux_2;
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++
        [(Assert,
         (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
         (((0 <= (param_8 + param_7)) /\
          ((param_8 + param_7) <= 18446744073709551615)) /\
         (((BArray800.is_init b_result_2 0 800) /\
          (result_4 = ((param_10 + param_7) + ((param_6 <> 0) ? 1 : 0)))) /\
         (result_3 = (param_8 + param_7))))))]);
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++
        [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
        st <- result_5;
        offset <- result_3;
        param_12 <- st;
        (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_12,
        (BArray800.init_arr (W8.of_int 255)));
        result_6 <- aux;
        b_result_1 <- aux_0;
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++
        [(Assert, (BArray800.is_init b_result_1 0 800))]);
        st <- result_6;
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_bcast_avx2x4 <-
        (trace___absorb_bcast_avx2x4 ++
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
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_bcast_avx2x4 (
    param_18, (BArray800.init_arr (W8.of_int 255)), param_17, param_16,
    (A.init_arr (W8.of_int 255)), param_15, param_14, param_13);
    result_9 <- aux;
    b_result_0 <- aux_0;
    result_8 <- aux_1;
    result_7 <- aux_2;
    trace___absorb_bcast_avx2x4 <-
    (trace___absorb_bcast_avx2x4 ++ tmp__trace);
    trace___absorb_bcast_avx2x4 <-
    (trace___absorb_bcast_avx2x4 ++
    [(Assert,
     (((0 <= param_14) /\ (param_14 <= 18446744073709551615)) /\
     (((0 <= (param_15 + param_14)) /\
      ((param_15 + param_14) <= 18446744073709551615)) /\
     (((BArray800.is_init b_result_0 0 800) /\
      (result_8 = ((param_17 + param_14) + ((param_13 <> 0) ? 1 : 0)))) /\
     (result_7 = (param_15 + param_14))))))]);
    trace___absorb_bcast_avx2x4 <-
    (trace___absorb_bcast_avx2x4 ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    st <- result_9;
    aT <- result_8;
    if ((_TRAILB <> 0)) {
      param_20 <- st;
      param_19 <- _RATE8;
      (aux, aux_0, tmp__trace) <@ M.__addratebit_avx2x4 (param_20,
      (BArray800.init_arr (W8.of_int 255)), param_19);
      result_10 <- aux;
      b_result <- aux_0;
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++ tmp__trace);
      trace___absorb_bcast_avx2x4 <-
      (trace___absorb_bcast_avx2x4 ++
      [(Assert, (BArray800.is_init b_result 0 800))]);
      st <- result_10;
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, aT, trace___absorb_bcast_avx2x4);
  }
  proc __addstate_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                          buf0:A.t, b_buf0:A.t,
                          buf1:A.t, b_buf1:A.t,
                          buf2:A.t, b_buf2:A.t,
                          buf3:A.t, b_buf3:A.t, offset:int,
                          _LEN:int, _TRAILB:int) : BArray800.t *
                                                   BArray800.t * int * int *
                                                   trace = {
    var dELTA:int;
    var aT8:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var at:int;
    var param:int;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:A.t;
    var result:W64.t;
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
    var result_4:W64.t;
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
    var result_14:W64.t;
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
    var result_24:W64.t;
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
    var result_34:W64.t;
    var result_35:int;
    var result_36:int;
    var result_37:int;
    var result_38:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_param_3:A.t;
    var b_param_4:A.t;
    var b_param_5:A.t;
    var b_param_6:A.t;
    var trace___addstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    param_5 <- witness;
    param_12 <- witness;
    param_19 <- witness;
    param_26 <- witness;
    param_33 <- witness;
    param_40 <- witness;
    param_47 <- witness;
    param_54 <- witness;
    trace___addstate_avx2x4 <- [];
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     ((((((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
         (BArray800.is_init b_st 0 800)) /\
        (A.is_init b_buf0 offset _LEN)) /\
       (A.is_init b_buf1 offset _LEN)) /\
      (A.is_init b_buf2 offset _LEN)) /\
     (A.is_init b_buf3 offset _LEN)))))]);
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert,
     ((((0 <= _TRAILB) /\ (_TRAILB < 256)) /\ (0 <= aT)) /\
     (((aT + _LEN) + ((_TRAILB <> 0) ? 1 : 0)) <= 200)))]);
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      b_param_6 <- b_buf0;
      param_5 <- buf0;
      param_4 <- offset;
      param_3 <- dELTA;
      param_2 <- _LEN;
      param_1 <- _TRAILB;
      param_0 <- aT;
      param <- aT8;
      (result_3, result_2, result_1, result_0, result, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_5, b_param_6, param_4, param_3, param_2,
      param_1, param_0, param);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
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
      t0 <- result;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * (aT %/ 8)) * 8)) /\ ((((4 * (aT %/ 8)) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * (aT %/ 8)) * 8)) /\ ((((4 * (aT %/ 8)) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (4 * (aT %/ 8))
      ((BArray800.get64 st (4 * (aT %/ 8))) `^` t0));
      b_param_5 <- b_buf1;
      param_12 <- buf1;
      param_11 <- offset;
      param_10 <- dELTA;
      param_9 <- _LEN;
      param_8 <- _TRAILB;
      param_7 <- aT;
      param_6 <- aT8;
      (result_8, result_7, result_6, result_5, result_4, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_12, b_param_5, param_11, param_10,
      param_9, param_8, param_7, param_6);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_7 <= param_6) /\ (param_6 < (param_7 + 8))) ? ((8 <=
                                                               ((param_6 -
                                                                param_7) +
                                                               param_9)) ? 
                                                              ((((result_8 =
                                                                 (param_10 +
                                                                 ((param_7 +
                                                                  8) -
                                                                 param_6))) /\
                                                                (result_7 =
                                                                (param_9 -
                                                                ((param_7 +
                                                                 8) -
                                                                param_6)))) /\
                                                               (result_6 =
                                                               param_8)) /\
                                                              (result_5 =
                                                              (param_7 + 8))) : 
                                                              ((((result_8 =
                                                                 (param_10 +
                                                                 param_9)) /\
                                                                (result_7 =
                                                                0)) /\
                                                               (result_6 = 0)) /\
                                                              (result_5 =
                                                              ((param_6 +
                                                               param_9) +
                                                              ((param_8 <> 0) ? 1 : 0))))) : 
       ((((result_8 = param_10) /\ (result_7 = param_9)) /\
        (result_6 = param_8)) /\
       (result_5 = param_6))))]);
      t1 <- result_4;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 1) * 8)) /\
       (((((4 * (aT %/ 8)) + 1) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 1) * 8)) /\
       (((((4 * (aT %/ 8)) + 1) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st ((4 * (aT %/ 8)) + 1)
      ((BArray800.get64 st ((4 * (aT %/ 8)) + 1)) `^` t1));
      b_param_4 <- b_buf2;
      param_19 <- buf2;
      param_18 <- offset;
      param_17 <- dELTA;
      param_16 <- _LEN;
      param_15 <- _TRAILB;
      param_14 <- aT;
      param_13 <- aT8;
      (result_13, result_12, result_11, result_10, result_9, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_19, b_param_4, param_18, param_17,
      param_16, param_15, param_14, param_13);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
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
      t2 <- result_9;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 2) * 8)) /\
       (((((4 * (aT %/ 8)) + 2) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 2) * 8)) /\
       (((((4 * (aT %/ 8)) + 2) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st ((4 * (aT %/ 8)) + 2)
      ((BArray800.get64 st ((4 * (aT %/ 8)) + 2)) `^` t2));
      b_param_3 <- b_buf3;
      param_26 <- buf3;
      param_25 <- offset;
      param_24 <- dELTA;
      param_23 <- _LEN;
      param_22 <- _TRAILB;
      param_21 <- aT;
      param_20 <- aT8;
      (result_18, result_17, result_16, result_15, result_14, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_26, b_param_3, param_25, param_24,
      param_23, param_22, param_21, param_20);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_21 <= param_20) /\ (param_20 < (param_21 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_20 -
                                                                    param_21) +
                                                                   param_23)) ? 
                                                                  (((
                                                                    (
                                                                    result_18 =
                                                                    (
                                                                    param_24 +
                                                                    (
                                                                    (
                                                                    param_21 +
                                                                    8) -
                                                                    param_20))) /\
                                                                    (
                                                                    result_17 =
                                                                    (
                                                                    param_23 -
                                                                    (
                                                                    (
                                                                    param_21 +
                                                                    8) -
                                                                    param_20)))) /\
                                                                   (result_16 =
                                                                   param_22)) /\
                                                                  (result_15 =
                                                                  (param_21 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_18 =
                                                                    (
                                                                    param_24 +
                                                                    param_23)) /\
                                                                    (
                                                                    result_17 =
                                                                    0)) /\
                                                                   (result_16 =
                                                                   0)) /\
                                                                  (result_15 =
                                                                  ((param_20 +
                                                                   param_23) +
                                                                  ((param_22 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_18 = param_24) /\ (result_17 = param_23)) /\
        (result_16 = param_22)) /\
       (result_15 = param_20))))]);
      dELTA <- result_18;
      _LEN <- result_17;
      _TRAILB <- result_16;
      aT8 <- result_15;
      t3 <- result_14;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 3) * 8)) /\
       (((((4 * (aT %/ 8)) + 3) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (((4 * (aT %/ 8)) + 3) * 8)) /\
       (((((4 * (aT %/ 8)) + 3) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st ((4 * (aT %/ 8)) + 3)
      ((BArray800.get64 st ((4 * (aT %/ 8)) + 3)) `^` t3));
      aT <- aT8;
    } else {
      
    }
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert,
     ((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)))]);
    offset <- (offset + dELTA);
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert,
     ((0 <= (4 * (aT %/ 8))) /\ ((4 * (aT %/ 8)) <= 18446744073709551615)))]);
    at <- (4 * (aT %/ 8));
    trace___addstate_avx2x4 <-
    (trace___addstate_avx2x4 ++
    [(Assert,
     ((0 <= ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))) /\
     (((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))) <= 18446744073709551615)))]);
    while ((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))))) {
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, (A.is_init b_buf0 offset 8))]);
      t0 <- (A.get64d buf0 offset);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st at ((BArray800.get64 st at) `^` t0));
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, (A.is_init b_buf1 offset 8))]);
      t1 <- (A.get64d buf1 offset);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 1) ((BArray800.get64 st (at + 1)) `^` t1));
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, (A.is_init b_buf2 offset 8))]);
      t2 <- (A.get64d buf2 offset);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 2) ((BArray800.get64 st (at + 2)) `^` t2));
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, (A.is_init b_buf3 offset 8))]);
      t3 <- (A.get64d buf3 offset);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (offset + 8)) /\ ((offset + 8) <= 18446744073709551615)))]);
      offset <- (offset + 8);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 3) ((BArray800.get64 st (at + 3)) `^` t3));
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 4)) /\ ((at + 4) <= 18446744073709551615)))]);
      at <- (at + 4);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))) /\
       (((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))) <= 18446744073709551615)))]);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      b_param_2 <- b_buf0;
      param_33 <- buf0;
      param_32 <- offset;
      param_31 <- 0;
      param_30 <- _LEN;
      param_29 <- _TRAILB;
      param_28 <- aT;
      param_27 <- aT;
      (result_23, result_22, result_21, result_20, result_19, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_33, b_param_2, param_32, param_31,
      param_30, param_29, param_28, param_27);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_28 <= param_27) /\ (param_27 < (param_28 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_27 -
                                                                    param_28) +
                                                                   param_30)) ? 
                                                                  (((
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
                                                                   (result_21 =
                                                                   param_29)) /\
                                                                  (result_20 =
                                                                  (param_28 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_23 =
                                                                    (
                                                                    param_31 +
                                                                    param_30)) /\
                                                                    (
                                                                    result_22 =
                                                                    0)) /\
                                                                   (result_21 =
                                                                   0)) /\
                                                                  (result_20 =
                                                                  ((param_27 +
                                                                   param_30) +
                                                                  ((param_29 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_23 = param_31) /\ (result_22 = param_30)) /\
        (result_21 = param_29)) /\
       (result_20 = param_27))))]);
      t0 <- result_19;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st at ((BArray800.get64 st at) `^` t0));
      b_param_1 <- b_buf1;
      param_40 <- buf1;
      param_39 <- offset;
      param_38 <- 0;
      param_37 <- _LEN;
      param_36 <- _TRAILB;
      param_35 <- aT;
      param_34 <- aT;
      (result_28, result_27, result_26, result_25, result_24, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_40, b_param_1, param_39, param_38,
      param_37, param_36, param_35, param_34);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_35 <= param_34) /\ (param_34 < (param_35 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_34 -
                                                                    param_35) +
                                                                   param_37)) ? 
                                                                  (((
                                                                    (
                                                                    result_28 =
                                                                    (
                                                                    param_38 +
                                                                    (
                                                                    (
                                                                    param_35 +
                                                                    8) -
                                                                    param_34))) /\
                                                                    (
                                                                    result_27 =
                                                                    (
                                                                    param_37 -
                                                                    (
                                                                    (
                                                                    param_35 +
                                                                    8) -
                                                                    param_34)))) /\
                                                                   (result_26 =
                                                                   param_36)) /\
                                                                  (result_25 =
                                                                  (param_35 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_28 =
                                                                    (
                                                                    param_38 +
                                                                    param_37)) /\
                                                                    (
                                                                    result_27 =
                                                                    0)) /\
                                                                   (result_26 =
                                                                   0)) /\
                                                                  (result_25 =
                                                                  ((param_34 +
                                                                   param_37) +
                                                                  ((param_36 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_28 = param_38) /\ (result_27 = param_37)) /\
        (result_26 = param_36)) /\
       (result_25 = param_34))))]);
      t1 <- result_24;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 1) ((BArray800.get64 st (at + 1)) `^` t1));
      b_param_0 <- b_buf2;
      param_47 <- buf2;
      param_46 <- offset;
      param_45 <- 0;
      param_44 <- _LEN;
      param_43 <- _TRAILB;
      param_42 <- aT;
      param_41 <- aT;
      (result_33, result_32, result_31, result_30, result_29, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_47, b_param_0, param_46, param_45,
      param_44, param_43, param_42, param_41);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_42 <= param_41) /\ (param_41 < (param_42 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_41 -
                                                                    param_42) +
                                                                   param_44)) ? 
                                                                  (((
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
                                                                   (result_31 =
                                                                   param_43)) /\
                                                                  (result_30 =
                                                                  (param_42 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_33 =
                                                                    (
                                                                    param_45 +
                                                                    param_44)) /\
                                                                    (
                                                                    result_32 =
                                                                    0)) /\
                                                                   (result_31 =
                                                                   0)) /\
                                                                  (result_30 =
                                                                  ((param_41 +
                                                                   param_44) +
                                                                  ((param_43 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_33 = param_45) /\ (result_32 = param_44)) /\
        (result_31 = param_43)) /\
       (result_30 = param_41))))]);
      t2 <- result_29;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 2) ((BArray800.get64 st (at + 2)) `^` t2));
      b_param <- b_buf3;
      param_54 <- buf3;
      param_53 <- offset;
      param_52 <- 0;
      param_51 <- _LEN;
      param_50 <- _TRAILB;
      param_49 <- aT;
      param_48 <- aT;
      (result_38, result_37, result_36, result_35, result_34, tmp__trace) <@ 
      RW.MM.__a_ilen_read_upto8_at (param_54, b_param, param_53, param_52,
      param_51, param_50, param_49, param_48);
      trace___addstate_avx2x4 <- (trace___addstate_avx2x4 ++ tmp__trace);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       (((param_49 <= param_48) /\ (param_48 < (param_49 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_48 -
                                                                    param_49) +
                                                                   param_51)) ? 
                                                                  (((
                                                                    (
                                                                    result_38 =
                                                                    (
                                                                    param_52 +
                                                                    (
                                                                    (
                                                                    param_49 +
                                                                    8) -
                                                                    param_48))) /\
                                                                    (
                                                                    result_37 =
                                                                    (
                                                                    param_51 -
                                                                    (
                                                                    (
                                                                    param_49 +
                                                                    8) -
                                                                    param_48)))) /\
                                                                   (result_36 =
                                                                   param_50)) /\
                                                                  (result_35 =
                                                                  (param_49 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_38 =
                                                                    (
                                                                    param_52 +
                                                                    param_51)) /\
                                                                    (
                                                                    result_37 =
                                                                    0)) /\
                                                                   (result_36 =
                                                                   0)) /\
                                                                  (result_35 =
                                                                  ((param_48 +
                                                                   param_51) +
                                                                  ((param_50 <>
                                                                   0) ? 1 : 0))))) : 
       ((((result_38 = param_52) /\ (result_37 = param_51)) /\
        (result_36 = param_50)) /\
       (result_35 = param_48))))]);
      dELTA <- result_38;
      aT <- result_35;
      t3 <- result_34;
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64 st (at + 3) ((BArray800.get64 st (at + 3)) `^` t3));
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
      trace___addstate_avx2x4 <-
      (trace___addstate_avx2x4 ++
      [(Assert,
       ((0 <= (offset + dELTA)) /\
       ((offset + dELTA) <= 18446744073709551615)))]);
      offset <- (offset + dELTA);
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, aT, offset, trace___addstate_avx2x4);
  }
  proc __absorb_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                        buf0:A.t, b_buf0:A.t,
                        buf1:A.t, b_buf1:A.t,
                        buf2:A.t, b_buf2:A.t,
                        buf3:A.t, b_buf3:A.t, _TRAILB:int,
                        _RATE8:int) : BArray800.t * BArray800.t * int * trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
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
    var param_3:A.t;
    var param_4:A.t;
    var param_5:A.t;
    var param_6:int;
    var param_7:BArray800.t;
    var result:int;
    var result_0:int;
    var result_1:BArray800.t;
    var param_8:BArray800.t;
    var result_2:BArray800.t;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:A.t;
    var param_13:A.t;
    var param_14:A.t;
    var param_15:A.t;
    var param_16:int;
    var param_17:BArray800.t;
    var result_3:int;
    var result_4:int;
    var result_5:BArray800.t;
    var param_18:BArray800.t;
    var result_6:BArray800.t;
    var param_19:int;
    var param_20:int;
    var param_21:int;
    var param_22:A.t;
    var param_23:A.t;
    var param_24:A.t;
    var param_25:A.t;
    var param_26:int;
    var param_27:BArray800.t;
    var result_7:int;
    var result_8:int;
    var result_9:BArray800.t;
    var param_28:int;
    var param_29:BArray800.t;
    var result_10:BArray800.t;
    var b_result:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_result_2:BArray800.t;
    var b_result_3:BArray800.t;
    var b_result_4:BArray800.t;
    var trace___absorb_avx2x4:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    param_25 <- witness;
    param_27 <- witness;
    param_29 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_9 <- witness;
    result_10 <- witness;
    trace___absorb_avx2x4 <- [];
    trace___absorb_avx2x4 <-
    (trace___absorb_avx2x4 ++
    [(Assert,
     (((((((((((0 < _RATE8) /\ (_RATE8 < 200)) /\ (0 <= _TRAILB)) /\
            (_TRAILB < 256)) /\
           (0 <= aT)) /\
          (aT < _RATE8)) /\
         (A.is_init b_buf0 0 _ASIZE)) /\
        (A.is_init b_buf1 0 _ASIZE)) /\
       (A.is_init b_buf2 0 _ASIZE)) /\
      (A.is_init b_buf3 0 _ASIZE)) /\
     (BArray800.is_init b_st 0 800)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      param_7 <- st;
      param_6 <- aT;
      param_5 <- buf0;
      param_4 <- buf1;
      param_3 <- buf2;
      param_2 <- buf3;
      param_1 <- offset;
      param_0 <- (_RATE8 - aT);
      param <- 0;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2x4 (param_7,
      (BArray800.init_arr (W8.of_int 255)), param_6, param_5,
      (A.init_arr (W8.of_int 255)), param_4,
      (A.init_arr (W8.of_int 255)), param_3,
      (A.init_arr (W8.of_int 255)), param_2,
      (A.init_arr (W8.of_int 255)), param_1, param_0, param);
      result_1 <- aux;
      b_result_4 <- aux_0;
      result_0 <- aux_1;
      result <- aux_2;
      trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
      trace___absorb_avx2x4 <-
      (trace___absorb_avx2x4 ++
      [(Assert,
       (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
       (((0 <= (param_1 + param_0)) /\
        ((param_1 + param_0) <= 18446744073709551615)) /\
       (((BArray800.is_init b_result_4 0 800) /\
        (result_0 = ((param_6 + param_0) + ((param <> 0) ? 1 : 0)))) /\
       (result = (param_1 + param_0))))))]);
      trace___absorb_avx2x4 <-
      (trace___absorb_avx2x4 ++
      [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
      st <- result_1;
      offset <- result;
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      param_8 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_8,
      (BArray800.init_arr (W8.of_int 255)));
      result_2 <- aux;
      b_result_3 <- aux_0;
      trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
      trace___absorb_avx2x4 <-
      (trace___absorb_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_3 0 800))]);
      st <- result_2;
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      trace___absorb_avx2x4 <-
      (trace___absorb_avx2x4 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_17 <- st;
        param_16 <- 0;
        param_15 <- buf0;
        param_14 <- buf1;
        param_13 <- buf2;
        param_12 <- buf3;
        param_11 <- offset;
        param_10 <- _RATE8;
        param_9 <- 0;
        (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2x4 (
        param_17, (BArray800.init_arr (W8.of_int 255)), param_16, param_15,
        (A.init_arr (W8.of_int 255)), param_14,
        (A.init_arr (W8.of_int 255)), param_13,
        (A.init_arr (W8.of_int 255)), param_12,
        (A.init_arr (W8.of_int 255)), param_11, param_10, param_9);
        result_5 <- aux;
        b_result_2 <- aux_0;
        result_4 <- aux_1;
        result_3 <- aux_2;
        trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
        trace___absorb_avx2x4 <-
        (trace___absorb_avx2x4 ++
        [(Assert,
         (((0 <= param_10) /\ (param_10 <= 18446744073709551615)) /\
         (((0 <= (param_11 + param_10)) /\
          ((param_11 + param_10) <= 18446744073709551615)) /\
         (((BArray800.is_init b_result_2 0 800) /\
          (result_4 = ((param_16 + param_10) + ((param_9 <> 0) ? 1 : 0)))) /\
         (result_3 = (param_11 + param_10))))))]);
        trace___absorb_avx2x4 <-
        (trace___absorb_avx2x4 ++
        [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
        st <- result_5;
        offset <- result_3;
        param_18 <- st;
        (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_18,
        (BArray800.init_arr (W8.of_int 255)));
        result_6 <- aux;
        b_result_1 <- aux_0;
        trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
        trace___absorb_avx2x4 <-
        (trace___absorb_avx2x4 ++
        [(Assert, (BArray800.is_init b_result_1 0 800))]);
        st <- result_6;
        trace___absorb_avx2x4 <-
        (trace___absorb_avx2x4 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_avx2x4 <-
        (trace___absorb_avx2x4 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    param_27 <- st;
    param_26 <- aT;
    param_25 <- buf0;
    param_24 <- buf1;
    param_23 <- buf2;
    param_22 <- buf3;
    param_21 <- offset;
    param_20 <- _LEN;
    param_19 <- _TRAILB;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ __addstate_avx2x4 (param_27,
    (BArray800.init_arr (W8.of_int 255)), param_26, param_25,
    (A.init_arr (W8.of_int 255)), param_24,
    (A.init_arr (W8.of_int 255)), param_23,
    (A.init_arr (W8.of_int 255)), param_22,
    (A.init_arr (W8.of_int 255)), param_21, param_20, param_19);
    result_9 <- aux;
    b_result_0 <- aux_0;
    result_8 <- aux_1;
    result_7 <- aux_2;
    trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
    trace___absorb_avx2x4 <-
    (trace___absorb_avx2x4 ++
    [(Assert,
     (((0 <= param_20) /\ (param_20 <= 18446744073709551615)) /\
     (((0 <= (param_21 + param_20)) /\
      ((param_21 + param_20) <= 18446744073709551615)) /\
     (((BArray800.is_init b_result_0 0 800) /\
      (result_8 = ((param_26 + param_20) + ((param_19 <> 0) ? 1 : 0)))) /\
     (result_7 = (param_21 + param_20))))))]);
    trace___absorb_avx2x4 <-
    (trace___absorb_avx2x4 ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    st <- result_9;
    aT <- result_8;
    if ((_TRAILB <> 0)) {
      param_29 <- st;
      param_28 <- _RATE8;
      (aux, aux_0, tmp__trace) <@ M.__addratebit_avx2x4 (param_29,
      (BArray800.init_arr (W8.of_int 255)), param_28);
      result_10 <- aux;
      b_result <- aux_0;
      trace___absorb_avx2x4 <- (trace___absorb_avx2x4 ++ tmp__trace);
      trace___absorb_avx2x4 <-
      (trace___absorb_avx2x4 ++
      [(Assert, (BArray800.is_init b_result 0 800))]);
      st <- result_10;
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, aT, trace___absorb_avx2x4);
  }
  proc __dumpstate_avx2x4 (buf0:A.t, b_buf0:A.t,
                           buf1:A.t, b_buf1:A.t,
                           buf2:A.t, b_buf2:A.t,
                           buf3:A.t, b_buf3:A.t, offset:int,
                           _LEN:int, st:BArray800.t, b_st:BArray800.t) : 
  A.t * A.t * A.t * A.t * A.t *
  A.t * A.t * A.t * int * trace = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:W256.t;
    var result:W256.t;
    var result_0:W256.t;
    var result_1:W256.t;
    var result_2:W256.t;
    var param_3:W64.t;
    var param_4:int;
    var param_5:int;
    var param_6:int;
    var param_7:A.t;
    var result_3:int;
    var result_4:int;
    var result_5:A.t;
    var param_8:W64.t;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:A.t;
    var result_6:int;
    var result_7:int;
    var result_8:A.t;
    var param_13:W64.t;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var param_17:A.t;
    var result_9:int;
    var result_10:int;
    var result_11:A.t;
    var param_18:W64.t;
    var param_19:int;
    var param_20:int;
    var param_21:int;
    var param_22:A.t;
    var result_12:int;
    var result_13:int;
    var result_14:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var b_result_0:A.t;
    var b_param_0:A.t;
    var b_result_1:A.t;
    var b_param_1:A.t;
    var b_result_2:A.t;
    var b_param_2:A.t;
    var trace___dumpstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    param_7 <- witness;
    param_12 <- witness;
    param_17 <- witness;
    param_22 <- witness;
    result_5 <- witness;
    result_8 <- witness;
    result_11 <- witness;
    result_14 <- witness;
    trace___dumpstate_avx2x4 <- [];
    trace___dumpstate_avx2x4 <-
    (trace___dumpstate_avx2x4 ++
    [(Assert,
     (((0 <= _LEN) /\ (_LEN <= 18446744073709551615)) /\
     (((0 <= (offset + _LEN)) /\ ((offset + _LEN) <= 18446744073709551615)) /\
     (((((((((0 <= offset) /\ (0 <= _LEN)) /\ ((offset + _LEN) <= _ASIZE)) /\
          (BArray800.is_init b_st 0 800)) /\
         (_LEN <= 200)) /\
        (A.is_init b_buf0 0 offset)) /\
       (A.is_init b_buf1 0 offset)) /\
      (A.is_init b_buf2 0 offset)) /\
     (A.is_init b_buf3 0 offset)))))]);
    trace___dumpstate_avx2x4 <-
    (trace___dumpstate_avx2x4 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    i <- 0;
    trace___dumpstate_avx2x4 <-
    (trace___dumpstate_avx2x4 ++
    [(Assert,
     ((0 <= (32 * (_LEN %/ 32))) /\
     ((32 * (_LEN %/ 32)) <= 18446744073709551615)))]);
    while ((i < (32 * (_LEN %/ 32)))) {
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 32) <= 800)))]);
      x0 <- (BArray800.get256d st (4 * i));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 32)) /\ (((4 * i) + 32) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 32)) /\ ((((4 * i) + 32) + 32) <= 800)))]);
      x1 <- (BArray800.get256d st ((4 * i) + 32));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 64)) /\ (((4 * i) + 64) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 64)) /\ ((((4 * i) + 64) + 32) <= 800)))]);
      x2 <- (BArray800.get256d st ((4 * i) + 64));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 96)) /\ (((4 * i) + 96) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 96)) /\ ((((4 * i) + 96) + 32) <= 800)))]);
      x3 <- (BArray800.get256d st ((4 * i) + 96));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (i + 32)) /\ ((i + 32) <= 18446744073709551615)))]);
      i <- (i + 32);
      param_2 <- x0;
      param_1 <- x1;
      param_0 <- x2;
      param <- x3;
      (result_2, result_1, result_0, result, tmp__trace) <@ M.__4u64x4_u256x4 (
      param_2, param_1, param_0, param);
      trace___dumpstate_avx2x4 <- (trace___dumpstate_avx2x4 ++ tmp__trace);
      x0 <- result_2;
      x1 <- result_1;
      x2 <- result_0;
      x3 <- result;
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 32) <= _ASIZE)))]);
      b_buf0 <-
      (A.set256d b_buf0 offset
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      buf0 <- (A.set256d buf0 offset x0);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 32) <= _ASIZE)))]);
      b_buf1 <-
      (A.set256d b_buf1 offset
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      buf1 <- (A.set256d buf1 offset x1);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 32) <= _ASIZE)))]);
      b_buf2 <-
      (A.set256d b_buf2 offset
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      buf2 <- (A.set256d buf2 offset x2);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 32) <= _ASIZE)))]);
      b_buf3 <-
      (A.set256d b_buf3 offset
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      buf3 <- (A.set256d buf3 offset x3);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (offset + 32)) /\ ((offset + 32) <= 18446744073709551615)))]);
      offset <- (offset + 32);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (32 * (_LEN %/ 32))) /\
       ((32 * (_LEN %/ 32)) <= 18446744073709551615)))]);
    }
    trace___dumpstate_avx2x4 <-
    (trace___dumpstate_avx2x4 ++
    [(Assert,
     ((0 <= (8 * (_LEN %/ 8))) /\
     ((8 * (_LEN %/ 8)) <= 18446744073709551615)))]);
    while ((i < (8 * (_LEN %/ 8)))) {
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 8) <= 800)))]);
      t0 <- (BArray800.get64d st (4 * i));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      b_buf0 <-
      (A.set64d b_buf0 offset (W64.of_int 18446744073709551615));
      buf0 <- (A.set64d buf0 offset t0);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 8)) /\ (((4 * i) + 8) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 8)) /\ ((((4 * i) + 8) + 8) <= 800)))]);
      t1 <- (BArray800.get64d st ((4 * i) + 8));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      b_buf1 <-
      (A.set64d b_buf1 offset (W64.of_int 18446744073709551615));
      buf1 <- (A.set64d buf1 offset t1);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 16)) /\ (((4 * i) + 16) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 16)) /\ ((((4 * i) + 16) + 8) <= 800)))]);
      t2 <- (BArray800.get64d st ((4 * i) + 16));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      b_buf2 <-
      (A.set64d b_buf2 offset (W64.of_int 18446744073709551615));
      buf2 <- (A.set64d buf2 offset t2);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 24)) /\ (((4 * i) + 24) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 24)) /\ ((((4 * i) + 24) + 8) <= 800)))]);
      t3 <- (BArray800.get64d st ((4 * i) + 24));
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= offset) /\ ((offset + 8) <= _ASIZE)))]);
      b_buf3 <-
      (A.set64d b_buf3 offset (W64.of_int 18446744073709551615));
      buf3 <- (A.set64d buf3 offset t3);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (i + 8)) /\ ((i + 8) <= 18446744073709551615)))]);
      i <- (i + 8);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (offset + 8)) /\ ((offset + 8) <= 18446744073709551615)))]);
      offset <- (offset + 8);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (8 * (_LEN %/ 8))) /\
       ((8 * (_LEN %/ 8)) <= 18446744073709551615)))]);
    }
    if ((0 < (_LEN %% 8))) {
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 8) <= 800)))]);
      t0 <- (BArray800.get64d st (4 * i));
      b_param_2 <- b_buf0;
      param_7 <- buf0;
      param_6 <- offset;
      param_5 <- 0;
      param_4 <- (_LEN %% 8);
      param_3 <- t0;
      (result_5, b_result_2, result_4, result_3, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_7, b_param_2, param_6, param_5, param_4, param_3);
      trace___dumpstate_avx2x4 <- (trace___dumpstate_avx2x4 ++ tmp__trace);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       (((0 <= param_5) /\ (param_5 <= 18446744073709551615)) /\
       (((0 <= (param_6 + param_5)) /\
        ((param_6 + param_5) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8))) /\
        (((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_6 + param_5) +
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8)))) /\
        (((param_6 + param_5) +
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8))) <=
        18446744073709551615)) /\
       (((result_4 =
         (param_5 +
         ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? 
                                                    param_4 : 8)))) /\
        (result_3 =
        (param_4 -
        ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? param_4 : 8))))) /\
       (A.is_init b_result_2 0
       ((param_6 + param_5) +
       ((((param_4 < 8) ? param_4 : 8) < 0) ? 0 : ((param_4 < 8) ? param_4 : 8)))
       )))))))]);
      b_buf0 <- b_result_2;
      buf0 <- result_5;
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 8)) /\ (((4 * i) + 8) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 8)) /\ ((((4 * i) + 8) + 8) <= 800)))]);
      t1 <- (BArray800.get64d st ((4 * i) + 8));
      b_param_1 <- b_buf1;
      param_12 <- buf1;
      param_11 <- offset;
      param_10 <- 0;
      param_9 <- (_LEN %% 8);
      param_8 <- t1;
      (result_8, b_result_1, result_7, result_6, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_12, b_param_1, param_11, param_10, param_9, param_8);
      trace___dumpstate_avx2x4 <- (trace___dumpstate_avx2x4 ++ tmp__trace);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       (((0 <= param_10) /\ (param_10 <= 18446744073709551615)) /\
       (((0 <= (param_11 + param_10)) /\
        ((param_11 + param_10) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? 
                                                    param_9 : 8))) /\
        (((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? 
                                                    param_9 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_11 + param_10) +
         ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? 
                                                    param_9 : 8)))) /\
        (((param_11 + param_10) +
         ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? 
                                                    param_9 : 8))) <=
        18446744073709551615)) /\
       (((result_7 =
         (param_10 +
         ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? 
                                                    param_9 : 8)))) /\
        (result_6 =
        (param_9 -
        ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? param_9 : 8))))) /\
       (A.is_init b_result_1 0
       ((param_11 + param_10) +
       ((((param_9 < 8) ? param_9 : 8) < 0) ? 0 : ((param_9 < 8) ? param_9 : 8)))
       )))))))]);
      b_buf1 <- b_result_1;
      buf1 <- result_8;
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 16)) /\ (((4 * i) + 16) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 16)) /\ ((((4 * i) + 16) + 8) <= 800)))]);
      t2 <- (BArray800.get64d st ((4 * i) + 16));
      b_param_0 <- b_buf2;
      param_17 <- buf2;
      param_16 <- offset;
      param_15 <- 0;
      param_14 <- (_LEN %% 8);
      param_13 <- t2;
      (result_11, b_result_0, result_10, result_9, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_17, b_param_0, param_16, param_15, param_14, param_13);
      trace___dumpstate_avx2x4 <- (trace___dumpstate_avx2x4 ++ tmp__trace);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       (((0 <= param_15) /\ (param_15 <= 18446744073709551615)) /\
       (((0 <= (param_16 + param_15)) /\
        ((param_16 + param_15) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8))) /\
        (((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_16 + param_15) +
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8)))) /\
        (((param_16 + param_15) +
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8))) <=
        18446744073709551615)) /\
       (((result_10 =
         (param_15 +
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8)))) /\
        (result_9 =
        (param_14 -
        ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                     param_14 : 8))))) /\
       (A.is_init b_result_0 0
       ((param_16 + param_15) +
       ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                    param_14 : 8)))
       )))))))]);
      b_buf2 <- b_result_0;
      buf2 <- result_11;
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 24)) /\ (((4 * i) + 24) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 24)) /\ ((((4 * i) + 24) + 8) <= 800)))]);
      t3 <- (BArray800.get64d st ((4 * i) + 24));
      b_param <- b_buf3;
      param_22 <- buf3;
      param_21 <- offset;
      param_20 <- 0;
      param_19 <- (_LEN %% 8);
      param_18 <- t3;
      (result_14, b_result, result_13, result_12, tmp__trace) <@ RW.MM.__a_ilen_write_upto8 (
      param_22, b_param, param_21, param_20, param_19, param_18);
      trace___dumpstate_avx2x4 <- (trace___dumpstate_avx2x4 ++ tmp__trace);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       (((0 <= param_20) /\ (param_20 <= 18446744073709551615)) /\
       (((0 <= (param_21 + param_20)) /\
        ((param_21 + param_20) <= 18446744073709551615)) /\
       (((0 <=
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) /\
        (((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         ((param_21 + param_20) +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)))) /\
        (((param_21 + param_20) +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) <=
        18446744073709551615)) /\
       (((result_13 =
         (param_20 +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)))) /\
        (result_12 =
        (param_19 -
        ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                     param_19 : 8))))) /\
       (A.is_init b_result 0
       ((param_21 + param_20) +
       ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                    param_19 : 8)))
       )))))))]);
      b_buf3 <- b_result;
      buf3 <- result_14;
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (_LEN %% 8)) /\ ((_LEN %% 8) <= 18446744073709551615)))]);
      trace___dumpstate_avx2x4 <-
      (trace___dumpstate_avx2x4 ++
      [(Assert,
       ((0 <= (offset + (_LEN %% 8))) /\
       ((offset + (_LEN %% 8)) <= 18446744073709551615)))]);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, b_buf0, buf1, b_buf1, buf2, b_buf2, buf3, b_buf3, offset,
           trace___dumpstate_avx2x4);
  }
  proc __squeeze_avx2x4 (st:BArray800.t, b_st:BArray800.t, buf0:A.t,
                         b_buf0:A.t, buf1:A.t,
                         b_buf1:A.t, buf2:A.t,
                         b_buf2:A.t, buf3:A.t,
                         b_buf3:A.t, _RATE8:int) : BArray800.t *
                                                           BArray800.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           A.t *
                                                           trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    var param:BArray800.t;
    var result:BArray800.t;
    var param_0:BArray800.t;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var param_4:A.t;
    var param_5:A.t;
    var param_6:A.t;
    var result_0:int;
    var result_1:A.t;
    var result_2:A.t;
    var result_3:A.t;
    var result_4:A.t;
    var param_7:BArray800.t;
    var result_5:BArray800.t;
    var param_8:BArray800.t;
    var param_9:int;
    var param_10:int;
    var param_11:A.t;
    var param_12:A.t;
    var param_13:A.t;
    var param_14:A.t;
    var result_6:int;
    var result_7:A.t;
    var result_8:A.t;
    var result_9:A.t;
    var result_10:A.t;
    var b_result:A.t;
    var b_result_0:A.t;
    var b_result_1:A.t;
    var b_result_2:A.t;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_result_3:BArray800.t;
    var b_result_4:A.t;
    var b_result_5:A.t;
    var b_result_6:A.t;
    var b_result_7:A.t;
    var b_param_3:A.t;
    var b_param_4:A.t;
    var b_param_5:A.t;
    var b_param_6:A.t;
    var b_result_8:BArray800.t;
    var trace___squeeze_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
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
    param <- witness;
    param_0 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_7 <- witness;
    result_8 <- witness;
    result_9 <- witness;
    result_10 <- witness;
    trace___squeeze_avx2x4 <- [];
    trace___squeeze_avx2x4 <-
    (trace___squeeze_avx2x4 ++
    [(Assert,
     (((0 < _RATE8) /\ (_RATE8 < 200)) /\ (BArray800.is_init b_st 0 800)))]);
    offset <- 0;
    _LEN <- _ASIZE;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    if ((0 < iTERS)) {
      i <- 0;
      trace___squeeze_avx2x4 <-
      (trace___squeeze_avx2x4 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param <- st;
        (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param,
        (BArray800.init_arr (W8.of_int 255)));
        result <- aux;
        b_result_8 <- aux_0;
        trace___squeeze_avx2x4 <- (trace___squeeze_avx2x4 ++ tmp__trace);
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert, (BArray800.is_init b_result_8 0 800))]);
        st <- result;
        b_param_6 <- b_buf0;
        param_6 <- buf0;
        b_param_5 <- b_buf1;
        param_5 <- buf1;
        b_param_4 <- b_buf2;
        param_4 <- buf2;
        b_param_3 <- b_buf3;
        param_3 <- buf3;
        param_2 <- offset;
        param_1 <- _RATE8;
        param_0 <- st;
        (result_4, b_result_7, result_3, b_result_6, result_2, b_result_5,
        result_1, b_result_4, result_0, tmp__trace) <@ __dumpstate_avx2x4 (
        param_6, b_param_6, param_5, b_param_5, param_4, b_param_4, param_3,
        b_param_3, param_2, param_1, param_0,
        (BArray800.init_arr (W8.of_int 255)));
        trace___squeeze_avx2x4 <- (trace___squeeze_avx2x4 ++ tmp__trace);
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert,
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (result_0 = (param_2 + param_1)))))]);
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert,
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         ((((A.is_init b_result_7 0 (param_2 + param_1)) /\
           (A.is_init b_result_6 0 (param_2 + param_1))) /\
          (A.is_init b_result_5 0 (param_2 + param_1))) /\
         (A.is_init b_result_4 0 (param_2 + param_1))))))))))))]);
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
        b_buf0 <- b_result_7;
        buf0 <- result_4;
        b_buf1 <- b_result_6;
        buf1 <- result_3;
        b_buf2 <- b_result_5;
        buf2 <- result_2;
        b_buf3 <- b_result_4;
        buf3 <- result_1;
        offset <- result_0;
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___squeeze_avx2x4 <-
        (trace___squeeze_avx2x4 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
    } else {
      
    }
    if ((0 < lO)) {
      param_7 <- st;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_7,
      (BArray800.init_arr (W8.of_int 255)));
      result_5 <- aux;
      b_result_3 <- aux_0;
      trace___squeeze_avx2x4 <- (trace___squeeze_avx2x4 ++ tmp__trace);
      trace___squeeze_avx2x4 <-
      (trace___squeeze_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_3 0 800))]);
      st <- result_5;
      b_param_2 <- b_buf0;
      param_14 <- buf0;
      b_param_1 <- b_buf1;
      param_13 <- buf1;
      b_param_0 <- b_buf2;
      param_12 <- buf2;
      b_param <- b_buf3;
      param_11 <- buf3;
      param_10 <- offset;
      param_9 <- lO;
      param_8 <- st;
      (result_10, b_result_2, result_9, b_result_1, result_8, b_result_0,
      result_7, b_result, result_6, tmp__trace) <@ __dumpstate_avx2x4 (
      param_14, b_param_2, param_13, b_param_1, param_12, b_param_0,
      param_11, b_param, param_10, param_9, param_8,
      (BArray800.init_arr (W8.of_int 255)));
      trace___squeeze_avx2x4 <- (trace___squeeze_avx2x4 ++ tmp__trace);
      trace___squeeze_avx2x4 <-
      (trace___squeeze_avx2x4 ++
      [(Assert,
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       (result_6 = (param_10 + param_9)))))]);
      trace___squeeze_avx2x4 <-
      (trace___squeeze_avx2x4 ++
      [(Assert,
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       ((((A.is_init b_result_2 0 (param_10 + param_9)) /\
         (A.is_init b_result_1 0 (param_10 + param_9))) /\
        (A.is_init b_result_0 0 (param_10 + param_9))) /\
       (A.is_init b_result 0 (param_10 + param_9))))))))))))]);
      trace___squeeze_avx2x4 <-
      (trace___squeeze_avx2x4 ++
      [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
      b_buf0 <- b_result_2;
      buf0 <- result_10;
      b_buf1 <- b_result_1;
      buf1 <- result_9;
      b_buf2 <- b_result_0;
      buf2 <- result_8;
      b_buf3 <- b_result;
      buf3 <- result_7;
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, buf0, b_buf0, buf1, b_buf1, buf2, b_buf2, buf3, 
           b_buf3, trace___squeeze_avx2x4);
  }
}.

(* safety specifications *)

op __addstate_bcast_avx2x4_spec _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB =
   hoare [MM.__addstate_bcast_avx2x4 :
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
    ((((0 <= _aT) /\ (((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)) <= 200)) /\
     (0 <= __TRAILB)) /\
    (__TRAILB < 256)))))))) /\
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
   (BArray800.is_init _b_st 0 (25 * 32)))))))))))))))))))))) ==>
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
    (((BArray800.is_init res.`2 0 (25 * 32)) /\
     (res.`3 = ((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)))) /\
    (res.`4 = (_offset + __LEN))))))))))))))))))) /\
   (valid res.`5))].

op __absorb_bcast_avx2x4_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8 =
   hoare [MM.__absorb_bcast_avx2x4 :
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
   ((((((((0 <= _aT) /\ (_aT < __RATE8)) /\ (0 <= __TRAILB)) /\
       (__TRAILB < 256)) /\
      (0 < __RATE8)) /\
     (__RATE8 < 200)) /\
    (A.is_init _b_buf 0 _ASIZE)) /\
   (BArray800.is_init _b_st 0 (25 * 32))))))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    ((BArray800.is_init res.`2 0 (25 * 32)) /\
    (res.`3 = (((_aT + _ASIZE) %% __RATE8) + ((__TRAILB <> 0) ? 1 : 0)))))))) /\
   (valid res.`4))].

op __addstate_avx2x4_spec _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _offset __LEN __TRAILB =
   hoare [MM.__addstate_avx2x4 :
   (((__TRAILB = _TRAILB) /\
    ((__LEN = _LEN) /\
    ((_offset = offset) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st)))))))))))))) /\
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
   ((((((((0 <= _offset) /\ (0 <= __LEN)) /\ ((_offset + __LEN) <= _ASIZE)) /\
       (BArray800.is_init _b_st 0 (25 * 32))) /\
      (A.is_init _b_buf0 _offset __LEN)) /\
     (A.is_init _b_buf1 _offset __LEN)) /\
    (A.is_init _b_buf2 _offset __LEN)) /\
   (A.is_init _b_buf3 _offset __LEN))))))))))))))))))))))))))) ==>
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
    (((BArray800.is_init res.`2 0 (25 * 32)) /\
     (res.`3 = ((_aT + __LEN) + ((__TRAILB <> 0) ? 1 : 0)))) /\
    (res.`4 = (_offset + __LEN))))))))))))))))))) /\
   (valid res.`5))].

op __absorb_avx2x4_spec _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 __TRAILB __RATE8 =
   hoare [MM.__absorb_avx2x4 :
   (((__RATE8 = _RATE8) /\
    ((__TRAILB = _TRAILB) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st))))))))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((((((((((0 < __RATE8) /\ (__RATE8 < 200)) /\ (0 <= __TRAILB)) /\
          (__TRAILB < 256)) /\
         (0 <= _aT)) /\
        (_aT < __RATE8)) /\
       (A.is_init _b_buf0 0 _ASIZE)) /\
      (A.is_init _b_buf1 0 _ASIZE)) /\
     (A.is_init _b_buf2 0 _ASIZE)) /\
    (A.is_init _b_buf3 0 _ASIZE)) /\
   (BArray800.is_init _b_st 0 (25 * 32))))))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    ((BArray800.is_init res.`2 0 (25 * 32)) /\
    (res.`3 = (((_aT + _ASIZE) %% __RATE8) + ((__TRAILB <> 0) ? 1 : 0)))))))) /\
   (valid res.`4))].

op __dumpstate_avx2x4_spec _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _offset __LEN _st _b_st =
   hoare [MM.__dumpstate_avx2x4 :
   (((_b_st = b_st) /\
    ((_st = st) /\
    ((__LEN = _LEN) /\
    ((_offset = offset) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\ ((_b_buf0 = b_buf0) /\ (_buf0 = buf0)))))))))))) /\
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
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
   (((0 <= (_offset + __LEN)) /\ ((_offset + __LEN) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((((0 <= _offset) /\ (0 <= __LEN)) /\ ((_offset + __LEN) <= _ASIZE)) /\
        (BArray800.is_init _b_st 0 (25 * 32))) /\
       (__LEN <= 200)) /\
      (A.is_init _b_buf0 0 _offset)) /\
     (A.is_init _b_buf1 0 _offset)) /\
    (A.is_init _b_buf2 0 _offset)) /\
   (A.is_init _b_buf3 0 _offset))))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`9) /\ (res.`9 <= 18446744073709551615)))) /\
    ((true /\
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
     (true /\
     (true /\
     (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
     (((0 <= (_offset + __LEN)) /\
      ((_offset + __LEN) <= 18446744073709551615)) /\
     (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
     (((0 <= (_offset + __LEN)) /\
      ((_offset + __LEN) <= 18446744073709551615)) /\
     (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
     (((0 <= (_offset + __LEN)) /\
      ((_offset + __LEN) <= 18446744073709551615)) /\
     (((0 <= __LEN) /\ (__LEN <= 18446744073709551615)) /\
     (((0 <= (_offset + __LEN)) /\
      ((_offset + __LEN) <= 18446744073709551615)) /\
     ((((A.is_init res.`2 0 (_offset + __LEN)) /\
       (A.is_init res.`4 0 (_offset + __LEN))) /\
      (A.is_init res.`6 0 (_offset + __LEN))) /\
     (A.is_init res.`8 0 (_offset + __LEN))))))))))))))))))))))))))))))))))))))))))) /\
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
    (res.`9 = (_offset + __LEN))))))))))))))) /\
   (valid res.`10))].

op __squeeze_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 __RATE8 =
   hoare [MM.__squeeze_avx2x4 :
   (((__RATE8 = _RATE8) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_b_st = b_st) /\ (_st = st))))))))))) /\
   (true /\
   (true /\
   (((0 < __RATE8) /\ (__RATE8 < 200)) /\
   (BArray800.is_init _b_st 0 (25 * 32)))))) ==>
   ((((((A.is_init res.`4 0 _ASIZE) /\ (A.is_init res.`6 0 _ASIZE)) /\
      (A.is_init res.`8 0 _ASIZE)) /\
     (A.is_init res.`10 0 _ASIZE)) /\
    (BArray800.is_init res.`2 0 (25 * 32))) /\
   (valid res.`11))].

lemma __addstate_bcast_avx2x4_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (__addstate_bcast_avx2x4_spec _st _b_st _aT _buf _b_buf _offset 
      __LEN __TRAILB).
proof.
rewrite /__addstate_bcast_avx2x4_spec; proc.
sp 11.
if.
+ (* then *)
  seq 27 : ((valid trace___addstate_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
  + (* cut *)
    wp; ecall (RW.__a_ilen_read_bcast_upto8_at_proof param_5 b_param_0 param_4 param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace___addstate_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8)) /\ !((at < (32 * ((aT %/ 8) + (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  sp 2.
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_bcast_upto8_at_proof param_12 b_param param_11 param_10 param_9 param_8 param_7 param_6).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 7 : ((valid trace___addstate_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8)) /\ !((at < (32 * ((aT %/ 8) + (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_bcast_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\ at %% 32 = 0 /\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  sp 2.
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_bcast_upto8_at_proof param_12 b_param param_11 param_10 param_9 param_8 param_7 param_6).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma __absorb_bcast_avx2x4_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (__absorb_bcast_avx2x4_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
rewrite /__absorb_bcast_avx2x4_spec; proc.
sp 25.
if.
+ (* then *)
  seq 28 : ((valid trace___absorb_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_5 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_bcast_avx2x4_proof param_4 ((BArray800.init_arr (W8.of_int 255))) param_3 param_2 ((A.init_arr (W8.of_int 255))) param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace___absorb_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2x4_proof param_12 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_bcast_avx2x4_proof param_11 ((BArray800.init_arr (W8.of_int 255))) param_10 param_9 ((A.init_arr (W8.of_int 255))) param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 17 : ((valid trace___absorb_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_bcast_avx2x4_proof param_18 ((BArray800.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_20 ((BArray800.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 16 : ((valid trace___absorb_bcast_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_bcast_avx2x4_proof param_18 ((BArray800.init_arr (W8.of_int 255))) param_17 param_16 ((A.init_arr (W8.of_int 255))) param_15 param_14 param_13).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_20 ((BArray800.init_arr (W8.of_int 255))) param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma __addstate_avx2x4_proof _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _offset __LEN __TRAILB :
      (__addstate_avx2x4_spec _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 
      _buf2 _b_buf2 _buf3 _b_buf3 _offset __LEN __TRAILB).
proof.
rewrite /__addstate_avx2x4_spec; proc.
sp 23.
if.
+ (* then *)
  seq 71 : ((valid trace___addstate_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf0 _offset __LEN /\ A.is_init b_buf1 _offset __LEN /\ A.is_init b_buf2 _offset __LEN /\ A.is_init b_buf3 _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
  + (* cut *)
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_26 b_param_3 param_25 param_24 param_23 param_22 param_21 param_20).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_19 b_param_4 param_18 param_17 param_16 param_15 param_14 param_13).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_12 b_param_5 param_11 param_10 param_9 param_8 param_7 param_6).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_5 b_param_6 param_4 param_3 param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace___addstate_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf0 _offset __LEN /\ A.is_init b_buf1 _offset __LEN /\ A.is_init b_buf2 _offset __LEN /\ A.is_init b_buf3 _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))) /\ !((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf0 _offset __LEN /\ A.is_init b_buf1 _offset __LEN /\ A.is_init b_buf2 _offset __LEN /\ A.is_init b_buf3 _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  sp 2.
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_54 b_param param_53 param_52 param_51 param_50 param_49 param_48).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_47 b_param_0 param_46 param_45 param_44 param_43 param_42 param_41).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_40 b_param_1 param_39 param_38 param_37 param_36 param_35 param_34).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_33 b_param_2 param_32 param_31 param_30 param_29 param_28 param_27).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 7 : ((valid trace___addstate_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf0 _offset __LEN /\ A.is_init b_buf1 _offset __LEN /\ A.is_init b_buf2 _offset __LEN /\ A.is_init b_buf3 _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))) /\ !((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8)))))).
  + (* loop *)
    wp; while ((valid trace___addstate_avx2x4 /\ 0 <= _LEN <= __LEN /\ 0 <= _TRAILB < 256 /\ 0 <= aT /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ A.is_init b_buf0 _offset __LEN /\ A.is_init b_buf1 _offset __LEN /\ A.is_init b_buf2 _offset __LEN /\ A.is_init b_buf3 _offset __LEN /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) = _aT + __LEN + (if __TRAILB <> 0 then 1 else 0) /\ aT + _LEN + (if _TRAILB <> 0 then 1 else 0) <= 200 /\ (aT %% 8 = 0 \/ (_LEN = 0 /\ _TRAILB = 0)) /\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\ at %% 4 = 0 /\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8)))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  sp 2.
  if.
  + (* then *)
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_54 b_param param_53 param_52 param_51 param_50 param_49 param_48).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_47 b_param_0 param_46 param_45 param_44 param_43 param_42 param_41).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_40 b_param_1 param_39 param_38 param_37 param_36 param_35 param_34).
    wp; ecall (RW.__a_ilen_read_upto8_at_proof param_33 b_param_2 param_32 param_31 param_30 param_29 param_28 param_27).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma __absorb_avx2x4_proof _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 __TRAILB __RATE8 :
      (__absorb_avx2x4_spec _st _b_st _aT _buf0 _b_buf0 _buf1 _b_buf1 
      _buf2 _b_buf2 _buf3 _b_buf3 __TRAILB __RATE8).
proof.
rewrite /__absorb_avx2x4_spec; proc.
sp 34.
if.
+ (* then *)
  seq 31 : ((valid trace___absorb_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_8 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (__addstate_avx2x4_proof param_7 ((BArray800.init_arr (W8.of_int 255))) param_6 param_5 ((A.init_arr (W8.of_int 255))) param_4 ((A.init_arr (W8.of_int 255))) param_3 ((A.init_arr (W8.of_int 255))) param_2 ((A.init_arr (W8.of_int 255))) param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace___absorb_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___absorb_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ 0 <= _aT < __RATE8 /\ __RATE8 <= _aT + _ASIZE /\ aT = 0 /\ _LEN = _ASIZE - (__RATE8 - _aT) /\ iTERS = _LEN %/ _RATE8 /\ 0 <= i <= iTERS /\ offset = (__RATE8 - _aT) + _RATE8 * i)).
    + (* loop body *)
      wp; ecall (_keccakf1600_avx2x4_proof param_18 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (__addstate_avx2x4_proof param_17 ((BArray800.init_arr (W8.of_int 255))) param_16 param_15 ((A.init_arr (W8.of_int 255))) param_14 ((A.init_arr (W8.of_int 255))) param_13 ((A.init_arr (W8.of_int 255))) param_12 ((A.init_arr (W8.of_int 255))) param_11 param_10 param_9).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 20 : ((valid trace___absorb_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_avx2x4_proof param_27 ((BArray800.init_arr (W8.of_int 255))) param_26 param_25 ((A.init_arr (W8.of_int 255))) param_24 ((A.init_arr (W8.of_int 255))) param_23 ((A.init_arr (W8.of_int 255))) param_22 ((A.init_arr (W8.of_int 255))) param_21 param_20 param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_29 ((BArray800.init_arr (W8.of_int 255))) param_28).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 19 : ((valid trace___absorb_avx2x4 /\ _RATE8 = __RATE8 /\ _TRAILB = __TRAILB /\ 0 < __RATE8 < 200 /\ 0 <= __TRAILB < 256 /\ aT = (_aT + _ASIZE) %% __RATE8 + (if __TRAILB <> 0 then 1 else 0))).
  + (* cut *)
    wp; ecall (__addstate_avx2x4_proof param_27 ((BArray800.init_arr (W8.of_int 255))) param_26 param_25 ((A.init_arr (W8.of_int 255))) param_24 ((A.init_arr (W8.of_int 255))) param_23 ((A.init_arr (W8.of_int 255))) param_22 ((A.init_arr (W8.of_int 255))) param_21 param_20 param_19).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (__addratebit_avx2x4_proof param_29 ((BArray800.init_arr (W8.of_int 255))) param_28).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma __dumpstate_avx2x4_proof _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _offset __LEN _st _b_st :
      (__dumpstate_avx2x4_spec _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2
      _buf3 _b_buf3 _offset __LEN _st _b_st).
proof.
rewrite /__dumpstate_avx2x4_spec; proc.
seq 22 : ((valid trace___dumpstate_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ 0 <= i <= 32 * (_LEN %/ 32) /\ i %% 32 = 0 /\ offset = _offset + i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset) /\ !((i < (32 * (_LEN %/ 32))))).
+ (* loop *)
  wp; while ((valid trace___dumpstate_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ 0 <= i <= 32 * (_LEN %/ 32) /\ i %% 32 = 0 /\ offset = _offset + i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset)).
  + (* loop body *)
    wp; ecall (__4u64x4_u256x4_proof param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
seq 2 : ((valid trace___dumpstate_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\ i %% 8 = 0 /\ offset = _offset + i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset) /\ !((i < (8 * (_LEN %/ 8))))).
+ (* loop *)
  wp; while ((valid trace___dumpstate_avx2x4 /\ _LEN = __LEN /\ 0 <= __LEN <= 200 /\ 0 <= _offset /\ _offset + __LEN <= _ASIZE /\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\ i %% 8 = 0 /\ offset = _offset + i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset)).
  + (* loop body *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
if.
+ (* then *)
  wp; ecall (RW.__a_ilen_write_upto8_proof param_22 b_param param_21 param_20 param_19 param_18).
  wp; ecall (RW.__a_ilen_write_upto8_proof param_17 b_param_0 param_16 param_15 param_14 param_13).
  wp; ecall (RW.__a_ilen_write_upto8_proof param_12 b_param_1 param_11 param_10 param_9 param_8).
  wp; ecall (RW.__a_ilen_write_upto8_proof param_7 b_param_2 param_6 param_5 param_4 param_3).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma __squeeze_avx2x4_proof _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 __RATE8 :
      (__squeeze_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2
      _b_buf2 _buf3 _b_buf3 __RATE8).
proof.
rewrite /__squeeze_avx2x4_spec; proc.
sp 46.
if.
+ (* then *)
  seq 3 : ((valid trace___squeeze_avx2x4 /\ _LEN = _ASIZE /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ offset = _RATE8 * i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset) /\ !((i < iTERS))).
  + (* loop *)
    wp; while ((valid trace___squeeze_avx2x4 /\ _LEN = _ASIZE /\ _RATE8 = __RATE8 /\ 0 < __RATE8 < 200 /\ iTERS = _LEN %/ _RATE8 /\ lO = _LEN %% _RATE8 /\ 0 <= i <= iTERS /\ offset = _RATE8 * i /\ A.is_init b_buf0 0 offset /\ A.is_init b_buf1 0 offset /\ A.is_init b_buf2 0 offset /\ A.is_init b_buf3 0 offset)).
    + (* loop body *)
      wp; ecall (__dumpstate_avx2x4_proof param_6 b_param_6 param_5 b_param_5 param_4 b_param_4 param_3 b_param_3 param_2 param_1 param_0 ((BArray800.init_arr (W8.of_int 255)))).
      wp; ecall (_keccakf1600_avx2x4_proof param ((BArray800.init_arr (W8.of_int 255)))).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (__dumpstate_avx2x4_proof param_14 b_param_2 param_13 b_param_1 param_12 b_param_0 param_11 b_param param_10 param_9 param_8 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2x4_proof param_7 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  if.
  + (* then *)
    wp; ecall (__dumpstate_avx2x4_proof param_14 b_param_2 param_13 b_param_1 param_12 b_param_0 param_11 b_param param_10 param_9 param_8 ((BArray800.init_arr (W8.of_int 255)))).
    wp; ecall (_keccakf1600_avx2x4_proof param_7 ((BArray800.init_arr (W8.of_int 255)))).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

end KeccakArrayAvx2x4Safety.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory KeccakUpdstateAvx2x4Safety.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

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
   ../extracted/Keccak1600_updstate_avx2x4_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc _add_bcast_updstate_avx2x4 (st:BArray800.t, b_st:BArray800.t, at:int,
                                   buf:A.t, b_buf:A.t,
                                   off:int, upto:int) : BArray800.t *
                                                        BArray800.t * int *
                                                        int * trace = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t128:W128.t;
    var t256:W256.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var param:int;
    var param_0:int;
    var param_1:A.t;
    var result:W64.t;
    var result_0:int;
    var param_2:int;
    var param_3:int;
    var param_4:A.t;
    var result_1:W64.t;
    var result_2:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var trace__add_bcast_updstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    param_1 <- witness;
    param_4 <- witness;
    trace__add_bcast_updstate_avx2x4 <- [];
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (off + (upto - at))) /\
      ((off + (upto - at)) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((((((BArray800.is_init b_st 0 800) /\ (0 <= at)) /\ (at <= upto)) /\
        (upto <= 200)) /\
       (0 <= off)) /\
      ((off + (upto - at)) <= _ASIZE)) /\
     (A.is_init b_buf off (upto - at)))))))]);
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - at)) /\ ((len - at) <= 18446744073709551615)))]);
      len <- (len - at);
      at <- (at `|>>` 3);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (at `<<` 3)) /\ ((at `<<` 3) <= 18446744073709551615)))]);
      at <- (at `<<` 3);
      b_param_0 <- b_buf;
      param_1 <- buf;
      param_0 <- off;
      param <- len;
      (result_0, result, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_1,
      b_param_0, param_0, param);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++ tmp__trace);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) /\
        (((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_0 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))) /\
        ((param_0 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) <=
        18446744073709551615)) /\
       (result_0 =
       (param_0 +
       ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))))))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      off2 <- result_0;
      t64 <- result;
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (len + (W64.to_uint at8))) /\
       ((len + (W64.to_uint at8)) <= 18446744073709551615)))]);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      t128 <- (VMOV_64 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      t256 <- (t256 `^` (BArray800.get256d st (4 * at)));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      st <- (BArray800.set256d st (4 * at) t256);
      if ((8 <= len)) {
        trace__add_bcast_updstate_avx2x4 <-
        (trace__add_bcast_updstate_avx2x4 ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__add_bcast_updstate_avx2x4 <-
        (trace__add_bcast_updstate_avx2x4 ++
        [(Assert,
         ((0 <= (off - (W64.to_uint at8))) /\
         ((off - (W64.to_uint at8)) <= 18446744073709551615)))]);
        off <- (off - (W64.to_uint at8));
        trace__add_bcast_updstate_avx2x4 <-
        (trace__add_bcast_updstate_avx2x4 ++
        [(Assert, ((0 <= (at + 8)) /\ ((at + 8) <= 18446744073709551615)))]);
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    trace__add_bcast_updstate_avx2x4 <-
    (trace__add_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
    newat <- (newat + 8);
    while ((newat <= upto)) {
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, (A.is_init b_buf off 8))]);
      t256 <- (VPBROADCAST_4u64 (A.get64d buf off));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      t256 <- (t256 `^` (BArray800.get256d st (4 * at)));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      st <- (BArray800.set256d st (4 * at) t256);
      at <- newat;
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
      off <- (off + 8);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      b_param <- b_buf;
      param_4 <- buf;
      param_3 <- off;
      param_2 <- (W64.to_uint upto8);
      (result_2, result_1, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_4,
      b_param, param_3, param_2);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++ tmp__trace);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) /\
        (((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_3 +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)))) /\
        ((param_3 +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) <=
        18446744073709551615)) /\
       (result_2 =
       (param_3 +
       ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? param_2 : 8)))))))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      off <- result_2;
      t64 <- result_1;
      t128 <- (VMOV_64 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      t256 <- (t256 `^` (BArray800.get256d st (4 * at)));
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_bcast_updstate_avx2x4 <-
      (trace__add_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 32) <= 800)))]);
      st <- (BArray800.set256d st (4 * at) t256);
    } else {
      
    }
    at <- upto;
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, at, off, trace__add_bcast_updstate_avx2x4);
  }
  proc _absorb_bcast_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                                      buf:A.t, b_buf:A.t,
                                      len:int) : BArray808.t * BArray808.t *
                                                 trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
    var aux_1:int;
    var aux_2:int;
    var ststatus:W64.t;
    var stk:BArray800.t;
    var r8:int;
    var at:int;
    var off:int;
    var param:W64.t;
    var result:int;
    var result_0:int;
    var result_1:W64.t;
    var param_0:int;
    var param_1:int;
    var param_2:A.t;
    var param_3:int;
    var param_4:BArray800.t;
    var result_2:int;
    var result_3:int;
    var result_4:BArray800.t;
    var param_5:BArray800.t;
    var result_5:BArray800.t;
    var param_6:int;
    var param_7:int;
    var param_8:A.t;
    var param_9:int;
    var param_10:BArray800.t;
    var result_6:int;
    var result_7:int;
    var result_8:BArray800.t;
    var b_stk:BArray800.t;
    var b_result:BArray800.t;
    var b_param:A.t;
    var b_param_0:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_param_1:A.t;
    var b_param_2:BArray800.t;
    var trace__absorb_bcast_updstate_avx2x4:trace;
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
    trace__absorb_bcast_updstate_avx2x4 <- [];
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert,
     ((((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
     (A.is_init b_buf 0 len)))]);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    ststatus <- (BArray808.get64 st 100);
    param <- ststatus;
    (result_1, result_0, result, tmp__trace) <@ M._ststatus_data_avx2x4 (
    param);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++ tmp__trace);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert,
     (((((0 < result_0) /\ (result_0 <= 200)) /\ ((result_0 %% 8) = 0)) /\
      (0 <= result)) /\
     (result < result_0)))]);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
    r8 <- result_0;
    at <- result;
    b_stk <- (SBArray808_800.get_sub256 b_st 0);
    stk <- (SBArray808_800.get_sub256 st 0);
    off <- 0;
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
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
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_bcast_updstate_avx2x4 (
      param_4, b_param_2, param_3, param_2, b_param_1, param_1, param_0);
      result_4 <- aux;
      b_result_1 <- aux_0;
      result_3 <- aux_1;
      result_2 <- aux_2;
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++ tmp__trace);
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++
      [(Assert,
       (((0 <= (param_0 - param_3)) /\
        ((param_0 - param_3) <= 18446744073709551615)) /\
       (((0 <= (param_1 + (param_0 - param_3))) /\
        ((param_1 + (param_0 - param_3)) <= 18446744073709551615)) /\
       (((BArray800.is_init b_result_1 0 800) /\ (result_3 = param_0)) /\
       (result_2 = (param_1 + (param_0 - param_3)))))))]);
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      stk <- result_4;
      off <- result_2;
      param_5 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_5,
      (BArray800.init_arr (W8.of_int 255)));
      result_5 <- aux;
      b_result_0 <- aux_0;
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++ tmp__trace);
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_0 0 800))]);
      b_stk <- (BArray800.init_arr (W8.of_int 255));
      stk <- result_5;
      trace__absorb_bcast_updstate_avx2x4 <-
      (trace__absorb_bcast_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - r8)) /\ ((len - r8) <= 18446744073709551615)))]);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    b_param_0 <- b_stk;
    param_10 <- stk;
    param_9 <- at;
    b_param <- b_buf;
    param_8 <- buf;
    param_7 <- off;
    param_6 <- len;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_bcast_updstate_avx2x4 (
    param_10, b_param_0, param_9, param_8, b_param, param_7, param_6);
    result_8 <- aux;
    b_result <- aux_0;
    result_7 <- aux_1;
    result_6 <- aux_2;
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++ tmp__trace);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (param_6 - param_9)) /\
      ((param_6 - param_9) <= 18446744073709551615)) /\
     (((0 <= (param_7 + (param_6 - param_9))) /\
      ((param_7 + (param_6 - param_9)) <= 18446744073709551615)) /\
     (((BArray800.is_init b_result 0 800) /\ (result_7 = param_6)) /\
     (result_6 = (param_7 + (param_6 - param_9)))))))]);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
    stk <- result_8;
    at <- result_7;
    b_st <-
    (SBArray808_800.set_sub256 b_st 0 (BArray800.init_arr (W8.of_int 255)));
    st <- (SBArray808_800.set_sub256 st 0 stk);
    trace__absorb_bcast_updstate_avx2x4 <-
    (trace__absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    b_st <- (BArray808.set8d b_st 800 (W8.of_int 255));
    st <- (BArray808.set8d st 800 (truncateu8 (W64.of_int at)));
    return (st, b_st, trace__absorb_bcast_updstate_avx2x4);
  }
  proc _add_updstate_avx2x4 (st:BArray800.t, b_st:BArray800.t, at:int,
                             buf0:A.t, b_buf0:A.t,
                             buf1:A.t, b_buf1:A.t,
                             buf2:A.t, b_buf2:A.t,
                             buf3:A.t, b_buf3:A.t, off:int,
                             upto:int) : BArray800.t * BArray800.t * int *
                                         int * trace = {
    var at8:W64.t;
    var shval:W8.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var param:int;
    var param_0:int;
    var param_1:A.t;
    var result:W64.t;
    var result_0:int;
    var param_2:int;
    var param_3:int;
    var param_4:A.t;
    var result_1:W64.t;
    var result_2:int;
    var param_5:int;
    var param_6:int;
    var param_7:A.t;
    var result_3:W64.t;
    var result_4:int;
    var param_8:int;
    var param_9:int;
    var param_10:A.t;
    var result_5:W64.t;
    var result_6:int;
    var param_11:int;
    var param_12:int;
    var param_13:A.t;
    var result_7:W64.t;
    var result_8:int;
    var param_14:int;
    var param_15:int;
    var param_16:A.t;
    var result_9:W64.t;
    var result_10:int;
    var param_17:int;
    var param_18:int;
    var param_19:A.t;
    var result_11:W64.t;
    var result_12:int;
    var param_20:int;
    var param_21:int;
    var param_22:A.t;
    var result_13:W64.t;
    var result_14:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_param_3:A.t;
    var b_param_4:A.t;
    var b_param_5:A.t;
    var b_param_6:A.t;
    var trace__add_updstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    param_1 <- witness;
    param_4 <- witness;
    param_7 <- witness;
    param_10 <- witness;
    param_13 <- witness;
    param_16 <- witness;
    param_19 <- witness;
    param_22 <- witness;
    trace__add_updstate_avx2x4 <- [];
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (off + (upto - at))) /\
      ((off + (upto - at)) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     ((((((((((BArray800.is_init b_st 0 800) /\ (0 <= at)) /\ (at <= upto)) /\
           (upto <= 200)) /\
          (0 <= off)) /\
         ((off + (upto - at)) <= _ASIZE)) /\
        (A.is_init b_buf0 off (upto - at))) /\
       (A.is_init b_buf1 off (upto - at))) /\
      (A.is_init b_buf2 off (upto - at))) /\
     (A.is_init b_buf3 off (upto - at))))))))))]);
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - at)) /\ ((len - at) <= 18446744073709551615)))]);
      len <- (len - at);
      at <- (at `|>>` 3);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (at `<<` 3)) /\ ((at `<<` 3) <= 18446744073709551615)))]);
      at <- (at `<<` 3);
      shval <- (truncateu8 at8);
      shval <- (shval `<<` (W8.of_int 3));
      b_param_6 <- b_buf0;
      param_1 <- buf0;
      param_0 <- off;
      param <- len;
      (result_0, result, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_1,
      b_param_6, param_0, param);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) /\
        (((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_0 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))) /\
        ((param_0 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) <=
        18446744073709551615)) /\
       (result_0 =
       (param_0 +
       ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      t64 <- result;
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st (4 * at) ((BArray800.get64d st (4 * at)) `^` t64));
      b_param_5 <- b_buf1;
      param_4 <- buf1;
      param_3 <- off;
      param_2 <- len;
      (result_2, result_1, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_4,
      b_param_5, param_3, param_2);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) /\
        (((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_3 +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8)))) /\
        ((param_3 +
         ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? 
                                                    param_2 : 8))) <=
        18446744073709551615)) /\
       (result_2 =
       (param_3 +
       ((((param_2 < 8) ? param_2 : 8) < 0) ? 0 : ((param_2 < 8) ? param_2 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      t64 <- result_1;
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 8)
      ((BArray800.get64d st ((4 * at) + 8)) `^` t64));
      b_param_4 <- b_buf2;
      param_7 <- buf2;
      param_6 <- off;
      param_5 <- len;
      (result_4, result_3, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_7,
      b_param_4, param_6, param_5);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) /\
        (((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_6 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8)))) /\
        ((param_6 +
         ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? 
                                                    param_5 : 8))) <=
        18446744073709551615)) /\
       (result_4 =
       (param_6 +
       ((((param_5 < 8) ? param_5 : 8) < 0) ? 0 : ((param_5 < 8) ? param_5 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
      t64 <- result_3;
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 16)
      ((BArray800.get64d st ((4 * at) + 16)) `^` t64));
      b_param_3 <- b_buf3;
      param_10 <- buf3;
      param_9 <- off;
      param_8 <- len;
      (result_6, result_5, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_10,
      b_param_3, param_9, param_8);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_8 < 8) ? param_8 : 8) < 0) ? 0 : ((param_8 < 8) ? 
                                                    param_8 : 8))) /\
        (((((param_8 < 8) ? param_8 : 8) < 0) ? 0 : ((param_8 < 8) ? 
                                                    param_8 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_9 +
         ((((param_8 < 8) ? param_8 : 8) < 0) ? 0 : ((param_8 < 8) ? 
                                                    param_8 : 8)))) /\
        ((param_9 +
         ((((param_8 < 8) ? param_8 : 8) < 0) ? 0 : ((param_8 < 8) ? 
                                                    param_8 : 8))) <=
        18446744073709551615)) /\
       (result_6 =
       (param_9 +
       ((((param_8 < 8) ? param_8 : 8) < 0) ? 0 : ((param_8 < 8) ? param_8 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
      off2 <- result_6;
      t64 <- result_5;
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 24)
      ((BArray800.get64d st ((4 * at) + 24)) `^` t64));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (len + (W64.to_uint at8))) /\
       ((len + (W64.to_uint at8)) <= 18446744073709551615)))]);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        trace__add_updstate_avx2x4 <-
        (trace__add_updstate_avx2x4 ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__add_updstate_avx2x4 <-
        (trace__add_updstate_avx2x4 ++
        [(Assert,
         ((0 <= (off - (W64.to_uint at8))) /\
         ((off - (W64.to_uint at8)) <= 18446744073709551615)))]);
        off <- (off - (W64.to_uint at8));
        trace__add_updstate_avx2x4 <-
        (trace__add_updstate_avx2x4 ++
        [(Assert, ((0 <= (at + 8)) /\ ((at + 8) <= 18446744073709551615)))]);
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    trace__add_updstate_avx2x4 <-
    (trace__add_updstate_avx2x4 ++
    [(Assert, ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
    newat <- (newat + 8);
    while ((newat <= upto)) {
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, (A.is_init b_buf0 off 8))]);
      t64 <- (A.get64d buf0 off);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st (4 * at) ((BArray800.get64d st (4 * at)) `^` t64));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, (A.is_init b_buf1 off 8))]);
      t64 <- (A.get64d buf1 off);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 8)
      ((BArray800.get64d st ((4 * at) + 8)) `^` t64));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, (A.is_init b_buf2 off 8))]);
      t64 <- (A.get64d buf2 off);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 16)
      ((BArray800.get64d st ((4 * at) + 16)) `^` t64));
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, (A.is_init b_buf3 off 8))]);
      t64 <- (A.get64d buf3 off);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 24)
      ((BArray800.get64d st ((4 * at) + 24)) `^` t64));
      at <- newat;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
      off <- (off + 8);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      b_param_2 <- b_buf0;
      param_13 <- buf0;
      param_12 <- off;
      param_11 <- (W64.to_uint upto8);
      (result_8, result_7, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_13,
      b_param_2, param_12, param_11);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) /\
        (((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_12 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)))) /\
        ((param_12 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) <=
        18446744073709551615)) /\
       (result_8 =
       (param_12 +
       ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                    param_11 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
      t64 <- result_7;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st (4 * at) ((BArray800.get64d st (4 * at)) `^` t64));
      b_param_1 <- b_buf1;
      param_16 <- buf1;
      param_15 <- off;
      param_14 <- (W64.to_uint upto8);
      (result_10, result_9, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_16,
      b_param_1, param_15, param_14);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8))) /\
        (((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_15 +
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8)))) /\
        ((param_15 +
         ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                      param_14 : 8))) <=
        18446744073709551615)) /\
       (result_10 =
       (param_15 +
       ((((param_14 < 8) ? param_14 : 8) < 0) ? 0 : ((param_14 < 8) ? 
                                                    param_14 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
      t64 <- result_9;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 8)
      ((BArray800.get64d st ((4 * at) + 8)) `^` t64));
      b_param_0 <- b_buf2;
      param_19 <- buf2;
      param_18 <- off;
      param_17 <- (W64.to_uint upto8);
      (result_12, result_11, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_19,
      b_param_0, param_18, param_17);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_17 < 8) ? param_17 : 8) < 0) ? 0 : ((param_17 < 8) ? 
                                                      param_17 : 8))) /\
        (((((param_17 < 8) ? param_17 : 8) < 0) ? 0 : ((param_17 < 8) ? 
                                                      param_17 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_18 +
         ((((param_17 < 8) ? param_17 : 8) < 0) ? 0 : ((param_17 < 8) ? 
                                                      param_17 : 8)))) /\
        ((param_18 +
         ((((param_17 < 8) ? param_17 : 8) < 0) ? 0 : ((param_17 < 8) ? 
                                                      param_17 : 8))) <=
        18446744073709551615)) /\
       (result_12 =
       (param_18 +
       ((((param_17 < 8) ? param_17 : 8) < 0) ? 0 : ((param_17 < 8) ? 
                                                    param_17 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_12) /\ (result_12 <= 18446744073709551615)))]);
      t64 <- result_11;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 16)
      ((BArray800.get64d st ((4 * at) + 16)) `^` t64));
      b_param <- b_buf3;
      param_22 <- buf3;
      param_21 <- off;
      param_20 <- (W64.to_uint upto8);
      (result_14, result_13, tmp__trace) <@ RW.MM.__a_rlen_read_upto8 (param_22,
      b_param, param_21, param_20);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++ tmp__trace);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_20 < 8) ? param_20 : 8) < 0) ? 0 : ((param_20 < 8) ? 
                                                      param_20 : 8))) /\
        (((((param_20 < 8) ? param_20 : 8) < 0) ? 0 : ((param_20 < 8) ? 
                                                      param_20 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_21 +
         ((((param_20 < 8) ? param_20 : 8) < 0) ? 0 : ((param_20 < 8) ? 
                                                      param_20 : 8)))) /\
        ((param_21 +
         ((((param_20 < 8) ? param_20 : 8) < 0) ? 0 : ((param_20 < 8) ? 
                                                      param_20 : 8))) <=
        18446744073709551615)) /\
       (result_14 =
       (param_21 +
       ((((param_20 < 8) ? param_20 : 8) < 0) ? 0 : ((param_20 < 8) ? 
                                                    param_20 : 8)))))))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= result_14) /\ (result_14 <= 18446744073709551615)))]);
      off <- result_14;
      t64 <- result_13;
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      trace__add_updstate_avx2x4 <-
      (trace__add_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      st <-
      (BArray800.set64d st ((4 * at) + 24)
      ((BArray800.get64d st ((4 * at) + 24)) `^` t64));
    } else {
      
    }
    at <- upto;
    b_st <- (BArray800.init_arr (W8.of_int 255));
    return (st, b_st, at, off, trace__add_updstate_avx2x4);
  }
  proc _absorb_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                                buf0:A.t, b_buf0:A.t,
                                buf1:A.t, b_buf1:A.t,
                                buf2:A.t, b_buf2:A.t,
                                buf3:A.t, b_buf3:A.t, len:int) : 
  BArray808.t * BArray808.t * trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
    var aux_1:int;
    var aux_2:int;
    var ststatus:W64.t;
    var stk:BArray800.t;
    var r8:int;
    var at:int;
    var off:int;
    var param:W64.t;
    var result:int;
    var result_0:int;
    var result_1:W64.t;
    var param_0:int;
    var param_1:int;
    var param_2:A.t;
    var param_3:A.t;
    var param_4:A.t;
    var param_5:A.t;
    var param_6:int;
    var param_7:BArray800.t;
    var result_2:int;
    var result_3:int;
    var result_4:BArray800.t;
    var param_8:BArray800.t;
    var result_5:BArray800.t;
    var param_9:int;
    var param_10:int;
    var param_11:A.t;
    var param_12:A.t;
    var param_13:A.t;
    var param_14:A.t;
    var param_15:int;
    var param_16:BArray800.t;
    var result_6:int;
    var result_7:int;
    var result_8:BArray800.t;
    var b_stk:BArray800.t;
    var b_result:BArray800.t;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_param_3:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_param_4:A.t;
    var b_param_5:A.t;
    var b_param_6:A.t;
    var b_param_7:A.t;
    var b_param_8:BArray800.t;
    var trace__absorb_updstate_avx2x4:trace;
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
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_stk <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    param_16 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_8 <- witness;
    stk <- witness;
    trace__absorb_updstate_avx2x4 <- [];
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert,
     (((((((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
        (A.is_init b_buf0 0 len)) /\
       (A.is_init b_buf1 0 len)) /\
      (A.is_init b_buf2 0 len)) /\
     (A.is_init b_buf3 0 len)))]);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    ststatus <- (BArray808.get64 st 100);
    param <- ststatus;
    (result_1, result_0, result, tmp__trace) <@ M._ststatus_data_avx2x4 (
    param);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++ tmp__trace);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert,
     (((((0 < result_0) /\ (result_0 <= 200)) /\ ((result_0 %% 8) = 0)) /\
      (0 <= result)) /\
     (result < result_0)))]);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
    r8 <- result_0;
    at <- result;
    b_stk <- (SBArray808_800.get_sub256 b_st 0);
    stk <- (SBArray808_800.get_sub256 st 0);
    (* Erased call to spill *)
    off <- 0;
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= (len + at)) /\ ((len + at) <= 18446744073709551615)))]);
    len <- (len + at);
    while ((r8 <= len)) {
      (* Erased call to spill *)
      b_param_8 <- b_stk;
      param_7 <- stk;
      param_6 <- at;
      b_param_7 <- b_buf0;
      param_5 <- buf0;
      b_param_6 <- b_buf1;
      param_4 <- buf1;
      b_param_5 <- b_buf2;
      param_3 <- buf2;
      b_param_4 <- b_buf3;
      param_2 <- buf3;
      param_1 <- off;
      param_0 <- r8;
      (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_updstate_avx2x4 (
      param_7, b_param_8, param_6, param_5, b_param_7, param_4, b_param_6,
      param_3, b_param_5, param_2, b_param_4, param_1, param_0);
      result_4 <- aux;
      b_result_1 <- aux_0;
      result_3 <- aux_1;
      result_2 <- aux_2;
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++ tmp__trace);
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++
      [(Assert,
       (((0 <= (param_0 - param_6)) /\
        ((param_0 - param_6) <= 18446744073709551615)) /\
       (((0 <= (param_1 + (param_0 - param_6))) /\
        ((param_1 + (param_0 - param_6)) <= 18446744073709551615)) /\
       (((BArray800.is_init b_result_1 0 800) /\ (result_3 = param_0)) /\
       (result_2 = (param_1 + (param_0 - param_6)))))))]);
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      stk <- result_4;
      off <- result_2;
      (* Erased call to unspill *)
      param_8 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_8,
      (BArray800.init_arr (W8.of_int 255)));
      result_5 <- aux;
      b_result_0 <- aux_0;
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++ tmp__trace);
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_0 0 800))]);
      b_stk <- (BArray800.init_arr (W8.of_int 255));
      stk <- result_5;
      trace__absorb_updstate_avx2x4 <-
      (trace__absorb_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - r8)) /\ ((len - r8) <= 18446744073709551615)))]);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    b_param_3 <- b_stk;
    param_16 <- stk;
    param_15 <- at;
    b_param_2 <- b_buf0;
    param_14 <- buf0;
    b_param_1 <- b_buf1;
    param_13 <- buf1;
    b_param_0 <- b_buf2;
    param_12 <- buf2;
    b_param <- b_buf3;
    param_11 <- buf3;
    param_10 <- off;
    param_9 <- len;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ _add_updstate_avx2x4 (param_16,
    b_param_3, param_15, param_14, b_param_2, param_13, b_param_1, param_12,
    b_param_0, param_11, b_param, param_10, param_9);
    result_8 <- aux;
    b_result <- aux_0;
    result_7 <- aux_1;
    result_6 <- aux_2;
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++ tmp__trace);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (param_9 - param_15)) /\
      ((param_9 - param_15) <= 18446744073709551615)) /\
     (((0 <= (param_10 + (param_9 - param_15))) /\
      ((param_10 + (param_9 - param_15)) <= 18446744073709551615)) /\
     (((BArray800.is_init b_result 0 800) /\ (result_7 = param_9)) /\
     (result_6 = (param_10 + (param_9 - param_15)))))))]);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
    stk <- result_8;
    at <- result_7;
    (* Erased call to unspill *)
    b_st <-
    (SBArray808_800.set_sub256 b_st 0 (BArray800.init_arr (W8.of_int 255)));
    st <- (SBArray808_800.set_sub256 st 0 stk);
    trace__absorb_updstate_avx2x4 <-
    (trace__absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    b_st <- (BArray808.set8d b_st 800 (W8.of_int 255));
    st <- (BArray808.set8d st 800 (truncateu8 (W64.of_int at)));
    return (st, b_st, trace__absorb_updstate_avx2x4);
  }
  proc _dump_updstate_avx2x4 (buf0:A.t, b_buf0:A.t,
                              buf1:A.t, b_buf1:A.t,
                              buf2:A.t, b_buf2:A.t,
                              buf3:A.t, b_buf3:A.t, off:int,
                              st:BArray800.t, b_st:BArray800.t, at:int,
                              upto:int) : A.t * A.t *
                                          A.t * A.t *
                                          A.t * A.t *
                                          A.t * A.t * int *
                                          int * trace = {
    var at8:W64.t;
    var sh:W8.t;
    var t64:W64.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var param:int;
    var param_0:W64.t;
    var param_1:int;
    var param_2:A.t;
    var result:int;
    var result_0:A.t;
    var param_3:int;
    var param_4:W64.t;
    var param_5:int;
    var param_6:A.t;
    var result_1:int;
    var result_2:A.t;
    var param_7:int;
    var param_8:W64.t;
    var param_9:int;
    var param_10:A.t;
    var result_3:int;
    var result_4:A.t;
    var param_11:int;
    var param_12:W64.t;
    var param_13:int;
    var param_14:A.t;
    var result_5:int;
    var result_6:A.t;
    var param_15:int;
    var param_16:W64.t;
    var param_17:int;
    var param_18:A.t;
    var result_7:int;
    var result_8:A.t;
    var param_19:int;
    var param_20:W64.t;
    var param_21:int;
    var param_22:A.t;
    var result_9:int;
    var result_10:A.t;
    var param_23:int;
    var param_24:W64.t;
    var param_25:int;
    var param_26:A.t;
    var result_11:int;
    var result_12:A.t;
    var param_27:int;
    var param_28:W64.t;
    var param_29:int;
    var param_30:A.t;
    var result_13:int;
    var result_14:A.t;
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
    var trace__dump_updstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    param_2 <- witness;
    param_6 <- witness;
    param_10 <- witness;
    param_14 <- witness;
    param_18 <- witness;
    param_22 <- witness;
    param_26 <- witness;
    param_30 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    result_4 <- witness;
    result_6 <- witness;
    result_8 <- witness;
    result_10 <- witness;
    result_12 <- witness;
    result_14 <- witness;
    trace__dump_updstate_avx2x4 <- [];
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (upto - at)) /\ ((upto - at) <= 18446744073709551615)) /\
     (((0 <= (off + (upto - at))) /\
      ((off + (upto - at)) <= 18446744073709551615)) /\
     ((((((((((BArray800.is_init b_st 0 800) /\ (0 <= at)) /\ (at <= upto)) /\
           (upto <= 200)) /\
          (0 <= off)) /\
         ((off + (upto - at)) <= _ASIZE)) /\
        (A.is_init b_buf0 0 off)) /\
       (A.is_init b_buf1 0 off)) /\
      (A.is_init b_buf2 0 off)) /\
     (A.is_init b_buf3 0 off)))))]);
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - at)) /\ ((len - at) <= 18446744073709551615)))]);
      len <- (len - at);
      at <- (at `|>>` 3);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (at `<<` 3)) /\ ((at `<<` 3) <= 18446744073709551615)))]);
      at <- (at `<<` 3);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st (4 * at));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      b_param_6 <- b_buf0;
      param_2 <- buf0;
      param_1 <- off;
      param_0 <- t64;
      param <- len;
      (result_0, b_result_6, result, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_2, b_param_6, param_1, param_0, param);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) /\
        (((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))) /\
        ((param_1 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) /\
        (((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))) /\
        ((param_1 +
         ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_6 0
        (param_1 +
        ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8)))) /\
       (result =
       (param_1 +
       ((((param < 8) ? param : 8) < 0) ? 0 : ((param < 8) ? param : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
      b_buf0 <- b_result_6;
      buf0 <- result_0;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 8));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      b_param_5 <- b_buf1;
      param_6 <- buf1;
      param_5 <- off;
      param_4 <- t64;
      param_3 <- len;
      (result_2, b_result_5, result_1, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_6, b_param_5, param_5, param_4, param_3);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8))) /\
        (((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_5 +
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8)))) /\
        ((param_5 +
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8))) /\
        (((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_5 +
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8)))) /\
        ((param_5 +
         ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? 
                                                    param_3 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_5 0
        (param_5 +
        ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? param_3 : 8)))
        ) /\
       (result_1 =
       (param_5 +
       ((((param_3 < 8) ? param_3 : 8) < 0) ? 0 : ((param_3 < 8) ? param_3 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_1) /\ (result_1 <= 18446744073709551615)))]);
      b_buf1 <- b_result_5;
      buf1 <- result_2;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 16));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      b_param_4 <- b_buf2;
      param_10 <- buf2;
      param_9 <- off;
      param_8 <- t64;
      param_7 <- len;
      (result_4, b_result_4, result_3, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_10, b_param_4, param_9, param_8, param_7);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8))) /\
        (((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_9 +
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8)))) /\
        ((param_9 +
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8))) /\
        (((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_9 +
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8)))) /\
        ((param_9 +
         ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? 
                                                    param_7 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_4 0
        (param_9 +
        ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? param_7 : 8)))
        ) /\
       (result_3 =
       (param_9 +
       ((((param_7 < 8) ? param_7 : 8) < 0) ? 0 : ((param_7 < 8) ? param_7 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      b_buf2 <- b_result_4;
      buf2 <- result_4;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 24));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      b_param_3 <- b_buf3;
      param_14 <- buf3;
      param_13 <- off;
      param_12 <- t64;
      param_11 <- len;
      (result_6, b_result_3, result_5, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_14, b_param_3, param_13, param_12, param_11);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) /\
        (((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_13 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)))) /\
        ((param_13 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) /\
        (((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_13 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8)))) /\
        ((param_13 +
         ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                      param_11 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_3 0
        (param_13 +
        ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                     param_11 : 8)))
        ) /\
       (result_5 =
       (param_13 +
       ((((param_11 < 8) ? param_11 : 8) < 0) ? 0 : ((param_11 < 8) ? 
                                                    param_11 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_5) /\ (result_5 <= 18446744073709551615)))]);
      b_buf3 <- b_result_3;
      buf3 <- result_6;
      off2 <- result_5;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (len + (W64.to_uint at8))) /\
       ((len + (W64.to_uint at8)) <= 18446744073709551615)))]);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        trace__dump_updstate_avx2x4 <-
        (trace__dump_updstate_avx2x4 ++
        [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
        off <- (off + 8);
        trace__dump_updstate_avx2x4 <-
        (trace__dump_updstate_avx2x4 ++
        [(Assert,
         ((0 <= (off - (W64.to_uint at8))) /\
         ((off - (W64.to_uint at8)) <= 18446744073709551615)))]);
        off <- (off - (W64.to_uint at8));
        trace__dump_updstate_avx2x4 <-
        (trace__dump_updstate_avx2x4 ++
        [(Assert, ((0 <= (at + 8)) /\ ((at + 8) <= 18446744073709551615)))]);
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    trace__dump_updstate_avx2x4 <-
    (trace__dump_updstate_avx2x4 ++
    [(Assert, ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
    newat <- (newat + 8);
    while ((newat <= upto)) {
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st (4 * at));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      b_buf0 <-
      (A.set64d b_buf0 off (W64.of_int 18446744073709551615));
      buf0 <- (A.set64d buf0 off t64);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 8));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      b_buf1 <-
      (A.set64d b_buf1 off (W64.of_int 18446744073709551615));
      buf1 <- (A.set64d buf1 off t64);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 16));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      b_buf2 <-
      (A.set64d b_buf2 off (W64.of_int 18446744073709551615));
      buf2 <- (A.set64d buf2 off t64);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 24));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      b_buf3 <-
      (A.set64d b_buf3 off (W64.of_int 18446744073709551615));
      buf3 <- (A.set64d buf3 off t64);
      at <- newat;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
      off <- (off + 8);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= (newat + 8)) /\ ((newat + 8) <= 18446744073709551615)))]);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= upto) /\ (upto <= 18446744073709551615)))]);
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ (((4 * at) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st (4 * at));
      b_param_2 <- b_buf0;
      param_18 <- buf0;
      param_17 <- off;
      param_16 <- t64;
      param_15 <- (W64.to_uint upto8);
      (result_8, b_result_2, result_7, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_18, b_param_2, param_17, param_16, param_15);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) /\
        (((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_17 +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)))) /\
        ((param_17 +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) /\
        (((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_17 +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8)))) /\
        ((param_17 +
         ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                      param_15 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_2 0
        (param_17 +
        ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                     param_15 : 8)))
        ) /\
       (result_7 =
       (param_17 +
       ((((param_15 < 8) ? param_15 : 8) < 0) ? 0 : ((param_15 < 8) ? 
                                                    param_15 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
      b_buf0 <- b_result_2;
      buf0 <- result_8;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 8)) /\ (((4 * at) + 8) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 8)) /\ ((((4 * at) + 8) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 8));
      b_param_1 <- b_buf1;
      param_22 <- buf1;
      param_21 <- off;
      param_20 <- t64;
      param_19 <- (W64.to_uint upto8);
      (result_10, b_result_1, result_9, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_22, b_param_1, param_21, param_20, param_19);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) /\
        (((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_21 +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)))) /\
        ((param_21 +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) /\
        (((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_21 +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8)))) /\
        ((param_21 +
         ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                      param_19 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_1 0
        (param_21 +
        ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                     param_19 : 8)))
        ) /\
       (result_9 =
       (param_21 +
       ((((param_19 < 8) ? param_19 : 8) < 0) ? 0 : ((param_19 < 8) ? 
                                                    param_19 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_9) /\ (result_9 <= 18446744073709551615)))]);
      b_buf1 <- b_result_1;
      buf1 <- result_10;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 16)) /\ (((4 * at) + 16) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 16)) /\ ((((4 * at) + 16) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 16));
      b_param_0 <- b_buf2;
      param_26 <- buf2;
      param_25 <- off;
      param_24 <- t64;
      param_23 <- (W64.to_uint upto8);
      (result_12, b_result_0, result_11, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_26, b_param_0, param_25, param_24, param_23);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8))) /\
        (((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_25 +
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8)))) /\
        ((param_25 +
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8))) /\
        (((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_25 +
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8)))) /\
        ((param_25 +
         ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                      param_23 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result_0 0
        (param_25 +
        ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                     param_23 : 8)))
        ) /\
       (result_11 =
       (param_25 +
       ((((param_23 < 8) ? param_23 : 8) < 0) ? 0 : ((param_23 < 8) ? 
                                                    param_23 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_11) /\ (result_11 <= 18446744073709551615)))]);
      b_buf2 <- b_result_0;
      buf2 <- result_12;
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= (4 * at)) /\ ((4 * at) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * at) + 24)) /\ (((4 * at) + 24) <= 18446744073709551615)))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= ((4 * at) + 24)) /\ ((((4 * at) + 24) + 8) <= 800)))]);
      t64 <- (BArray800.get64d st ((4 * at) + 24));
      b_param <- b_buf3;
      param_30 <- buf3;
      param_29 <- off;
      param_28 <- t64;
      param_27 <- (W64.to_uint upto8);
      (result_14, b_result, result_13, tmp__trace) <@ RW.MM.__a_rlen_write_upto8 (
      param_30, b_param, param_29, param_28, param_27);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++ tmp__trace);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert,
       (((0 <=
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8))) /\
        (((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_29 +
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8)))) /\
        ((param_29 +
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8))) <=
        18446744073709551615)) /\
       (((0 <=
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8))) /\
        (((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8)) <=
        18446744073709551615)) /\
       (((0 <=
         (param_29 +
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8)))) /\
        ((param_29 +
         ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                      param_27 : 8))) <=
        18446744073709551615)) /\
       ((A.is_init b_result 0
        (param_29 +
        ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                     param_27 : 8)))
        ) /\
       (result_13 =
       (param_29 +
       ((((param_27 < 8) ? param_27 : 8) < 0) ? 0 : ((param_27 < 8) ? 
                                                    param_27 : 8))))))))))]);
      trace__dump_updstate_avx2x4 <-
      (trace__dump_updstate_avx2x4 ++
      [(Assert, ((0 <= result_13) /\ (result_13 <= 18446744073709551615)))]);
      b_buf3 <- b_result;
      buf3 <- result_14;
      off <- result_13;
    } else {
      
    }
    at <- upto;
    return (buf0, b_buf0, buf1, b_buf1, buf2, b_buf2, buf3, b_buf3, off, 
           at, trace__dump_updstate_avx2x4);
  }
  proc _squeeze_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                                 buf0:A.t, b_buf0:A.t,
                                 buf1:A.t, b_buf1:A.t,
                                 buf2:A.t, b_buf2:A.t,
                                 buf3:A.t, b_buf3:A.t,
                                 len:int) : BArray808.t * BArray808.t *
                                            A.t * A.t *
                                            A.t * A.t *
                                            A.t * A.t *
                                            A.t * A.t * trace = {
    var aux:BArray800.t;
    var aux_0:BArray800.t;
    var ststatus:W64.t;
    var stk:BArray800.t;
    var r8:int;
    var at:int;
    var off:int;
    var param:W64.t;
    var result:int;
    var result_0:int;
    var result_1:W64.t;
    var param_0:BArray800.t;
    var result_2:BArray800.t;
    var param_1:int;
    var param_2:int;
    var param_3:BArray800.t;
    var param_4:int;
    var param_5:A.t;
    var param_6:A.t;
    var param_7:A.t;
    var param_8:A.t;
    var result_3:int;
    var result_4:int;
    var result_5:A.t;
    var result_6:A.t;
    var result_7:A.t;
    var result_8:A.t;
    var param_9:BArray800.t;
    var result_9:BArray800.t;
    var param_10:int;
    var param_11:int;
    var param_12:BArray800.t;
    var param_13:int;
    var param_14:A.t;
    var param_15:A.t;
    var param_16:A.t;
    var param_17:A.t;
    var result_10:int;
    var result_11:int;
    var result_12:A.t;
    var result_13:A.t;
    var result_14:A.t;
    var result_15:A.t;
    var b_stk:BArray800.t;
    var b_result:A.t;
    var b_result_0:A.t;
    var b_result_1:A.t;
    var b_result_2:A.t;
    var b_param:BArray800.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var b_param_3:A.t;
    var b_result_3:BArray800.t;
    var b_param_4:BArray800.t;
    var b_result_4:A.t;
    var b_result_5:A.t;
    var b_result_6:A.t;
    var b_result_7:A.t;
    var b_param_5:BArray800.t;
    var b_param_6:A.t;
    var b_param_7:A.t;
    var b_param_8:A.t;
    var b_param_9:A.t;
    var b_result_8:BArray800.t;
    var b_param_10:BArray800.t;
    var trace__squeeze_updstate_avx2x4:trace;
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
    b_param_10 <- witness;
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
    b_stk <- witness;
    param_0 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_12 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    result_2 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_8 <- witness;
    result_9 <- witness;
    result_12 <- witness;
    result_13 <- witness;
    result_14 <- witness;
    result_15 <- witness;
    stk <- witness;
    trace__squeeze_updstate_avx2x4 <- [];
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert,
     (((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)))]);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    ststatus <- (BArray808.get64 st 100);
    param <- ststatus;
    (result_1, result_0, result, tmp__trace) <@ M._ststatus_data_avx2x4 (
    param);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++ tmp__trace);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert,
     (((((0 < result_0) /\ (result_0 <= 200)) /\ ((result_0 %% 8) = 0)) /\
      (0 <= result)) /\
     (result < result_0)))]);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
    r8 <- result_0;
    at <- result;
    b_stk <- (SBArray808_800.get_sub256 b_st 0);
    stk <- (SBArray808_800.get_sub256 st 0);
    if ((at = 0)) {
      b_param_10 <- b_stk;
      param_0 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_0, b_param_10);
      result_2 <- aux;
      b_result_8 <- aux_0;
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++ tmp__trace);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_8 0 800))]);
      b_stk <- (BArray800.init_arr (W8.of_int 255));
      stk <- result_2;
    } else {
      
    }
    off <- 0;
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= (len + at)) /\ ((len + at) <= 18446744073709551615)))]);
    len <- (len + at);
    while ((r8 < len)) {
      b_param_9 <- b_buf0;
      param_8 <- buf0;
      b_param_8 <- b_buf1;
      param_7 <- buf1;
      b_param_7 <- b_buf2;
      param_6 <- buf2;
      b_param_6 <- b_buf3;
      param_5 <- buf3;
      param_4 <- off;
      b_param_5 <- b_stk;
      param_3 <- stk;
      param_2 <- at;
      param_1 <- r8;
      (result_8, b_result_7, result_7, b_result_6, result_6, b_result_5,
      result_5, b_result_4, result_4, result_3, tmp__trace) <@ _dump_updstate_avx2x4 (
      param_8, b_param_9, param_7, b_param_8, param_6, b_param_7, param_5,
      b_param_6, param_4, param_3, b_param_5, param_2, param_1);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++ tmp__trace);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert,
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       (((0 <= (param_1 - param_2)) /\
        ((param_1 - param_2) <= 18446744073709551615)) /\
       (((0 <= (param_4 + (param_1 - param_2))) /\
        ((param_4 + (param_1 - param_2)) <= 18446744073709551615)) /\
       ((((((result_4 = (param_4 + (param_1 - param_2))) /\
           (result_3 = param_1)) /\
          (A.is_init b_result_7 0 (param_4 + (param_1 - param_2)))) /\
         (A.is_init b_result_6 0 (param_4 + (param_1 - param_2)))) /\
        (A.is_init b_result_5 0 (param_4 + (param_1 - param_2)))) /\
       (A.is_init b_result_4 0 (param_4 + (param_1 - param_2)))))))))))))))]);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      b_buf0 <- b_result_7;
      buf0 <- result_8;
      b_buf1 <- b_result_6;
      buf1 <- result_7;
      b_buf2 <- b_result_5;
      buf2 <- result_6;
      b_buf3 <- b_result_4;
      buf3 <- result_5;
      off <- result_4;
      b_param_4 <- b_stk;
      param_9 <- stk;
      (aux, aux_0, tmp__trace) <@ M._keccakf1600_avx2x4 (param_9, b_param_4);
      result_9 <- aux;
      b_result_3 <- aux_0;
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++ tmp__trace);
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert, (BArray800.is_init b_result_3 0 800))]);
      b_stk <- (BArray800.init_arr (W8.of_int 255));
      stk <- result_9;
      trace__squeeze_updstate_avx2x4 <-
      (trace__squeeze_updstate_avx2x4 ++
      [(Assert, ((0 <= (len - r8)) /\ ((len - r8) <= 18446744073709551615)))]);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    b_param_3 <- b_buf0;
    param_17 <- buf0;
    b_param_2 <- b_buf1;
    param_16 <- buf1;
    b_param_1 <- b_buf2;
    param_15 <- buf2;
    b_param_0 <- b_buf3;
    param_14 <- buf3;
    param_13 <- off;
    b_param <- b_stk;
    param_12 <- stk;
    param_11 <- at;
    param_10 <- len;
    (result_15, b_result_2, result_14, b_result_1, result_13, b_result_0,
    result_12, b_result, result_11, result_10, tmp__trace) <@ _dump_updstate_avx2x4 (
    param_17, b_param_3, param_16, b_param_2, param_15, b_param_1, param_14,
    b_param_0, param_13, param_12, b_param, param_11, param_10);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++ tmp__trace);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert,
     (((0 <= (param_10 - param_11)) /\
      ((param_10 - param_11) <= 18446744073709551615)) /\
     (((0 <= (param_13 + (param_10 - param_11))) /\
      ((param_13 + (param_10 - param_11)) <= 18446744073709551615)) /\
     (((0 <= (param_10 - param_11)) /\
      ((param_10 - param_11) <= 18446744073709551615)) /\
     (((0 <= (param_13 + (param_10 - param_11))) /\
      ((param_13 + (param_10 - param_11)) <= 18446744073709551615)) /\
     (((0 <= (param_10 - param_11)) /\
      ((param_10 - param_11) <= 18446744073709551615)) /\
     (((0 <= (param_13 + (param_10 - param_11))) /\
      ((param_13 + (param_10 - param_11)) <= 18446744073709551615)) /\
     (((0 <= (param_10 - param_11)) /\
      ((param_10 - param_11) <= 18446744073709551615)) /\
     (((0 <= (param_13 + (param_10 - param_11))) /\
      ((param_13 + (param_10 - param_11)) <= 18446744073709551615)) /\
     (((0 <= (param_10 - param_11)) /\
      ((param_10 - param_11) <= 18446744073709551615)) /\
     (((0 <= (param_13 + (param_10 - param_11))) /\
      ((param_13 + (param_10 - param_11)) <= 18446744073709551615)) /\
     ((((((result_11 = (param_13 + (param_10 - param_11))) /\
         (result_10 = param_10)) /\
        (A.is_init b_result_2 0 (param_13 + (param_10 - param_11)))) /\
       (A.is_init b_result_1 0 (param_13 + (param_10 - param_11)))) /\
      (A.is_init b_result_0 0 (param_13 + (param_10 - param_11)))) /\
     (A.is_init b_result 0 (param_13 + (param_10 - param_11)))))))))))))))]);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= result_11) /\ (result_11 <= 18446744073709551615)))]);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
    b_buf0 <- b_result_2;
    buf0 <- result_15;
    b_buf1 <- b_result_1;
    buf1 <- result_14;
    b_buf2 <- b_result_0;
    buf2 <- result_13;
    b_buf3 <- b_result;
    buf3 <- result_12;
    at <- result_10;
    b_st <- (SBArray808_800.set_sub256 b_st 0 b_stk);
    st <- (SBArray808_800.set_sub256 st 0 stk);
    trace__squeeze_updstate_avx2x4 <-
    (trace__squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
    b_st <- (BArray808.set8d b_st 800 (W8.of_int 255));
    st <- (BArray808.set8d st 800 (truncateu8 (W64.of_int at)));
    return (st, b_st, buf0, b_buf0, buf1, b_buf1, buf2, b_buf2, buf3, 
           b_buf3, trace__squeeze_updstate_avx2x4);
  }
  proc absorb_bcast_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                                     buf:A.t, b_buf:A.t,
                                     len:int) : BArray808.t * BArray808.t *
                                                trace = {
    var aux:BArray808.t;
    var aux_0:BArray808.t;
    var param:int;
    var param_0:A.t;
    var param_1:BArray808.t;
    var result:BArray808.t;
    var b_result:BArray808.t;
    var b_param:A.t;
    var trace_absorb_bcast_updstate_avx2x4:trace;
    b_param <- witness;
    b_result <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_absorb_bcast_updstate_avx2x4 <- [];
    trace_absorb_bcast_updstate_avx2x4 <-
    (trace_absorb_bcast_updstate_avx2x4 ++
    [(Assert,
     ((((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
     (A.is_init b_buf 0 len)))]);
    trace_absorb_bcast_updstate_avx2x4 <-
    (trace_absorb_bcast_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    st <- st;
    b_buf <- b_buf;
    buf <- buf;
    len <- len;
    param_1 <- st;
    b_param <- b_buf;
    param_0 <- buf;
    param <- len;
    (aux, aux_0, tmp__trace) <@ _absorb_bcast_updstate_avx2x4 (param_1,
    (BArray808.init_arr (W8.of_int 255)), param_0, b_param, param);
    result <- aux;
    b_result <- aux_0;
    trace_absorb_bcast_updstate_avx2x4 <-
    (trace_absorb_bcast_updstate_avx2x4 ++ tmp__trace);
    trace_absorb_bcast_updstate_avx2x4 <-
    (trace_absorb_bcast_updstate_avx2x4 ++
    [(Assert, (BArray808.is_init b_result 0 808))]);
    st <- result;
    b_st <- (BArray808.init_arr (W8.of_int 255));
    return (st, b_st, trace_absorb_bcast_updstate_avx2x4);
  }
  proc absorb_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                               buf0:A.t, b_buf0:A.t,
                               buf1:A.t, b_buf1:A.t,
                               buf2:A.t, b_buf2:A.t,
                               buf3:A.t, b_buf3:A.t, len:int) : 
  BArray808.t * BArray808.t * trace = {
    var aux:BArray808.t;
    var aux_0:BArray808.t;
    var param:int;
    var param_0:A.t;
    var param_1:A.t;
    var param_2:A.t;
    var param_3:A.t;
    var param_4:BArray808.t;
    var result:BArray808.t;
    var b_result:BArray808.t;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var trace_absorb_updstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_result <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    trace_absorb_updstate_avx2x4 <- [];
    trace_absorb_updstate_avx2x4 <-
    (trace_absorb_updstate_avx2x4 ++
    [(Assert,
     (((((((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)) /\
        (A.is_init b_buf0 0 len)) /\
       (A.is_init b_buf1 0 len)) /\
      (A.is_init b_buf2 0 len)) /\
     (A.is_init b_buf3 0 len)))]);
    trace_absorb_updstate_avx2x4 <-
    (trace_absorb_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    st <- st;
    b_buf0 <- b_buf0;
    buf0 <- buf0;
    b_buf1 <- b_buf1;
    buf1 <- buf1;
    b_buf2 <- b_buf2;
    buf2 <- buf2;
    b_buf3 <- b_buf3;
    buf3 <- buf3;
    len <- len;
    param_4 <- st;
    b_param_2 <- b_buf0;
    param_3 <- buf0;
    b_param_1 <- b_buf1;
    param_2 <- buf1;
    b_param_0 <- b_buf2;
    param_1 <- buf2;
    b_param <- b_buf3;
    param_0 <- buf3;
    param <- len;
    (aux, aux_0, tmp__trace) <@ _absorb_updstate_avx2x4 (param_4,
    (BArray808.init_arr (W8.of_int 255)), param_3, b_param_2, param_2,
    b_param_1, param_1, b_param_0, param_0, b_param, param);
    result <- aux;
    b_result <- aux_0;
    trace_absorb_updstate_avx2x4 <-
    (trace_absorb_updstate_avx2x4 ++ tmp__trace);
    trace_absorb_updstate_avx2x4 <-
    (trace_absorb_updstate_avx2x4 ++
    [(Assert, (BArray808.is_init b_result 0 808))]);
    st <- result;
    b_st <- (BArray808.init_arr (W8.of_int 255));
    return (st, b_st, trace_absorb_updstate_avx2x4);
  }
  proc squeeze_updstate_avx2x4 (st:BArray808.t, b_st:BArray808.t,
                                buf0:A.t, b_buf0:A.t,
                                buf1:A.t, b_buf1:A.t,
                                buf2:A.t, b_buf2:A.t,
                                buf3:A.t, b_buf3:A.t, len:int) : 
  BArray808.t * BArray808.t * A.t * A.t * A.t *
  A.t * A.t * A.t * A.t * A.t * trace = {
    var aux:BArray808.t;
    var aux_0:BArray808.t;
    var aux_1:A.t;
    var aux_2:A.t;
    var aux_3:A.t;
    var aux_4:A.t;
    var aux_5:A.t;
    var aux_6:A.t;
    var aux_7:A.t;
    var aux_8:A.t;
    var param:int;
    var param_0:A.t;
    var param_1:A.t;
    var param_2:A.t;
    var param_3:A.t;
    var param_4:BArray808.t;
    var result:A.t;
    var result_0:A.t;
    var result_1:A.t;
    var result_2:A.t;
    var result_3:BArray808.t;
    var b_result:A.t;
    var b_result_0:A.t;
    var b_result_1:A.t;
    var b_result_2:A.t;
    var b_result_3:BArray808.t;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var b_param_2:A.t;
    var trace_squeeze_updstate_avx2x4:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_squeeze_updstate_avx2x4 <- [];
    trace_squeeze_updstate_avx2x4 <-
    (trace_squeeze_updstate_avx2x4 ++
    [(Assert,
     (((BArray808.is_init b_st 0 808) /\ (0 <= len)) /\ (len <= _ASIZE)))]);
    trace_squeeze_updstate_avx2x4 <-
    (trace_squeeze_updstate_avx2x4 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    st <- st;
    b_buf0 <- b_buf0;
    buf0 <- buf0;
    b_buf1 <- b_buf1;
    buf1 <- buf1;
    b_buf2 <- b_buf2;
    buf2 <- buf2;
    b_buf3 <- b_buf3;
    buf3 <- buf3;
    param_4 <- st;
    b_param_2 <- b_buf0;
    param_3 <- buf0;
    b_param_1 <- b_buf1;
    param_2 <- buf1;
    b_param_0 <- b_buf2;
    param_1 <- buf2;
    b_param <- b_buf3;
    param_0 <- buf3;
    param <- len;
    (aux, aux_0, aux_1, aux_2, aux_3, aux_4, aux_5, aux_6, aux_7, aux_8,
    tmp__trace) <@ _squeeze_updstate_avx2x4 (param_4,
    (BArray808.init_arr (W8.of_int 255)), param_3, b_param_2, param_2,
    b_param_1, param_1, b_param_0, param_0, b_param, param);
    result_3 <- aux;
    b_result_3 <- aux_0;
    result_2 <- aux_1;
    b_result_2 <- aux_2;
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    result_0 <- aux_5;
    b_result_0 <- aux_6;
    result <- aux_7;
    b_result <- aux_8;
    trace_squeeze_updstate_avx2x4 <-
    (trace_squeeze_updstate_avx2x4 ++ tmp__trace);
    trace_squeeze_updstate_avx2x4 <-
    (trace_squeeze_updstate_avx2x4 ++
    [(Assert,
     (((((BArray808.is_init b_result_3 0 808) /\
        (A.is_init b_result_2 0 param)) /\
       (A.is_init b_result_1 0 param)) /\
      (A.is_init b_result_0 0 param)) /\
     (A.is_init b_result 0 param)))]);
    st <- result_3;
    b_buf0 <- b_result_2;
    buf0 <- result_2;
    b_buf1 <- b_result_1;
    buf1 <- result_1;
    b_buf2 <- b_result_0;
    buf2 <- result_0;
    b_buf3 <- b_result;
    buf3 <- result;
    b_st <- (BArray808.init_arr (W8.of_int 255));
    return (st, b_st, buf0, b_buf0, buf1, b_buf1, buf2, b_buf2, buf3, 
           b_buf3, trace_squeeze_updstate_avx2x4);
  }
}.

(* safety specifications *)

op _add_bcast_updstate_avx2x4_spec _st _b_st _at _buf _b_buf _off _upto =
   hoare [MM._add_bcast_updstate_avx2x4 :
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
   (((((((BArray800.is_init _b_st 0 800) /\ (0 <= _at)) /\ (_at <= _upto)) /\
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
    (((BArray800.is_init res.`2 0 800) /\ (res.`3 = _upto)) /\
    (res.`4 = (_off + (_upto - _at)))))))))))))))))))))))) /\
   (valid res.`5))].

op _absorb_bcast_updstate_avx2x4_spec _st _b_st _buf _b_buf _len =
   hoare [MM._absorb_bcast_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   ((((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
   (A.is_init _b_buf 0 _len))))))))) ==>
   ((BArray808.is_init res.`2 0 808) /\ (valid res.`3))].

op _add_updstate_avx2x4_spec _st _b_st _at _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _off _upto =
   hoare [MM._add_updstate_avx2x4 :
   (((_upto = upto) /\
    ((_off = off) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_at = at) /\ ((_b_st = b_st) /\ (_st = st))))))))))))) /\
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
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
   ((((((((((BArray800.is_init _b_st 0 800) /\ (0 <= _at)) /\ (_at <= _upto)) /\
         (_upto <= 200)) /\
        (0 <= _off)) /\
       ((_off + (_upto - _at)) <= _ASIZE)) /\
      (A.is_init _b_buf0 _off (_upto - _at))) /\
     (A.is_init _b_buf1 _off (_upto - _at))) /\
    (A.is_init _b_buf2 _off (_upto - _at))) /\
   (A.is_init _b_buf3 _off (_upto - _at))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (((BArray800.is_init res.`2 0 800) /\ (res.`3 = _upto)) /\
    (res.`4 = (_off + (_upto - _at)))))))))))))))))))))))) /\
   (valid res.`5))].

op _absorb_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len =
   hoare [MM._absorb_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_b_st = b_st) /\ (_st = st))))))))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
      (A.is_init _b_buf0 0 _len)) /\
     (A.is_init _b_buf1 0 _len)) /\
    (A.is_init _b_buf2 0 _len)) /\
   (A.is_init _b_buf3 0 _len)))))))))))) ==>
   ((BArray808.is_init res.`2 0 808) /\ (valid res.`3))].

op _dump_updstate_avx2x4_spec _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _off _st _b_st _at _upto =
   hoare [MM._dump_updstate_avx2x4 :
   (((_upto = upto) /\
    ((_at = at) /\
    ((_b_st = b_st) /\
    ((_st = st) /\
    ((_off = off) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\ ((_b_buf0 = b_buf0) /\ (_buf0 = buf0))))))))))))) /\
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
   ((((((((((BArray800.is_init _b_st 0 800) /\ (0 <= _at)) /\ (_at <= _upto)) /\
         (_upto <= 200)) /\
        (0 <= _off)) /\
       ((_off + (_upto - _at)) <= _ASIZE)) /\
      (A.is_init _b_buf0 0 _off)) /\
     (A.is_init _b_buf1 0 _off)) /\
    (A.is_init _b_buf2 0 _off)) /\
   (A.is_init _b_buf3 0 _off)))))))))))))))))))))))))))))))))) ==>
   (((true /\
     (true /\ ((0 <= res.`10) /\ (res.`10 <= 18446744073709551615)))) /\
    ((true /\ (true /\ ((0 <= res.`9) /\ (res.`9 <= 18446744073709551615)))) /\
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
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    (((0 <= (_upto - _at)) /\ ((_upto - _at) <= 18446744073709551615)) /\
    (((0 <= (_off + (_upto - _at))) /\
     ((_off + (_upto - _at)) <= 18446744073709551615)) /\
    ((((((res.`9 = (_off + (_upto - _at))) /\ (res.`10 = _upto)) /\
       (A.is_init res.`2 0 (_off + (_upto - _at)))) /\
      (A.is_init res.`4 0 (_off + (_upto - _at)))) /\
     (A.is_init res.`6 0 (_off + (_upto - _at)))) /\
    (A.is_init res.`8 0 (_off + (_upto - _at)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`11))].

op _squeeze_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len =
   hoare [MM._squeeze_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_b_st = b_st) /\ (_st = st))))))))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    (((((BArray808.is_init res.`2 0 808) /\
       (A.is_init res.`4 0 _len)) /\
      (A.is_init res.`6 0 _len)) /\
     (A.is_init res.`8 0 _len)) /\
    (A.is_init res.`10 0 _len)))))) /\
   (valid res.`11))].

op absorb_bcast_updstate_avx2x4_spec _st _b_st _buf _b_buf _len =
   hoare [MM.absorb_bcast_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf = b_buf) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   ((((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
   (A.is_init _b_buf 0 _len))))))))) ==>
   ((BArray808.is_init res.`2 0 808) /\ (valid res.`3))].

op absorb_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len =
   hoare [MM.absorb_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_b_st = b_st) /\ (_st = st))))))))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)) /\
      (A.is_init _b_buf0 0 _len)) /\
     (A.is_init _b_buf1 0 _len)) /\
    (A.is_init _b_buf2 0 _len)) /\
   (A.is_init _b_buf3 0 _len)))))))))))) ==>
   ((BArray808.is_init res.`2 0 808) /\ (valid res.`3))].

op squeeze_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len =
   hoare [MM.squeeze_updstate_avx2x4 :
   (((_len = len) /\
    ((_b_buf3 = b_buf3) /\
    ((_buf3 = buf3) /\
    ((_b_buf2 = b_buf2) /\
    ((_buf2 = buf2) /\
    ((_b_buf1 = b_buf1) /\
    ((_buf1 = buf1) /\
    ((_b_buf0 = b_buf0) /\
    ((_buf0 = buf0) /\ ((_b_st = b_st) /\ (_st = st))))))))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
   (true /\
   (true /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((BArray808.is_init _b_st 0 808) /\ (0 <= _len)) /\ (_len <= _ASIZE)))))))) ==>
   ((true /\
    (true /\
    (true /\
    (true /\
    (((((BArray808.is_init res.`2 0 808) /\
       (A.is_init res.`4 0 _len)) /\
      (A.is_init res.`6 0 _len)) /\
     (A.is_init res.`8 0 _len)) /\
    (A.is_init res.`10 0 _len)))))) /\
   (valid res.`11))].

lemma _add_bcast_updstate_avx2x4_proof _st _b_st _at _buf _b_buf _off _upto :
      (_add_bcast_updstate_avx2x4_spec _st _b_st _at _buf _b_buf _off _upto).
proof.
rewrite /_add_bcast_updstate_avx2x4_spec; proc.
sp 12.
if.
+ (* then *)
  seq 35 : ((valid trace__add_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf _off (_upto - _at))).
  + (* cut *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_1 b_param_0 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace__add_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf _off (_upto - _at)) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf _off (_upto - _at))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_4 b_param param_3 param_2).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 4 : ((valid trace__add_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf _off (_upto - _at)) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_bcast_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf _off (_upto - _at))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_4 b_param param_3 param_2).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma _absorb_bcast_updstate_avx2x4_proof _st _b_st _buf _b_buf _len :
      (_absorb_bcast_updstate_avx2x4_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /_absorb_bcast_updstate_avx2x4_spec; proc.
seq 34 : ((valid trace__absorb_bcast_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
wp; ecall (_add_bcast_updstate_avx2x4_proof param_10 b_param_0 param_9 param_8 b_param param_7 param_6).
wp; while ((valid trace__absorb_bcast_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf 0 _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* loop body *)
  wp; ecall (_keccakf1600_avx2x4_proof param_5 ((BArray800.init_arr (W8.of_int 255)))).
  wp; ecall (_add_bcast_updstate_avx2x4_proof param_4 b_param_2 param_3 param_2 b_param_1 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma _add_updstate_avx2x4_proof _st _b_st _at _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _off _upto :
      (_add_updstate_avx2x4_spec _st _b_st _at _buf0 _b_buf0 _buf1 _b_buf1
      _buf2 _b_buf2 _buf3 _b_buf3 _off _upto).
proof.
rewrite /_add_updstate_avx2x4_spec; proc.
sp 24.
if.
+ (* then *)
  seq 87 : ((valid trace__add_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 _off (_upto - _at) /\ A.is_init b_buf1 _off (_upto - _at) /\ A.is_init b_buf2 _off (_upto - _at) /\ A.is_init b_buf3 _off (_upto - _at))).
  + (* cut *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_10 b_param_3 param_9 param_8).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_7 b_param_4 param_6 param_5).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_4 b_param_5 param_3 param_2).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_1 b_param_6 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace__add_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 _off (_upto - _at) /\ A.is_init b_buf1 _off (_upto - _at) /\ A.is_init b_buf2 _off (_upto - _at) /\ A.is_init b_buf3 _off (_upto - _at)) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 _off (_upto - _at) /\ A.is_init b_buf1 _off (_upto - _at) /\ A.is_init b_buf2 _off (_upto - _at) /\ A.is_init b_buf3 _off (_upto - _at))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_22 b_param param_21 param_20).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_19 b_param_0 param_18 param_17).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_16 b_param_1 param_15 param_14).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_13 b_param_2 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 4 : ((valid trace__add_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 _off (_upto - _at) /\ A.is_init b_buf1 _off (_upto - _at) /\ A.is_init b_buf2 _off (_upto - _at) /\ A.is_init b_buf3 _off (_upto - _at)) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__add_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 _off (_upto - _at) /\ A.is_init b_buf1 _off (_upto - _at) /\ A.is_init b_buf2 _off (_upto - _at) /\ A.is_init b_buf3 _off (_upto - _at))).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_read_upto8_proof param_22 b_param param_21 param_20).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_19 b_param_0 param_18 param_17).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_16 b_param_1 param_15 param_14).
    wp; ecall (RW.__a_rlen_read_upto8_proof param_13 b_param_2 param_12 param_11).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma _absorb_updstate_avx2x4_proof _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len :
      (_absorb_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1
      _buf2 _b_buf2 _buf3 _b_buf3 _len).
proof.
rewrite /_absorb_updstate_avx2x4_spec; proc.
seq 46 : ((valid trace__absorb_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf0 0 _len /\ A.is_init b_buf1 0 _len /\ A.is_init b_buf2 0 _len /\ A.is_init b_buf3 0 _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
wp; ecall (_add_updstate_avx2x4_proof param_16 b_param_3 param_15 param_14 b_param_2 param_13 b_param_1 param_12 b_param_0 param_11 b_param param_10 param_9).
wp; while ((valid trace__absorb_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf0 0 _len /\ A.is_init b_buf1 0 _len /\ A.is_init b_buf2 0 _len /\ A.is_init b_buf3 0 _len /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* loop body *)
  wp; ecall (_keccakf1600_avx2x4_proof param_8 ((BArray800.init_arr (W8.of_int 255)))).
  wp; ecall (_add_updstate_avx2x4_proof param_7 b_param_8 param_6 param_5 b_param_7 param_4 b_param_6 param_3 b_param_5 param_2 b_param_4 param_1 param_0).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma _dump_updstate_avx2x4_proof _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _off _st _b_st _at _upto :
      (_dump_updstate_avx2x4_spec _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2
      _buf3 _b_buf3 _off _st _b_st _at _upto).
proof.
rewrite /_dump_updstate_avx2x4_spec; proc.
sp 40.
if.
+ (* then *)
  seq 79 : ((valid trace__dump_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off)).
  + (* cut *)
    wp; ecall (RW.__a_rlen_write_upto8_proof param_14 b_param_3 param_13 param_12 param_11).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_10 b_param_4 param_9 param_8 param_7).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_6 b_param_5 param_5 param_4 param_3).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_2 b_param_6 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  seq 1 : ((valid trace__dump_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__dump_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_write_upto8_proof param_30 b_param param_29 param_28 param_27).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_26 b_param_0 param_25 param_24 param_23).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_22 b_param_1 param_21 param_20 param_19).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_18 b_param_2 param_17 param_16 param_15).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  seq 4 : ((valid trace__dump_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off) /\ !((newat <= upto))).
  + (* loop *)
    wp; while ((valid trace__dump_updstate_avx2x4 /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= upto /\ off = _off + (at - _at) /\ (at %% 8 = 0 \/ at = upto) /\ newat = at + 8 /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off)).
    + (* loop body *)
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
    (* before the loop *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  if.
  + (* then *)
    wp; ecall (RW.__a_rlen_write_upto8_proof param_30 b_param param_29 param_28 param_27).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_26 b_param_0 param_25 param_24 param_23).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_22 b_param_1 param_21 param_20 param_19).
    wp; ecall (RW.__a_rlen_write_upto8_proof param_18 b_param_2 param_17 param_16 param_15).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  + (* else *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(and7_to_uint and7_nz int_shr3 int_shl3 divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma _squeeze_updstate_avx2x4_proof _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len :
      (_squeeze_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1
      _buf2 _b_buf2 _buf3 _b_buf3 _len).
proof.
rewrite /_squeeze_updstate_avx2x4_spec; proc.
seq 60 : ((valid trace__squeeze_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ len = _len /\ 0 <= _len <= _ASIZE /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
+ (* cut *)
  wp; ecall (_ststatus_data_avx2x4_proof param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
if.
+ (* then *)
  seq 12 : ((valid trace__squeeze_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* cut *)
    wp; ecall (_keccakf1600_avx2x4_proof param_0 b_param_10).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  wp; ecall (_dump_updstate_avx2x4_proof param_17 b_param_3 param_16 b_param_2 param_15 b_param_1 param_14 b_param_0 param_13 param_12 b_param param_11 param_10).
  wp; while ((valid trace__squeeze_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* loop body *)
    wp; ecall (_keccakf1600_avx2x4_proof param_9 b_param_4).
    wp; ecall (_dump_updstate_avx2x4_proof param_8 b_param_9 param_7 b_param_8 param_6 b_param_7 param_5 b_param_6 param_4 param_3 b_param_5 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
+ (* else *)
  wp; ecall (_dump_updstate_avx2x4_proof param_17 b_param_3 param_16 b_param_2 param_15 b_param_1 param_14 b_param_0 param_13 param_12 b_param param_11 param_10).
  wp; while ((valid trace__squeeze_updstate_avx2x4 /\ 0 < r8 <= 200 /\ 0 <= at < r8 /\ at <= len /\ 0 <= off /\ off + (len - at) = _len /\ 0 <= _len <= _ASIZE /\ A.is_init b_buf0 0 off /\ A.is_init b_buf1 0 off /\ A.is_init b_buf2 0 off /\ A.is_init b_buf3 0 off /\ BArray808.is_init b_st 0 808 /\ BArray800.is_init b_stk 0 800)).
  + (* loop body *)
    wp; ecall (_keccakf1600_avx2x4_proof param_9 b_param_4).
    wp; ecall (_dump_updstate_avx2x4_proof param_8 b_param_9 param_7 b_param_8 param_6 b_param_7 param_5 b_param_6 param_4 param_3 b_param_5 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
  (* before the loop *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma absorb_bcast_updstate_avx2x4_proof _st _b_st _buf _b_buf _len :
      (absorb_bcast_updstate_avx2x4_spec _st _b_st _buf _b_buf _len).
proof.
rewrite /absorb_bcast_updstate_avx2x4_spec; proc.
wp; ecall (_absorb_bcast_updstate_avx2x4_proof param_1 ((BArray808.init_arr (W8.of_int 255))) param_0 b_param param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma absorb_updstate_avx2x4_proof _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len :
      (absorb_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1
      _buf2 _b_buf2 _buf3 _b_buf3 _len).
proof.
rewrite /absorb_updstate_avx2x4_spec; proc.
wp; ecall (_absorb_updstate_avx2x4_proof param_4 ((BArray808.init_arr (W8.of_int 255))) param_3 b_param_2 param_2 b_param_1 param_1 b_param_0 param_0 b_param param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

lemma squeeze_updstate_avx2x4_proof _st _b_st _buf0 _b_buf0 _buf1 _b_buf1 _buf2 _b_buf2 _buf3 _b_buf3 _len :
      (squeeze_updstate_avx2x4_spec _st _b_st _buf0 _b_buf0 _buf1 _b_buf1
      _buf2 _b_buf2 _buf3 _b_buf3 _len).
proof.
rewrite /squeeze_updstate_avx2x4_spec; proc.
wp; ecall (_squeeze_updstate_avx2x4_proof param_4 ((BArray808.init_arr (W8.of_int 255))) param_3 b_param_2 param_2 b_param_1 param_1 b_param_0 param_0 b_param param).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; do ?(split; try (move=> *; rewrite ?List.all_cat /=)); smt(divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp _ASIZE_ge0 _ASIZE_u64).
qed.

end KeccakUpdstateAvx2x4Safety.
