(* -------------------------------------------------------------------- *)
(* Safety of the common helpers: feature query, shifts, rho offsets,
   memory/array sub-reads/writes, 4-way pack/unpack, status-word decoder.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.

(* -------------------------------------------------------------------- *)
(* bitmaps of fully (un)initialised arrays, sub-array updates             *)
require import SBArray208_200 SBArray808_800.
hint simplify SBArray208_200.is_init_cell_set, SBArray808_800.is_init_cell_set.
lemma BArray3_init_cell_ones k : BArray3.is_init_cell (BArray3.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray3.init_arrP witness). qed.
lemma BArray3_init_cell_zeros k : BArray3.is_init_cell (BArray3.init_arr (W8.of_int 0)) k = !(0 <= k < 3).
proof. by rewrite /BArray3.is_init_cell; case: (0 <= k < 3) => //= h; rewrite BArray3.initE h /= W8.to_uint_eq. qed.
hint simplify BArray3_init_cell_ones, BArray3_init_cell_zeros.
lemma BArray32_init_cell_ones k : BArray32.is_init_cell (BArray32.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray32.init_arrP witness). qed.
lemma BArray32_init_cell_zeros k : BArray32.is_init_cell (BArray32.init_arr (W8.of_int 0)) k = !(0 <= k < 32).
proof. by rewrite /BArray32.is_init_cell; case: (0 <= k < 32) => //= h; rewrite BArray32.initE h /= W8.to_uint_eq. qed.
hint simplify BArray32_init_cell_ones, BArray32_init_cell_zeros.
lemma BArray40_init_cell_ones k : BArray40.is_init_cell (BArray40.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray40.init_arrP witness). qed.
lemma BArray40_init_cell_zeros k : BArray40.is_init_cell (BArray40.init_arr (W8.of_int 0)) k = !(0 <= k < 40).
proof. by rewrite /BArray40.is_init_cell; case: (0 <= k < 40) => //= h; rewrite BArray40.initE h /= W8.to_uint_eq. qed.
hint simplify BArray40_init_cell_ones, BArray40_init_cell_zeros.
lemma BArray160_init_cell_ones k : BArray160.is_init_cell (BArray160.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray160.init_arrP witness). qed.
lemma BArray160_init_cell_zeros k : BArray160.is_init_cell (BArray160.init_arr (W8.of_int 0)) k = !(0 <= k < 160).
proof. by rewrite /BArray160.is_init_cell; case: (0 <= k < 160) => //= h; rewrite BArray160.initE h /= W8.to_uint_eq. qed.
hint simplify BArray160_init_cell_ones, BArray160_init_cell_zeros.
lemma BArray192_init_cell_ones k : BArray192.is_init_cell (BArray192.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray192.init_arrP witness). qed.
lemma BArray192_init_cell_zeros k : BArray192.is_init_cell (BArray192.init_arr (W8.of_int 0)) k = !(0 <= k < 192).
proof. by rewrite /BArray192.is_init_cell; case: (0 <= k < 192) => //= h; rewrite BArray192.initE h /= W8.to_uint_eq. qed.
hint simplify BArray192_init_cell_ones, BArray192_init_cell_zeros.
lemma BArray200_init_cell_ones k : BArray200.is_init_cell (BArray200.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray200.init_arrP witness). qed.
lemma BArray200_init_cell_zeros k : BArray200.is_init_cell (BArray200.init_arr (W8.of_int 0)) k = !(0 <= k < 200).
proof. by rewrite /BArray200.is_init_cell; case: (0 <= k < 200) => //= h; rewrite BArray200.initE h /= W8.to_uint_eq. qed.
hint simplify BArray200_init_cell_ones, BArray200_init_cell_zeros.
lemma BArray208_init_cell_ones k : BArray208.is_init_cell (BArray208.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray208.init_arrP witness). qed.
lemma BArray208_init_cell_zeros k : BArray208.is_init_cell (BArray208.init_arr (W8.of_int 0)) k = !(0 <= k < 208).
proof. by rewrite /BArray208.is_init_cell; case: (0 <= k < 208) => //= h; rewrite BArray208.initE h /= W8.to_uint_eq. qed.
hint simplify BArray208_init_cell_ones, BArray208_init_cell_zeros.
lemma BArray224_init_cell_ones k : BArray224.is_init_cell (BArray224.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray224.init_arrP witness). qed.
lemma BArray224_init_cell_zeros k : BArray224.is_init_cell (BArray224.init_arr (W8.of_int 0)) k = !(0 <= k < 224).
proof. by rewrite /BArray224.is_init_cell; case: (0 <= k < 224) => //= h; rewrite BArray224.initE h /= W8.to_uint_eq. qed.
hint simplify BArray224_init_cell_ones, BArray224_init_cell_zeros.
lemma BArray800_init_cell_ones k : BArray800.is_init_cell (BArray800.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray800.init_arrP witness). qed.
lemma BArray800_init_cell_zeros k : BArray800.is_init_cell (BArray800.init_arr (W8.of_int 0)) k = !(0 <= k < 800).
proof. by rewrite /BArray800.is_init_cell; case: (0 <= k < 800) => //= h; rewrite BArray800.initE h /= W8.to_uint_eq. qed.
hint simplify BArray800_init_cell_ones, BArray800_init_cell_zeros.
lemma BArray808_init_cell_ones k : BArray808.is_init_cell (BArray808.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (BArray808.init_arrP witness). qed.
lemma BArray808_init_cell_zeros k : BArray808.is_init_cell (BArray808.init_arr (W8.of_int 0)) k = !(0 <= k < 808).
proof. by rewrite /BArray808.is_init_cell; case: (0 <= k < 808) => //= h; rewrite BArray808.initE h /= W8.to_uint_eq. qed.
hint simplify BArray808_init_cell_ones, BArray808_init_cell_zeros.

lemma __HAS_FEATURE_proof _sELECTION _fEATURES :
      (__HAS_FEATURE_spec _sELECTION _fEATURES).
proof.
rewrite /__HAS_FEATURE_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __SHLQ_proof _x _shbytes : (__SHLQ_spec _x _shbytes).
proof.
rewrite /__SHLQ_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __SHLDQ_proof _x _shbytes : (__SHLDQ_spec _x _shbytes).
proof.
rewrite /__SHLDQ_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __SHLQ_256_proof _x _shbytes : (__SHLQ_256_spec _x _shbytes).
proof.
rewrite /__SHLQ_256_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __KECCAK_F_proof _pERMUTATION : (__KECCAK_F_spec _pERMUTATION).
proof.
rewrite /__KECCAK_F_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __KECCAK_Fx4_proof _pERMUTATION : (__KECCAK_Fx4_spec _pERMUTATION).
proof.
rewrite /__KECCAK_Fx4_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma keccakf1600_index_proof _x _y : (keccakf1600_index_spec _x _y).
proof.
rewrite /keccakf1600_index_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma keccakf1600_rho_offsets_proof _i : (keccakf1600_rho_offsets_spec _i).
proof.
rewrite /keccakf1600_rho_offsets_spec; proc.
wp; while ((valid trace_keccakf1600_rho_offsets)).
+ (* loop body *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma keccakf1600_rhotates_proof _x _y : (keccakf1600_rhotates_spec _x _y).
proof.
rewrite /keccakf1600_rhotates_spec; proc.
inline M.keccakf1600_index.
wp; ecall (keccakf1600_rho_offsets_proof param_1).
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* memory sub-reads/writes *)

lemma __m_ilen_read_upto8_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_upto8_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_upto8_at_spec; proc.
inline M.__SHLQ.
sp 3.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    if.
    + (* then *)
      sp 8.
      if.
      + (* then *)
        sp 9.
        if.
        + (* then *)
          sp 12.
          if.
          + (* then *)
            sp 6.
            if.
            + (* then *)
              sp 11.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            sp 5.
            if.
            + (* then *)
              sp 11.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
        + (* else *)
          if.
          + (* then *)
            sp 11.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
      + (* else *)
        sp 8.
        if.
        + (* then *)
          sp 12.
          if.
          + (* then *)
            sp 6.
            if.
            + (* then *)
              sp 11.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            sp 5.
            if.
            + (* then *)
              sp 11.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
        + (* else *)
          if.
          + (* then *)
            sp 11.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
    + (* else *)
      sp 1.
      if.
      + (* then *)
        sp 12.
        if.
        + (* then *)
          sp 6.
          if.
          + (* then *)
            sp 11.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
        + (* else *)
          sp 5.
          if.
          + (* then *)
            sp 11.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
      + (* else *)
        if.
        + (* then *)
          sp 11.
          if.
          + (* then *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_read_upto16_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_upto16_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_upto16_at_spec; proc.
inline M.__SHLDQ.
sp 3.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    if.
    + (* then *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_5 param_4 param_3 param_2 param_1).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
    + (* else *)
      wp; ecall (__m_ilen_read_upto8_at_proof param_15 param_14 param_13 param_12 param_11).
      wp; ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_read_upto32_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_upto32_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_upto32_at_spec; proc.
sp 3.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    if.
    + (* then *)
      wp; ecall (__m_ilen_read_upto16_at_proof param_3 param_2 param_1 param_0 param).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
    + (* else *)
      wp; ecall (__m_ilen_read_upto16_at_proof param_13 param_12 param_11 param_10 param_9).
      wp; ecall (__m_ilen_read_upto16_at_proof param_8 param_7 param_6 param_5 param_4).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_read_bcast_upto8_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_bcast_upto8_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_bcast_upto8_at_spec; proc.
inline M.__SHLQ_256.
sp 3.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    wp; ecall (__m_ilen_read_upto8_at_proof param_5 param_4 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_write_upto8_proof _buf _lEN _w :
      (__m_ilen_write_upto8_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto8_spec; proc.
sp 3.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    if.
    + (* then *)
      sp 7.
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
    + (* else *)
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_write_upto16_proof _buf _lEN _w :
      (__m_ilen_write_upto16_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto16_spec; proc.
sp 3.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    wp; ecall (__m_ilen_write_upto8_proof param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __m_ilen_write_upto32_proof _buf _lEN _w :
      (__m_ilen_write_upto32_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto32_spec; proc.
sp 3.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
  + (* else *)
    wp; ecall (__m_ilen_write_upto16_proof param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* -------------------------------------------------------------------- *)
(* TEST_64 on small lengths (variable-length sub-reads/writes)             *)

lemma and_shlwE (x y: W64.t) k:
 x `&` (y `<<<` k) = ((x `>>>` k) `&` y) `<<<` k.
proof.
apply W64.ext_eq => i Hi.
rewrite andwE !shlwE andwE !shrwE !Hi /=.
case: (0 <= i - k < 64 ) => C/=; first smt().
by  rewrite (W64.get_out y) //.
qed.

lemma test_64_zf k x:
 0 <= k < 64 =>
 (TEST_64 x (W64.of_int (2^k))).`5 <=> !(x.[k]).
proof.
move => Hk; rewrite /TEST_64 /rflags_of_bwop /= /ZF_of get_to_uint Hk /=.
have ->: W64.of_int (2 ^ k) = W64.one `<<<` k by rewrite shlMP 1:/#.
rewrite and_shlwE to_uint_eq /= (:1=2^1-1) 1:/# and_mod //= to_uint_shl 1:/# of_uintK.
rewrite (modz_small (to_uint (x `>>>` k)%%2)) 1:/# modz_small.
 move: (modz_cmp (to_uint (x `>>>` k)) 2 _) => //.
 have ?: 0 <= 2^k < W64.modulus.
  split => *; first smt(gt0_pow2).
  rewrite ltz_def; split.
   apply (contra (W64.modulus = 2^k) (64=k) ).
    by apply (StdOrder.IntOrder.ieexprIn 2) => /#.
   smt().
  by apply StdOrder.IntOrder.ler_weexpn2l => /#.
 move=> ?.
 have: to_uint (x `>>>` k) %% 2 = 0 \/ to_uint (x `>>>` k) %% 2 = 1 by smt().
 by move=> [->|->] //=.
rewrite to_uint_shr 1:/#.
case: (to_uint x %/ 2 ^ k %% 2 = 0) => ?.
 smt().
smt(gt0_pow2).
qed.

lemma test_zf_small (l k : int) : 0 <= k < 64 => 0 <= l < 18446744073709551616 =>
  (TEST_64 (W64.of_int l) (W64.of_int (2^k))).`5 <=> l %/ 2^k %% 2 = 0.
proof. by move=> hk hl; rewrite test_64_zf // of_intwE hk /int_bit /= (modz_small l) /#. qed.

lemma zf4 l : 0 <= l < 8 => (TEST_64 (W64.of_int l) (W64.of_int 4)).`5 <=> l < 4.
proof.
move=> hl; rewrite (: 4 = 2^2) 1:// test_zf_small //; 1:smt().
have: l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 by smt().
by case=> [|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma zf2 l : 0 <= l < 8 => (TEST_64 (W64.of_int l) (W64.of_int 2)).`5 <=> (l = 0 \/ l = 1 \/ l = 4 \/ l = 5).
proof.
move=> hl; rewrite (: 2 = 2^1) 1:// test_zf_small //; 1:smt().
have: l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 by smt().
by case=> [|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma zf1 l : 0 <= l < 8 => (TEST_64 (W64.of_int l) W64.one).`5 <=> (l = 0 \/ l = 2 \/ l = 4 \/ l = 6).
proof.
move=> hl; rewrite (: W64.one = W64.of_int (2^0)) 1:// test_zf_small //; 1:smt().
have: l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 by smt().
by case=> [|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma __m_rlen_read_upto8_proof _buf _len :
      (__m_rlen_read_upto8_spec _buf _len).
proof.
rewrite /__m_rlen_read_upto8_spec; proc.
auto => &m /> *.
case: (8 <= len{m}) => h8; 1: smt().
have hl: 0 <= len{m} < 8 by smt().
rewrite (zf4 _ hl) (zf2 _ hl) (zf1 _ hl) /=.
smt().
qed.

lemma __m_rlen_write_upto8_proof _buf _data _len :
      (__m_rlen_write_upto8_spec _buf _data _len).
proof.
rewrite /__m_rlen_write_upto8_spec; proc.
auto => &m /> *.
case: (8 <= len{m}) => h8; 1: smt().
have hl: 0 <= len{m} < 8 by smt().
rewrite (zf4 _ hl) (zf2 _ hl) (zf1 _ hl) /=.
smt().
qed.

(* status-word decoder *)

lemma to_uint_and255 (w: W64.t) : 0 <= to_uint (w `&` W64.of_int 255) < 256.
proof. by rewrite (: 255 = 2^8-1) // to_uint_and_mod //; smt(modz_cmp). qed.

lemma _ststatus_data_proof _ststatus : (_ststatus_data_spec _ststatus).
proof.
rewrite /_ststatus_data_spec; proc.
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

(* 4-way pack/unpack *)

lemma __u256x4_4u64x4_proof _x0 _x1 _x2 _x3 :
      (__u256x4_4u64x4_spec _x0 _x1 _x2 _x3).
proof.
rewrite /__u256x4_4u64x4_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __st4x_pack_proof _st4x _b_st4x _st0 _b_st0 _st1 _b_st1 _st2 _b_st2 _st3 _b_st3 :
      (__st4x_pack_spec _st4x _b_st4x _st0 _b_st0 _st1 _b_st1 _st2 _b_st2
      _st3 _b_st3).
proof.
rewrite /__st4x_pack_spec; proc.
wp; while ((valid trace___st4x_pack /\ 0 <= i <= 6 /\ BArray800.is_init b_st4x 0 (128 * i))).
+ (* loop body *)
  wp; ecall (__u256x4_4u64x4_proof param_2 param_1 param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __4u64x4_u256x4_proof _y0 _y1 _y2 _y3 :
      (__4u64x4_u256x4_spec _y0 _y1 _y2 _y3).
proof.
rewrite /__4u64x4_u256x4_spec; proc.
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

lemma __st4x_unpack_proof _st0 _b_st0 _st1 _b_st1 _st2 _b_st2 _st3 _b_st3 _st4x _b_st4x :
      (__st4x_unpack_spec _st0 _b_st0 _st1 _b_st1 _st2 _b_st2 _st3 _b_st3
      _st4x _b_st4x).
proof.
rewrite /__st4x_unpack_spec; proc.
wp; while ((valid trace___st4x_unpack /\ 0 <= i <= 6 /\ BArray200.is_init b_st0 0 (32 * i) /\ BArray200.is_init b_st1 0 (32 * i) /\ BArray200.is_init b_st2 0 (32 * i) /\ BArray200.is_init b_st3 0 (32 * i))).
+ (* loop body *)
  wp; ecall (__4u64x4_u256x4_proof param_2 param_1 param_0 param).
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
(* before the loop *)
auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt()); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt().
qed.

(* -------------------------------------------------------------------- *)
(* word facts used by the streaming (updstate) code                        *)
lemma and7_to_uint (a : int) :
  0 <= a < 18446744073709551616 =>
  to_uint (W64.of_int a `&` W64.of_int 7) = a %% 8.
proof.
move=> ha; rewrite (: 7 = 2^3 - 1) // to_uint_and_mod // of_uintK.
by rewrite (modz_small a) //; smt().
qed.

lemma and7_nz (a : int) :
  0 <= a < 18446744073709551616 =>
  (W64.of_int a `&` W64.of_int 7 <> W64.of_int 0) = (a %% 8 <> 0).
proof. by move=> ha; rewrite W64.to_uint_eq /= (and7_to_uint a ha). qed.

lemma int_shr3 (a : int) : a `|>>` 3 = a %/ 8.
proof. by rewrite /(`|>>`) /(`<<`) /=. qed.

lemma int_shl3 (a : int) : a `<<` 3 = a * 8.
proof. by rewrite /(`<<`) /=. qed.

lemma chunks8 (l : int) :
  0 <= l => 32 * (l %/ 32) + (if 16 <= l %% 32 then 16 else 0) + (if 8 <= l %% 16 then 8 else 0) = 8 * (l %/ 8).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
(* Array variants, abstracted over the array size.                       *)
(* -------------------------------------------------------------------- *)
abstract theory ReadWriteArraySafety.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

(* the ui64 range conditions of the model are stated with the literal 2^64-1 *)
lemma _ASIZE_max: _ASIZE <= 18446744073709551615.
proof. smt(_ASIZE_u64 pow2_64). qed.

clone import ByteArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

lemma A_init_cell_ones k : A.is_init_cell (A.init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (A.init_arrP witness). qed.
lemma A_init_cell_zeros k : A.is_init_cell (A.init_arr (W8.of_int 0)) k = !(0 <= k < _ASIZE).
proof. by rewrite /A.is_init_cell; case: (0 <= k < _ASIZE) => //= h; rewrite A.initE h /= W8.to_uint_eq. qed.
hint simplify A_init_cell_ones, A_init_cell_zeros.

(* The array procedures of Keccak1600_Jazz_ASIZE_safety (extracted at
   _ASIZE = 999), with BArray999 replaced by A and 999 by _ASIZE,
   the size-independent callees taken from Keccak1600_Jazz_safety.M, and
   their safety specifications restated over MM. Generated by
   scripts/asize_transform.py --safety; checked by
   ../extracted/Keccak1600_subreadwrite_checkXtr.ec. *)

module MM = {
  var tmp__trace : trace
  proc __a_ilen_read_upto8_at (buf:A.t, b_buf:A.t,
                               offset:int, dELTA:int, lEN:int, tRAIL:int,
                               cUR:int, aT:int) : int * int * int * int *
                                                  W64.t * trace = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    var param:int;
    var param_0:W64.t;
    var result:W64.t;
    var param_1:int;
    var param_2:W64.t;
    var result_0:W64.t;
    var param_3:int;
    var param_4:W64.t;
    var result_1:W64.t;
    var param_5:int;
    var param_6:W64.t;
    var result_2:W64.t;
    var trace___a_ilen_read_upto8_at:trace;
    trace___a_ilen_read_upto8_at <- [];
    trace___a_ilen_read_upto8_at <-
    (trace___a_ilen_read_upto8_at ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 8) ? lEN : 8)) /\
      (((lEN < 8) ? lEN : 8) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 8) ? lEN : 8))) /\
      (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= 18446744073709551615)) /\
     (((((((A.is_init b_buf (offset + dELTA) ((lEN < 8) ? lEN : 8)) /\
          (0 <= dELTA)) /\
         (0 <= offset)) /\
        (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= _ASIZE)) /\
       (0 <= lEN)) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256)))))))))]);
    trace___a_ilen_read_upto8_at <-
    (trace___a_ilen_read_upto8_at ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        trace___a_ilen_read_upto8_at <-
        (trace___a_ilen_read_upto8_at ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_read_upto8_at <-
        (trace___a_ilen_read_upto8_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_read_upto8_at <-
        (trace___a_ilen_read_upto8_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
        trace___a_ilen_read_upto8_at <-
        (trace___a_ilen_read_upto8_at ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 8))]);
        w <- (A.get64d buf (offset + dELTA));
        param_0 <- w;
        param <- (aT - cUR);
        (result, tmp__trace) <@ M.__SHLQ (param_0, param);
        trace___a_ilen_read_upto8_at <-
        (trace___a_ilen_read_upto8_at ++ tmp__trace);
        w <- result;
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 4) <= _ASIZE)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, (A.is_init b_buf (offset + dELTA) 4))]);
          w <- (zeroextu64 (A.get32d buf (offset + dELTA)));
          param_2 <- w;
          param_1 <- (aT - cUR);
          (result_0, tmp__trace) <@ M.__SHLQ (param_2, param_1);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++ tmp__trace);
          w <- result_0;
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 2) <= _ASIZE)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, (A.is_init b_buf (offset + dELTA) 2))]);
          t16 <- (zeroextu64 (A.get16d buf (offset + dELTA)));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          param_4 <- t16;
          param_3 <- (aT - cUR);
          (result_1, tmp__trace) <@ M.__SHLQ (param_4, param_3);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++ tmp__trace);
          t16 <- result_1;
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 1) <= _ASIZE)))]);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++
          [(Assert, (A.is_init b_buf (offset + dELTA) 1))]);
          t8 <- (zeroextu64 (A.get8d buf (offset + dELTA)));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          param_6 <- t8;
          param_5 <- (aT - cUR);
          (result_2, tmp__trace) <@ M.__SHLQ (param_6, param_5);
          trace___a_ilen_read_upto8_at <-
          (trace___a_ilen_read_upto8_at ++ tmp__trace);
          t8 <- result_2;
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w, trace___a_ilen_read_upto8_at);
  }
  proc __a_ilen_read_upto16_at (buf:A.t, b_buf:A.t,
                                offset:int, dELTA:int, lEN:int, tRAIL:int,
                                cUR:int, aT:int) : int * int * int * int *
                                                   W128.t * trace = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    var param:int;
    var param_0:W128.t;
    var result:W128.t;
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
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:int;
    var param_19:int;
    var param_20:int;
    var param_21:A.t;
    var result_10:W64.t;
    var result_11:int;
    var result_12:int;
    var result_13:int;
    var result_14:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var trace___a_ilen_read_upto16_at:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    param_7 <- witness;
    param_14 <- witness;
    param_21 <- witness;
    trace___a_ilen_read_upto16_at <- [];
    trace___a_ilen_read_upto16_at <-
    (trace___a_ilen_read_upto16_at ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 16) ? lEN : 16)) /\
      (((lEN < 16) ? lEN : 16) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 16) ? lEN : 16))) /\
      (((offset + dELTA) + ((lEN < 16) ? lEN : 16)) <= 18446744073709551615)) /\
     (((((((A.is_init b_buf (offset + dELTA) ((lEN < 16) ? lEN : 16)) /\
          (0 <= dELTA)) /\
         (0 <= offset)) /\
        (((offset + dELTA) + ((lEN < 16) ? lEN : 16)) <= _ASIZE)) /\
       (0 <= lEN)) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256)))))))))]);
    trace___a_ilen_read_upto16_at <-
    (trace___a_ilen_read_upto16_at ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        trace___a_ilen_read_upto16_at <-
        (trace___a_ilen_read_upto16_at ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_read_upto16_at <-
        (trace___a_ilen_read_upto16_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_read_upto16_at <-
        (trace___a_ilen_read_upto16_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 16) <= _ASIZE)))]);
        trace___a_ilen_read_upto16_at <-
        (trace___a_ilen_read_upto16_at ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 16))]);
        w <- (A.get128d buf (offset + dELTA));
        param_0 <- w;
        param <- (aT - cUR);
        (result, tmp__trace) <@ M.__SHLDQ (param_0, param);
        trace___a_ilen_read_upto16_at <-
        (trace___a_ilen_read_upto16_at ++ tmp__trace);
        w <- result;
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          b_param <- b_buf;
          param_7 <- buf;
          param_6 <- offset;
          param_5 <- dELTA;
          param_4 <- lEN;
          param_3 <- tRAIL;
          param_2 <- (cUR + 8);
          param_1 <- aT;
          (result_4, result_3, result_2, result_1, result_0, tmp__trace) <@ 
          __a_ilen_read_upto8_at (param_7, b_param, param_6, param_5,
          param_4, param_3, param_2, param_1);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++ tmp__trace);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++
          [(Assert,
           (((param_2 <= param_1) /\ (param_1 < (param_2 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_1 -
                                                                    param_2) +
                                                                   param_4)) ? 
                                                                  (((
                                                                    (
                                                                    result_4 =
                                                                    (
                                                                    param_5 +
                                                                    (
                                                                    (
                                                                    param_2 +
                                                                    8) -
                                                                    param_1))) /\
                                                                    (
                                                                    result_3 =
                                                                    (
                                                                    param_4 -
                                                                    (
                                                                    (
                                                                    param_2 +
                                                                    8) -
                                                                    param_1)))) /\
                                                                   (result_2 =
                                                                   param_3)) /\
                                                                  (result_1 =
                                                                  (param_2 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_4 =
                                                                    (
                                                                    param_5 +
                                                                    param_4)) /\
                                                                    (
                                                                    result_3 =
                                                                    0)) /\
                                                                   (result_2 =
                                                                   0)) /\
                                                                  (result_1 =
                                                                  ((param_1 +
                                                                   param_4) +
                                                                  ((param_3 <>
                                                                   0) ? 1 : 0))))) : 
           ((((result_4 = param_5) /\ (result_3 = param_4)) /\
            (result_2 = param_3)) /\
           (result_1 = param_1))))]);
          dELTA <- result_4;
          lEN <- result_3;
          tRAIL <- result_2;
          aT <- result_1;
          t64_1 <- result_0;
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          b_param_1 <- b_buf;
          param_14 <- buf;
          param_13 <- offset;
          param_12 <- dELTA;
          param_11 <- lEN;
          param_10 <- tRAIL;
          param_9 <- cUR;
          param_8 <- aT;
          (result_9, result_8, result_7, result_6, result_5, tmp__trace) <@ 
          __a_ilen_read_upto8_at (param_14, b_param_1, param_13, param_12,
          param_11, param_10, param_9, param_8);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++ tmp__trace);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++
          [(Assert,
           (((param_9 <= param_8) /\ (param_8 < (param_9 + 8))) ? ((8 <=
                                                                   ((
                                                                    param_8 -
                                                                    param_9) +
                                                                   param_11)) ? 
                                                                  (((
                                                                    (
                                                                    result_9 =
                                                                    (
                                                                    param_12 +
                                                                    (
                                                                    (
                                                                    param_9 +
                                                                    8) -
                                                                    param_8))) /\
                                                                    (
                                                                    result_8 =
                                                                    (
                                                                    param_11 -
                                                                    (
                                                                    (
                                                                    param_9 +
                                                                    8) -
                                                                    param_8)))) /\
                                                                   (result_7 =
                                                                   param_10)) /\
                                                                  (result_6 =
                                                                  (param_9 +
                                                                  8))) : 
                                                                  (((
                                                                    (
                                                                    result_9 =
                                                                    (
                                                                    param_12 +
                                                                    param_11)) /\
                                                                    (
                                                                    result_8 =
                                                                    0)) /\
                                                                   (result_7 =
                                                                   0)) /\
                                                                  (result_6 =
                                                                  ((param_8 +
                                                                   param_11) +
                                                                  ((param_10 <>
                                                                   0) ? 1 : 0))))) : 
           ((((result_9 = param_12) /\ (result_8 = param_11)) /\
            (result_7 = param_10)) /\
           (result_6 = param_8))))]);
          dELTA <- result_9;
          lEN <- result_8;
          tRAIL <- result_7;
          aT <- result_6;
          t64_0 <- result_5;
          w <- (VMOV_64 t64_0);
          b_param_0 <- b_buf;
          param_21 <- buf;
          param_20 <- offset;
          param_19 <- dELTA;
          param_18 <- lEN;
          param_17 <- tRAIL;
          param_16 <- (cUR + 8);
          param_15 <- aT;
          (result_14, result_13, result_12, result_11, result_10, tmp__trace) <@ 
          __a_ilen_read_upto8_at (param_21, b_param_0, param_20, param_19,
          param_18, param_17, param_16, param_15);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++ tmp__trace);
          trace___a_ilen_read_upto16_at <-
          (trace___a_ilen_read_upto16_at ++
          [(Assert,
           (((param_16 <= param_15) /\ (param_15 < (param_16 + 8))) ? 
           ((8 <= ((param_15 - param_16) + param_18)) ? ((((result_14 =
                                                           (param_19 +
                                                           ((param_16 + 8) -
                                                           param_15))) /\
                                                          (result_13 =
                                                          (param_18 -
                                                          ((param_16 + 8) -
                                                          param_15)))) /\
                                                         (result_12 =
                                                         param_17)) /\
                                                        (result_11 =
                                                        (param_16 + 8))) : 
           ((((result_14 = (param_19 + param_18)) /\ (result_13 = 0)) /\
            (result_12 = 0)) /\
           (result_11 = ((param_15 + param_18) + ((param_17 <> 0) ? 1 : 0))))) : 
           ((((result_14 = param_19) /\ (result_13 = param_18)) /\
            (result_12 = param_17)) /\
           (result_11 = param_15))))]);
          dELTA <- result_14;
          lEN <- result_13;
          tRAIL <- result_12;
          aT <- result_11;
          t64_1 <- result_10;
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w, trace___a_ilen_read_upto16_at);
  }
  proc __a_ilen_read_upto32_at (buf:A.t, b_buf:A.t,
                                offset:int, dELTA:int, lEN:int, tRAIL:int,
                                cUR:int, aT:int) : int * int * int * int *
                                                   W256.t * trace = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    var param:int;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:A.t;
    var result:W128.t;
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
    var result_4:W128.t;
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
    var result_9:W128.t;
    var result_10:int;
    var result_11:int;
    var result_12:int;
    var result_13:int;
    var b_param:A.t;
    var b_param_0:A.t;
    var b_param_1:A.t;
    var trace___a_ilen_read_upto32_at:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    param_5 <- witness;
    param_12 <- witness;
    param_19 <- witness;
    trace___a_ilen_read_upto32_at <- [];
    trace___a_ilen_read_upto32_at <-
    (trace___a_ilen_read_upto32_at ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 32) ? lEN : 32)) /\
      (((lEN < 32) ? lEN : 32) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 32) ? lEN : 32))) /\
      (((offset + dELTA) + ((lEN < 32) ? lEN : 32)) <= 18446744073709551615)) /\
     (((((((A.is_init b_buf (offset + dELTA) ((lEN < 32) ? lEN : 32)) /\
          (0 <= dELTA)) /\
         (0 <= offset)) /\
        (((offset + dELTA) + ((lEN < 32) ? lEN : 32)) <= _ASIZE)) /\
       (0 <= lEN)) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256)))))))))]);
    trace___a_ilen_read_upto32_at <-
    (trace___a_ilen_read_upto32_at ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        trace___a_ilen_read_upto32_at <-
        (trace___a_ilen_read_upto32_at ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_read_upto32_at <-
        (trace___a_ilen_read_upto32_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_read_upto32_at <-
        (trace___a_ilen_read_upto32_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 32) <= _ASIZE)))]);
        trace___a_ilen_read_upto32_at <-
        (trace___a_ilen_read_upto32_at ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 32))]);
        w <- (A.get256d buf (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          b_param <- b_buf;
          param_5 <- buf;
          param_4 <- offset;
          param_3 <- dELTA;
          param_2 <- lEN;
          param_1 <- tRAIL;
          param_0 <- (cUR + 16);
          param <- aT;
          (result_3, result_2, result_1, result_0, result, tmp__trace) <@ 
          __a_ilen_read_upto16_at (param_5, b_param, param_4, param_3,
          param_2, param_1, param_0, param);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++ tmp__trace);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++
          [(Assert,
           (((param_0 <= param) /\ (param < (param_0 + 16))) ? ((16 <=
                                                                ((param -
                                                                 param_0) +
                                                                param_2)) ? 
                                                               ((((result_3 =
                                                                  (param_3 +
                                                                  ((param_0 +
                                                                   16) -
                                                                  param))) /\
                                                                 (result_2 =
                                                                 (param_2 -
                                                                 ((param_0 +
                                                                  16) -
                                                                 param)))) /\
                                                                (result_1 =
                                                                param_1)) /\
                                                               (result_0 =
                                                               (param_0 + 16))) : 
                                                               ((((result_3 =
                                                                  (param_3 +
                                                                  param_2)) /\
                                                                 (result_2 =
                                                                 0)) /\
                                                                (result_1 =
                                                                0)) /\
                                                               (result_0 =
                                                               ((param +
                                                                param_2) +
                                                               ((param_1 <>
                                                                0) ? 1 : 0))))) : 
           ((((result_3 = param_3) /\ (result_2 = param_2)) /\
            (result_1 = param_1)) /\
           (result_0 = param))))]);
          dELTA <- result_3;
          lEN <- result_2;
          tRAIL <- result_1;
          aT <- result_0;
          t128_1 <- result;
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          b_param_1 <- b_buf;
          param_12 <- buf;
          param_11 <- offset;
          param_10 <- dELTA;
          param_9 <- lEN;
          param_8 <- tRAIL;
          param_7 <- cUR;
          param_6 <- aT;
          (result_8, result_7, result_6, result_5, result_4, tmp__trace) <@ 
          __a_ilen_read_upto16_at (param_12, b_param_1, param_11, param_10,
          param_9, param_8, param_7, param_6);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++ tmp__trace);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++
          [(Assert,
           (((param_7 <= param_6) /\ (param_6 < (param_7 + 16))) ? ((16 <=
                                                                    (
                                                                    (
                                                                    param_6 -
                                                                    param_7) +
                                                                    param_9)) ? 
                                                                   ((
                                                                    (
                                                                    (
                                                                    result_8 =
                                                                    (
                                                                    param_10 +
                                                                    (
                                                                    (
                                                                    param_7 +
                                                                    16) -
                                                                    param_6))) /\
                                                                    (
                                                                    result_7 =
                                                                    (
                                                                    param_9 -
                                                                    (
                                                                    (
                                                                    param_7 +
                                                                    16) -
                                                                    param_6)))) /\
                                                                    (
                                                                    result_6 =
                                                                    param_8)) /\
                                                                   (result_5 =
                                                                   (param_7 +
                                                                   16))) : 
                                                                   ((
                                                                    (
                                                                    (
                                                                    result_8 =
                                                                    (
                                                                    param_10 +
                                                                    param_9)) /\
                                                                    (
                                                                    result_7 =
                                                                    0)) /\
                                                                    (
                                                                    result_6 =
                                                                    0)) /\
                                                                   (result_5 =
                                                                   ((
                                                                    param_6 +
                                                                    param_9) +
                                                                   ((
                                                                    param_8 <>
                                                                    0) ? 1 : 0))))) : 
           ((((result_8 = param_10) /\ (result_7 = param_9)) /\
            (result_6 = param_8)) /\
           (result_5 = param_6))))]);
          dELTA <- result_8;
          lEN <- result_7;
          tRAIL <- result_6;
          aT <- result_5;
          t128_0 <- result_4;
          w <- (zeroextu256 t128_0);
          b_param_0 <- b_buf;
          param_19 <- buf;
          param_18 <- offset;
          param_17 <- dELTA;
          param_16 <- lEN;
          param_15 <- tRAIL;
          param_14 <- (cUR + 16);
          param_13 <- aT;
          (result_13, result_12, result_11, result_10, result_9, tmp__trace) <@ 
          __a_ilen_read_upto16_at (param_19, b_param_0, param_18, param_17,
          param_16, param_15, param_14, param_13);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++ tmp__trace);
          trace___a_ilen_read_upto32_at <-
          (trace___a_ilen_read_upto32_at ++
          [(Assert,
           (((param_14 <= param_13) /\ (param_13 < (param_14 + 16))) ? 
           ((16 <= ((param_13 - param_14) + param_16)) ? ((((result_13 =
                                                            (param_17 +
                                                            ((param_14 + 16) -
                                                            param_13))) /\
                                                           (result_12 =
                                                           (param_16 -
                                                           ((param_14 + 16) -
                                                           param_13)))) /\
                                                          (result_11 =
                                                          param_15)) /\
                                                         (result_10 =
                                                         (param_14 + 16))) : 
           ((((result_13 = (param_17 + param_16)) /\ (result_12 = 0)) /\
            (result_11 = 0)) /\
           (result_10 = ((param_13 + param_16) + ((param_15 <> 0) ? 1 : 0))))) : 
           ((((result_13 = param_17) /\ (result_12 = param_16)) /\
            (result_11 = param_15)) /\
           (result_10 = param_13))))]);
          dELTA <- result_13;
          lEN <- result_12;
          tRAIL <- result_11;
          aT <- result_10;
          t128_1 <- result_9;
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w, trace___a_ilen_read_upto32_at);
  }
  proc __a_ilen_read_bcast_upto8_at (buf:A.t, b_buf:A.t,
                                     offset:int, dELTA:int, lEN:int,
                                     tRAIL:int, cUR:int, aT:int) : int *
                                                                   int *
                                                                   int *
                                                                   int *
                                                                   W256.t *
                                                                   trace = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    var param:int;
    var param_0:W256.t;
    var result:W256.t;
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
    var b_param:A.t;
    var trace___a_ilen_read_bcast_upto8_at:trace;
    b_param <- witness;
    param_7 <- witness;
    trace___a_ilen_read_bcast_upto8_at <- [];
    trace___a_ilen_read_bcast_upto8_at <-
    (trace___a_ilen_read_bcast_upto8_at ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 8) ? lEN : 8)) /\
      (((lEN < 8) ? lEN : 8) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 8) ? lEN : 8))) /\
      (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= 18446744073709551615)) /\
     (((((((A.is_init b_buf (offset + dELTA) ((lEN < 8) ? lEN : 8)) /\
          (0 <= dELTA)) /\
         (0 <= offset)) /\
        (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= _ASIZE)) /\
       (0 <= lEN)) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256)))))))))]);
    trace___a_ilen_read_bcast_upto8_at <-
    (trace___a_ilen_read_bcast_upto8_at ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++
        [(Assert, (A.is_init b_buf (offset + dELTA) 8))]);
        w256 <- (VPBROADCAST_4u64 (A.get64d buf (offset + dELTA)));
        param_0 <- w256;
        param <- (aT - cUR);
        (result, tmp__trace) <@ M.__SHLQ_256 (param_0, param);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++ tmp__trace);
        w256 <- result;
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        b_param <- b_buf;
        param_7 <- buf;
        param_6 <- offset;
        param_5 <- dELTA;
        param_4 <- lEN;
        param_3 <- tRAIL;
        param_2 <- cUR;
        param_1 <- aT;
        (result_4, result_3, result_2, result_1, result_0, tmp__trace) <@ 
        __a_ilen_read_upto8_at (param_7, b_param, param_6, param_5, param_4,
        param_3, param_2, param_1);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++ tmp__trace);
        trace___a_ilen_read_bcast_upto8_at <-
        (trace___a_ilen_read_bcast_upto8_at ++
        [(Assert,
         (((param_2 <= param_1) /\ (param_1 < (param_2 + 8))) ? ((8 <=
                                                                 ((param_1 -
                                                                  param_2) +
                                                                 param_4)) ? 
                                                                ((((result_4 =
                                                                   (param_5 +
                                                                   ((
                                                                    param_2 +
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
                                                                 (result_2 =
                                                                 0)) /\
                                                                (result_1 =
                                                                ((param_1 +
                                                                 param_4) +
                                                                ((param_3 <>
                                                                 0) ? 1 : 0))))) : 
         ((((result_4 = param_5) /\ (result_3 = param_4)) /\
          (result_2 = param_3)) /\
         (result_1 = param_1))))]);
        dELTA <- result_4;
        lEN <- result_3;
        tRAIL <- result_2;
        aT <- result_1;
        w <- result_0;
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256, trace___a_ilen_read_bcast_upto8_at);
  }
  proc __a_ilen_write_upto8 (buf:A.t, b_buf:A.t, offset:int,
                             dELTA:int, lEN:int, w:W64.t) : A.t *
                                                            A.t *
                                                            int * int * trace = {
    var trace___a_ilen_write_upto8:trace;
    trace___a_ilen_write_upto8 <- [];
    trace___a_ilen_write_upto8 <-
    (trace___a_ilen_write_upto8 ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 8) ? lEN : 8)) /\
      (((lEN < 8) ? lEN : 8) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 8) ? lEN : 8))) /\
      (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= 18446744073709551615)) /\
     (((A.is_init b_buf 0 (offset + dELTA)) /\ (0 <= dELTA)) /\
     (((offset + dELTA) + ((lEN < 8) ? lEN : 8)) <= _ASIZE)))))))))]);
    trace___a_ilen_write_upto8 <-
    (trace___a_ilen_write_upto8 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        trace___a_ilen_write_upto8 <-
        (trace___a_ilen_write_upto8 ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_write_upto8 <-
        (trace___a_ilen_write_upto8 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_write_upto8 <-
        (trace___a_ilen_write_upto8 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
        b_buf <-
        (A.set64d b_buf (offset + dELTA)
        (W64.of_int 18446744073709551615));
        buf <- (A.set64d buf (offset + dELTA) w);
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 4) <= _ASIZE)))]);
          b_buf <-
          (A.set32d b_buf (offset + dELTA) (W32.of_int 4294967295));
          buf <- (A.set32d buf (offset + dELTA) (truncateu32 w));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 2) <= _ASIZE)))]);
          b_buf <-
          (A.set16d b_buf (offset + dELTA) (W16.of_int 65535));
          buf <- (A.set16d buf (offset + dELTA) (truncateu16 w));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_write_upto8 <-
          (trace___a_ilen_write_upto8 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 1) <= _ASIZE)))]);
          b_buf <- (A.set8d b_buf (offset + dELTA) (W8.of_int 255));
          buf <- (A.set8d buf (offset + dELTA) (truncateu8 w));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, b_buf, dELTA, lEN, trace___a_ilen_write_upto8);
  }
  proc __a_ilen_write_upto16 (buf:A.t, b_buf:A.t, offset:int,
                              dELTA:int, lEN:int, w:W128.t) : A.t *
                                                              A.t *
                                                              int * int *
                                                              trace = {
    var t64:W64.t;
    var param:W64.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result:int;
    var result_0:int;
    var result_1:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var trace___a_ilen_write_upto16:trace;
    b_param <- witness;
    b_result <- witness;
    param_3 <- witness;
    result_1 <- witness;
    trace___a_ilen_write_upto16 <- [];
    trace___a_ilen_write_upto16 <-
    (trace___a_ilen_write_upto16 ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 16) ? lEN : 16)) /\
      (((lEN < 16) ? lEN : 16) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 16) ? lEN : 16))) /\
      (((offset + dELTA) + ((lEN < 16) ? lEN : 16)) <= 18446744073709551615)) /\
     (((A.is_init b_buf 0 (offset + dELTA)) /\ (0 <= dELTA)) /\
     (((offset + dELTA) + ((lEN < 16) ? lEN : 16)) <= _ASIZE)))))))))]);
    trace___a_ilen_write_upto16 <-
    (trace___a_ilen_write_upto16 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        trace___a_ilen_write_upto16 <-
        (trace___a_ilen_write_upto16 ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_write_upto16 <-
        (trace___a_ilen_write_upto16 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_write_upto16 <-
        (trace___a_ilen_write_upto16 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 16) <= _ASIZE)))]);
        b_buf <-
        (A.set128d b_buf (offset + dELTA)
        (W128.of_int 340282366920938463463374607431768211455));
        buf <- (A.set128d buf (offset + dELTA) w);
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          trace___a_ilen_write_upto16 <-
          (trace___a_ilen_write_upto16 ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_write_upto16 <-
          (trace___a_ilen_write_upto16 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_write_upto16 <-
          (trace___a_ilen_write_upto16 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 8) <= _ASIZE)))]);
          b_buf <-
          (A.set64d b_buf (offset + dELTA)
          (W64.of_int 18446744073709551615));
          buf <-
          (A.set64d buf (offset + dELTA) (MOVV_64 (truncateu64 w)));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (MOVV_64 (truncateu64 w));
        b_param <- b_buf;
        param_3 <- buf;
        param_2 <- offset;
        param_1 <- dELTA;
        param_0 <- lEN;
        param <- t64;
        (result_1, b_result, result_0, result, tmp__trace) <@ __a_ilen_write_upto8 (
        param_3, b_param, param_2, param_1, param_0, param);
        trace___a_ilen_write_upto16 <-
        (trace___a_ilen_write_upto16 ++ tmp__trace);
        trace___a_ilen_write_upto16 <-
        (trace___a_ilen_write_upto16 ++
        [(Assert,
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (((0 <=
           ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                      param_0 : 8))) /\
          (((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                      param_0 : 8)) <=
          18446744073709551615)) /\
         (((0 <=
           ((param_2 + param_1) +
           ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                      param_0 : 8)))) /\
          (((param_2 + param_1) +
           ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                      param_0 : 8))) <=
          18446744073709551615)) /\
         (((result_0 =
           (param_1 +
           ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                      param_0 : 8)))) /\
          (result =
          (param_0 -
          ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                     param_0 : 8))))) /\
         (A.is_init b_result 0
         ((param_2 + param_1) +
         ((((param_0 < 8) ? param_0 : 8) < 0) ? 0 : ((param_0 < 8) ? 
                                                    param_0 : 8)))
         )))))))]);
        b_buf <- b_result;
        buf <- result_1;
        dELTA <- result_0;
        lEN <- result;
      }
    } else {
      
    }
    return (buf, b_buf, dELTA, lEN, trace___a_ilen_write_upto16);
  }
  proc __a_ilen_write_upto32 (buf:A.t, b_buf:A.t, offset:int,
                              dELTA:int, lEN:int, w:W256.t) : A.t *
                                                              A.t *
                                                              int * int *
                                                              trace = {
    var t128:W128.t;
    var param:W128.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:A.t;
    var result:int;
    var result_0:int;
    var result_1:A.t;
    var b_result:A.t;
    var b_param:A.t;
    var trace___a_ilen_write_upto32:trace;
    b_param <- witness;
    b_result <- witness;
    param_3 <- witness;
    result_1 <- witness;
    trace___a_ilen_write_upto32 <- [];
    trace___a_ilen_write_upto32 <-
    (trace___a_ilen_write_upto32 ++
    [(Assert,
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= dELTA) /\ (dELTA <= 18446744073709551615)) /\
     (((0 <= (offset + dELTA)) /\ ((offset + dELTA) <= 18446744073709551615)) /\
     (((0 <= ((lEN < 32) ? lEN : 32)) /\
      (((lEN < 32) ? lEN : 32) <= 18446744073709551615)) /\
     (((0 <= ((offset + dELTA) + ((lEN < 32) ? lEN : 32))) /\
      (((offset + dELTA) + ((lEN < 32) ? lEN : 32)) <= 18446744073709551615)) /\
     ((((A.is_init b_buf 0 (offset + dELTA)) /\ (0 <= dELTA)) /\
      (0 <= offset)) /\
     (((offset + dELTA) + ((lEN < 32) ? lEN : 32)) <= _ASIZE)))))))))]);
    trace___a_ilen_write_upto32 <-
    (trace___a_ilen_write_upto32 ++
    [(Assert, ((0 <= offset) /\ (offset <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        trace___a_ilen_write_upto32 <-
        (trace___a_ilen_write_upto32 ++
        [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
        trace___a_ilen_write_upto32 <-
        (trace___a_ilen_write_upto32 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\
         ((offset + dELTA) <= 18446744073709551615)))]);
        trace___a_ilen_write_upto32 <-
        (trace___a_ilen_write_upto32 ++
        [(Assert,
         ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 32) <= _ASIZE)))]);
        b_buf <-
        (A.set256d b_buf (offset + dELTA)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        buf <- (A.set256d buf (offset + dELTA) w);
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          trace___a_ilen_write_upto32 <-
          (trace___a_ilen_write_upto32 ++
          [(Assert, ((0 <= dELTA) /\ (dELTA <= 18446744073709551615)))]);
          trace___a_ilen_write_upto32 <-
          (trace___a_ilen_write_upto32 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\
           ((offset + dELTA) <= 18446744073709551615)))]);
          trace___a_ilen_write_upto32 <-
          (trace___a_ilen_write_upto32 ++
          [(Assert,
           ((0 <= (offset + dELTA)) /\ (((offset + dELTA) + 16) <= _ASIZE)))]);
          b_buf <-
          (A.set128d b_buf (offset + dELTA)
          (W128.of_int 340282366920938463463374607431768211455));
          buf <- (A.set128d buf (offset + dELTA) t128);
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        b_param <- b_buf;
        param_3 <- buf;
        param_2 <- offset;
        param_1 <- dELTA;
        param_0 <- lEN;
        param <- t128;
        (result_1, b_result, result_0, result, tmp__trace) <@ __a_ilen_write_upto16 (
        param_3, b_param, param_2, param_1, param_0, param);
        trace___a_ilen_write_upto32 <-
        (trace___a_ilen_write_upto32 ++ tmp__trace);
        trace___a_ilen_write_upto32 <-
        (trace___a_ilen_write_upto32 ++
        [(Assert,
         (((0 <= param_1) /\ (param_1 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_1)) /\
          ((param_2 + param_1) <= 18446744073709551615)) /\
         (((0 <=
           ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                        param_0 : 16))) /\
          (((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                        param_0 : 16)) <=
          18446744073709551615)) /\
         (((0 <=
           ((param_2 + param_1) +
           ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                        param_0 : 16)))) /\
          (((param_2 + param_1) +
           ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                        param_0 : 16))) <=
          18446744073709551615)) /\
         (((result_0 =
           (param_1 +
           ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                        param_0 : 16)))) /\
          (result =
          (param_0 -
          ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                       param_0 : 16))))) /\
         (A.is_init b_result 0
         ((param_2 + param_1) +
         ((((param_0 < 16) ? param_0 : 16) < 0) ? 0 : ((param_0 < 16) ? 
                                                      param_0 : 16)))
         )))))))]);
        b_buf <- b_result;
        buf <- result_1;
        dELTA <- result_0;
        lEN <- result;
      }
    } else {
      
    }
    return (buf, b_buf, dELTA, lEN, trace___a_ilen_write_upto32);
  }
  proc __a_rlen_read_upto8 (a:A.t, b_a:A.t, off:int, len:int) : 
  int * W64.t * trace = {
    var w:W64.t;
    var zf:bool;
    var sh:W8.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var trace___a_rlen_read_upto8:trace;
    trace___a_rlen_read_upto8 <- [];
    trace___a_rlen_read_upto8 <-
    (trace___a_rlen_read_upto8 ++
    [(Assert,
     (((0 <= ((len < 8) ? len : 8)) /\
      (((len < 8) ? len : 8) <= 18446744073709551615)) /\
     (((0 <= (off + ((len < 8) ? len : 8))) /\
      ((off + ((len < 8) ? len : 8)) <= 18446744073709551615)) /\
     (((A.is_init b_a off ((len < 8) ? len : 8)) /\ (0 <= off)) /\
     ((off + ((len < 8) ? len : 8)) <= _ASIZE)))))]);
    trace___a_rlen_read_upto8 <-
    (trace___a_rlen_read_upto8 ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace___a_rlen_read_upto8 <-
    (trace___a_rlen_read_upto8 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    if ((8 <= len)) {
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, (A.is_init b_a off 8))]);
      w <- (A.get64d a off);
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
      off <- (off + 8);
    } else {
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 4) <= _ASIZE)))]);
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, (A.is_init b_a off 4))]);
        w <- (zeroextu64 (A.get32d a off));
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= (off + 4)) /\ ((off + 4) <= 18446744073709551615)))]);
        off <- (off + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 2) <= _ASIZE)))]);
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, (A.is_init b_a off 2))]);
        x <- (zeroextu64 (A.get16d a off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= (off + 2)) /\ ((off + 2) <= 18446744073709551615)))]);
        off <- (off + 2);
        sh <- (sh + (W8.of_int 16));
      } else {
        
      }
      trace___a_rlen_read_upto8 <-
      (trace___a_rlen_read_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 1) <= _ASIZE)))]);
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, (A.is_init b_a off 1))]);
        x <- (zeroextu64 (A.get8d a off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        trace___a_rlen_read_upto8 <-
        (trace___a_rlen_read_upto8 ++
        [(Assert, ((0 <= (off + 1)) /\ ((off + 1) <= 18446744073709551615)))]);
        off <- (off + 1);
      } else {
        
      }
    }
    return (off, w, trace___a_rlen_read_upto8);
  }
  proc __a_rlen_write_upto8 (buf:A.t, b_buf:A.t, off:int,
                             data:W64.t, len:int) : A.t *
                                                    A.t * int * trace = {
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var trace___a_rlen_write_upto8:trace;
    trace___a_rlen_write_upto8 <- [];
    trace___a_rlen_write_upto8 <-
    (trace___a_rlen_write_upto8 ++
    [(Assert,
     (((0 <= ((len < 8) ? len : 8)) /\
      (((len < 8) ? len : 8) <= 18446744073709551615)) /\
     (((0 <= (off + ((len < 8) ? len : 8))) /\
      ((off + ((len < 8) ? len : 8)) <= 18446744073709551615)) /\
     (((A.is_init b_buf 0 off) /\ (0 <= off)) /\
     ((off + ((len < 8) ? len : 8)) <= _ASIZE)))))]);
    trace___a_rlen_write_upto8 <-
    (trace___a_rlen_write_upto8 ++
    [(Assert, ((0 <= off) /\ (off <= 18446744073709551615)))]);
    trace___a_rlen_write_upto8 <-
    (trace___a_rlen_write_upto8 ++
    [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
    if ((8 <= len)) {
      trace___a_rlen_write_upto8 <-
      (trace___a_rlen_write_upto8 ++
      [(Assert, ((0 <= off) /\ ((off + 8) <= _ASIZE)))]);
      b_buf <-
      (A.set64d b_buf off (W64.of_int 18446744073709551615));
      buf <- (A.set64d buf off data);
      trace___a_rlen_write_upto8 <-
      (trace___a_rlen_write_upto8 ++
      [(Assert, ((0 <= (off + 8)) /\ ((off + 8) <= 18446744073709551615)))]);
      off <- (off + 8);
    } else {
      trace___a_rlen_write_upto8 <-
      (trace___a_rlen_write_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 4) <= _ASIZE)))]);
        b_buf <- (A.set32d b_buf off (W32.of_int 4294967295));
        buf <- (A.set32d buf off (truncateu32 data));
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= (off + 4)) /\ ((off + 4) <= 18446744073709551615)))]);
        off <- (off + 4);
        data <- (data `>>` (W8.of_int 32));
      } else {
        
      }
      trace___a_rlen_write_upto8 <-
      (trace___a_rlen_write_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 2) <= _ASIZE)))]);
        b_buf <- (A.set16d b_buf off (W16.of_int 65535));
        buf <- (A.set16d buf off (truncateu16 data));
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= (off + 2)) /\ ((off + 2) <= 18446744073709551615)))]);
        off <- (off + 2);
        data <- (data `>>` (W8.of_int 16));
      } else {
        
      }
      trace___a_rlen_write_upto8 <-
      (trace___a_rlen_write_upto8 ++
      [(Assert, ((0 <= len) /\ (len <= 18446744073709551615)))]);
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= off) /\ ((off + 1) <= _ASIZE)))]);
        b_buf <- (A.set8d b_buf off (W8.of_int 255));
        buf <- (A.set8d buf off (truncateu8 data));
        trace___a_rlen_write_upto8 <-
        (trace___a_rlen_write_upto8 ++
        [(Assert, ((0 <= (off + 1)) /\ ((off + 1) <= 18446744073709551615)))]);
        off <- (off + 1);
      } else {
        
      }
    }
    return (buf, b_buf, off, trace___a_rlen_write_upto8);
  }
}.

(* safety specifications *)

op __a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT =
   hoare [MM.__a_ilen_read_upto8_at :
   (((_aT = aT) /\
    ((_cUR = cUR) /\
    ((_tRAIL = tRAIL) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
    ((_offset = offset) /\ ((_b_buf = b_buf) /\ (_buf = buf)))))))) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 8) ? _lEN : 8)) /\
    (((_lEN < 8) ? _lEN : 8) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8))) /\
    (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((A.is_init _b_buf (_offset + _dELTA) ((_lEN < 8) ? _lEN : 8)
         ) /\
        (0 <= _dELTA)) /\
       (0 <= _offset)) /\
      (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= _ASIZE)) /\
     (0 <= _lEN)) /\
    (0 <= _tRAIL)) /\
   (_tRAIL < 256))))))))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (((_cUR <= _aT) /\ (_aT < (_cUR + 8))) ? ((8 <= ((_aT - _cUR) + _lEN)) ? 
                                             ((((res.`1 =
                                                (_dELTA + ((_cUR + 8) - _aT))) /\
                                               (res.`2 =
                                               (_lEN - ((_cUR + 8) - _aT)))) /\
                                              (res.`3 = _tRAIL)) /\
                                             (res.`4 = (_cUR + 8))) : 
                                             ((((res.`1 = (_dELTA + _lEN)) /\
                                               (res.`2 = 0)) /\
                                              (res.`3 = 0)) /\
                                             (res.`4 =
                                             ((_aT + _lEN) +
                                             ((_tRAIL <> 0) ? 1 : 0))))) : 
    ((((res.`1 = _dELTA) /\ (res.`2 = _lEN)) /\ (res.`3 = _tRAIL)) /\
    (res.`4 = _aT))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`6))].

op __a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT =
   hoare [MM.__a_ilen_read_upto16_at :
   (((_aT = aT) /\
    ((_cUR = cUR) /\
    ((_tRAIL = tRAIL) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
    ((_offset = offset) /\ ((_b_buf = b_buf) /\ (_buf = buf)))))))) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 16) ? _lEN : 16)) /\
    (((_lEN < 16) ? _lEN : 16) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16))) /\
    (((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16)) <=
    18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((A.is_init _b_buf (_offset + _dELTA)
         ((_lEN < 16) ? _lEN : 16)) /\
        (0 <= _dELTA)) /\
       (0 <= _offset)) /\
      (((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16)) <= _ASIZE)) /\
     (0 <= _lEN)) /\
    (0 <= _tRAIL)) /\
   (_tRAIL < 256))))))))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (((_cUR <= _aT) /\ (_aT < (_cUR + 16))) ? ((16 <= ((_aT - _cUR) + _lEN)) ? 
                                              ((((res.`1 =
                                                 (_dELTA +
                                                 ((_cUR + 16) - _aT))) /\
                                                (res.`2 =
                                                (_lEN - ((_cUR + 16) - _aT)))) /\
                                               (res.`3 = _tRAIL)) /\
                                              (res.`4 = (_cUR + 16))) : 
                                              ((((res.`1 = (_dELTA + _lEN)) /\
                                                (res.`2 = 0)) /\
                                               (res.`3 = 0)) /\
                                              (res.`4 =
                                              ((_aT + _lEN) +
                                              ((_tRAIL <> 0) ? 1 : 0))))) : 
    ((((res.`1 = _dELTA) /\ (res.`2 = _lEN)) /\ (res.`3 = _tRAIL)) /\
    (res.`4 = _aT))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`6))].

op __a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT =
   hoare [MM.__a_ilen_read_upto32_at :
   (((_aT = aT) /\
    ((_cUR = cUR) /\
    ((_tRAIL = tRAIL) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
    ((_offset = offset) /\ ((_b_buf = b_buf) /\ (_buf = buf)))))))) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 32) ? _lEN : 32)) /\
    (((_lEN < 32) ? _lEN : 32) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32))) /\
    (((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32)) <=
    18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((A.is_init _b_buf (_offset + _dELTA)
         ((_lEN < 32) ? _lEN : 32)) /\
        (0 <= _dELTA)) /\
       (0 <= _offset)) /\
      (((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32)) <= _ASIZE)) /\
     (0 <= _lEN)) /\
    (0 <= _tRAIL)) /\
   (_tRAIL < 256))))))))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (((_cUR <= _aT) /\ (_aT < (_cUR + 32))) ? ((32 <= ((_aT - _cUR) + _lEN)) ? 
                                              ((((res.`1 =
                                                 (_dELTA +
                                                 ((_cUR + 32) - _aT))) /\
                                                (res.`2 =
                                                (_lEN - ((_cUR + 32) - _aT)))) /\
                                               (res.`3 = _tRAIL)) /\
                                              (res.`4 = (_cUR + 32))) : 
                                              ((((res.`1 = (_dELTA + _lEN)) /\
                                                (res.`2 = 0)) /\
                                               (res.`3 = 0)) /\
                                              (res.`4 =
                                              ((_aT + _lEN) +
                                              ((_tRAIL <> 0) ? 1 : 0))))) : 
    ((((res.`1 = _dELTA) /\ (res.`2 = _lEN)) /\ (res.`3 = _tRAIL)) /\
    (res.`4 = _aT))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`6))].

op __a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT =
   hoare [MM.__a_ilen_read_bcast_upto8_at :
   (((_aT = aT) /\
    ((_cUR = cUR) /\
    ((_tRAIL = tRAIL) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
    ((_offset = offset) /\ ((_b_buf = b_buf) /\ (_buf = buf)))))))) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 8) ? _lEN : 8)) /\
    (((_lEN < 8) ? _lEN : 8) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8))) /\
    (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((((((A.is_init _b_buf (_offset + _dELTA) ((_lEN < 8) ? _lEN : 8)
         ) /\
        (0 <= _dELTA)) /\
       (0 <= _offset)) /\
      (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= _ASIZE)) /\
     (0 <= _lEN)) /\
    (0 <= _tRAIL)) /\
   (_tRAIL < 256))))))))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (((_cUR <= _aT) /\ (_aT < (_cUR + 8))) ? ((8 <= ((_aT - _cUR) + _lEN)) ? 
                                             ((((res.`1 =
                                                (_dELTA + ((_cUR + 8) - _aT))) /\
                                               (res.`2 =
                                               (_lEN - ((_cUR + 8) - _aT)))) /\
                                              (res.`3 = _tRAIL)) /\
                                             (res.`4 = (_cUR + 8))) : 
                                             ((((res.`1 = (_dELTA + _lEN)) /\
                                               (res.`2 = 0)) /\
                                              (res.`3 = 0)) /\
                                             (res.`4 =
                                             ((_aT + _lEN) +
                                             ((_tRAIL <> 0) ? 1 : 0))))) : 
    ((((res.`1 = _dELTA) /\ (res.`2 = _lEN)) /\ (res.`3 = _tRAIL)) /\
    (res.`4 = _aT))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`6))].

op __a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w =
   hoare [MM.__a_ilen_write_upto8 :
   (((_w = w) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 8) ? _lEN : 8)) /\
    (((_lEN < 8) ? _lEN : 8) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8))) /\
    (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((A.is_init _b_buf 0 (_offset + _dELTA)) /\ (0 <= _dELTA)) /\
   (((_offset + _dELTA) + ((_lEN < 8) ? _lEN : 8)) <= _ASIZE)))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
    (((0 <= (_offset + _dELTA)) /\
     ((_offset + _dELTA) <= 18446744073709551615)) /\
    (((0 <= ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))) /\
     (((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8)) <=
     18446744073709551615)) /\
    (((0 <=
      ((_offset + _dELTA) +
      ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8)))) /\
     (((_offset + _dELTA) +
      ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))) <=
     18446744073709551615)) /\
    (((res.`3 =
      (_dELTA +
      ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8)))) /\
     (res.`4 =
     (_lEN - ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))))) /\
    (A.is_init res.`2 0
    ((_offset + _dELTA) +
    ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))))))))))))))))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`5))].

op __a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w =
   hoare [MM.__a_ilen_write_upto16 :
   (((_w = w) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 16) ? _lEN : 16)) /\
    (((_lEN < 16) ? _lEN : 16) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16))) /\
    (((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16)) <=
    18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((A.is_init _b_buf 0 (_offset + _dELTA)) /\ (0 <= _dELTA)) /\
   (((_offset + _dELTA) + ((_lEN < 16) ? _lEN : 16)) <= _ASIZE)))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
    (((0 <= (_offset + _dELTA)) /\
     ((_offset + _dELTA) <= 18446744073709551615)) /\
    (((0 <=
      ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16))) /\
     (((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16)) <=
     18446744073709551615)) /\
    (((0 <=
      ((_offset + _dELTA) +
      ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16)))) /\
     (((_offset + _dELTA) +
      ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16))) <=
     18446744073709551615)) /\
    (((res.`3 =
      (_dELTA +
      ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16)))) /\
     (res.`4 =
     (_lEN -
     ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16))))) /\
    (A.is_init res.`2 0
    ((_offset + _dELTA) +
    ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16))))))))))))))))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`5))].

op __a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w =
   hoare [MM.__a_ilen_write_upto32 :
   (((_w = w) /\
    ((_lEN = lEN) /\
    ((_dELTA = dELTA) /\
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
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
   (((0 <= (_offset + _dELTA)) /\
    ((_offset + _dELTA) <= 18446744073709551615)) /\
   (((0 <= ((_lEN < 32) ? _lEN : 32)) /\
    (((_lEN < 32) ? _lEN : 32) <= 18446744073709551615)) /\
   (((0 <= ((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32))) /\
    (((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32)) <=
    18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   ((((A.is_init _b_buf 0 (_offset + _dELTA)) /\ (0 <= _dELTA)) /\
    (0 <= _offset)) /\
   (((_offset + _dELTA) + ((_lEN < 32) ? _lEN : 32)) <= _ASIZE)))))))))))))))))))))))))))))))))))))))))))) ==>
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
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= _dELTA) /\ (_dELTA <= 18446744073709551615)) /\
    (((0 <= (_offset + _dELTA)) /\
     ((_offset + _dELTA) <= 18446744073709551615)) /\
    (((0 <=
      ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32))) /\
     (((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32)) <=
     18446744073709551615)) /\
    (((0 <=
      ((_offset + _dELTA) +
      ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32)))) /\
     (((_offset + _dELTA) +
      ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32))) <=
     18446744073709551615)) /\
    (((res.`3 =
      (_dELTA +
      ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32)))) /\
     (res.`4 =
     (_lEN -
     ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32))))) /\
    (A.is_init res.`2 0
    ((_offset + _dELTA) +
    ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32))))))))))))))))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`5))].

op __a_rlen_read_upto8_spec _a _b_a _off _len =
   hoare [MM.__a_rlen_read_upto8 :
   (((_len = len) /\ ((_off = off) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
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
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= ((_len < 8) ? _len : 8)) /\
    (((_len < 8) ? _len : 8) <= 18446744073709551615)) /\
   (((0 <= (_off + ((_len < 8) ? _len : 8))) /\
    ((_off + ((_len < 8) ? _len : 8)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((A.is_init _b_a _off ((_len < 8) ? _len : 8)) /\ (0 <= _off)) /\
   ((_off + ((_len < 8) ? _len : 8)) <= _ASIZE)))))))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)))) /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) /\
     (((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)) <=
     18446744073709551615)) /\
    (((0 <=
      (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)))) /\
     ((_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) <=
     18446744073709551615)) /\
    (res.`1 =
    (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))))))))))))))))))))))))))))))) /\
   (valid res.`3))].

op __a_rlen_write_upto8_spec _buf _b_buf _off _data _len =
   hoare [MM.__a_rlen_write_upto8 :
   (((_len = len) /\
    ((_data = data) /\ ((_off = off) /\ ((_b_buf = b_buf) /\ (_buf = buf))))) /\
   ((true /\ (true /\ ((0 <= _len) /\ (_len <= 18446744073709551615)))) /\
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
   (((0 <= 0) /\ (0 <= 18446744073709551615)) /\
   (((0 <= ((_len < 8) ? _len : 8)) /\
    (((_len < 8) ? _len : 8) <= 18446744073709551615)) /\
   (((0 <= (_off + ((_len < 8) ? _len : 8))) /\
    ((_off + ((_len < 8) ? _len : 8)) <= 18446744073709551615)) /\
   (((0 <= _ASIZE) /\ (_ASIZE <= 18446744073709551615)) /\
   (((A.is_init _b_buf 0 _off) /\ (0 <= _off)) /\
   ((_off + ((_len < 8) ? _len : 8)) <= _ASIZE)))))))))))))))))))))))) ==>
   (((true /\ (true /\ ((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)))) /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (true /\
    (((0 <= ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) /\
     (((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)) <=
     18446744073709551615)) /\
    (((0 <=
      (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)))) /\
     ((_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) <=
     18446744073709551615)) /\
    (((0 <= ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) /\
     (((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)) <=
     18446744073709551615)) /\
    (((0 <=
      (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)))) /\
     ((_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))) <=
     18446744073709551615)) /\
    ((A.is_init res.`2 0
     (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8)))) /\
    (res.`3 =
    (_off + ((((_len < 8) ? _len : 8) < 0) ? 0 : ((_len < 8) ? _len : 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))) /\
   (valid res.`4))].

lemma __a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (__a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL
      _cUR _aT).
proof.
rewrite /__a_ilen_read_upto8_at_spec; proc.
inline M.__SHLQ.
sp 3.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    if.
    + (* then *)
      sp 10.
      if.
      + (* then *)
        sp 7.
        if.
        + (* then *)
          sp 12.
          if.
          + (* then *)
            sp 6.
            if.
            + (* then *)
              sp 12.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            sp 5.
            if.
            + (* then *)
              sp 12.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
        + (* else *)
          if.
          + (* then *)
            sp 12.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
      + (* else *)
        sp 6.
        if.
        + (* then *)
          sp 12.
          if.
          + (* then *)
            sp 6.
            if.
            + (* then *)
              sp 12.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            sp 5.
            if.
            + (* then *)
              sp 12.
              if.
              + (* then *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
              + (* else *)
                auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
        + (* else *)
          if.
          + (* then *)
            sp 12.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
    + (* else *)
      sp 1.
      if.
      + (* then *)
        sp 12.
        if.
        + (* then *)
          sp 6.
          if.
          + (* then *)
            sp 12.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
        + (* else *)
          sp 5.
          if.
          + (* then *)
            sp 12.
            if.
            + (* then *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
            + (* else *)
              auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
      + (* else *)
        if.
        + (* then *)
          sp 12.
          if.
          + (* then *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
          + (* else *)
            auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
        + (* else *)
          auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (__a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL
      _cUR _aT).
proof.
rewrite /__a_ilen_read_upto16_at_spec; proc.
inline M.__SHLDQ.
sp 9.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    if.
    + (* then *)
      wp; ecall (__a_ilen_read_upto8_at_proof param_7 b_param param_6 param_5 param_4 param_3 param_2 param_1).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
    + (* else *)
      wp; ecall (__a_ilen_read_upto8_at_proof param_21 b_param_0 param_20 param_19 param_18 param_17 param_16 param_15).
      wp; ecall (__a_ilen_read_upto8_at_proof param_14 b_param_1 param_13 param_12 param_11 param_10 param_9 param_8).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (__a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN _tRAIL
      _cUR _aT).
proof.
rewrite /__a_ilen_read_upto32_at_spec; proc.
sp 9.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    if.
    + (* then *)
      wp; ecall (__a_ilen_read_upto16_at_proof param_5 b_param param_4 param_3 param_2 param_1 param_0 param).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
    + (* else *)
      wp; ecall (__a_ilen_read_upto16_at_proof param_19 b_param_0 param_18 param_17 param_16 param_15 param_14 param_13).
      wp; ecall (__a_ilen_read_upto16_at_proof param_12 b_param_1 param_11 param_10 param_9 param_8 param_7 param_6).
      auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (__a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
rewrite /__a_ilen_read_bcast_upto8_at_spec; proc.
inline M.__SHLQ_256.
sp 5.
if.
+ (* then *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    wp; ecall (__a_ilen_read_upto8_at_proof param_7 b_param param_6 param_5 param_4 param_3 param_2 param_1).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (__a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /__a_ilen_write_upto8_spec; proc.
sp 3.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    if.
    + (* then *)
      sp 8.
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
    + (* else *)
      if.
      + (* then *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
      + (* else *)
        auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (__a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /__a_ilen_write_upto16_spec; proc.
sp 7.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    wp; ecall (__a_ilen_write_upto8_proof param_3 b_param param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (__a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /__a_ilen_write_upto32_spec; proc.
sp 7.
if.
+ (* then *)
  if.
  + (* then *)
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
  + (* else *)
    wp; ecall (__a_ilen_write_upto16_proof param_3 b_param param_2 param_1 param_0 param).
    auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
+ (* else *)
  auto; rewrite /is_init /valid /=; (move=> &hr /> * || move=> &hr /> || move=> /> * || move=> />); rewrite ?List.all_cat /=; try (do 2!(split; try (move=> *; rewrite ?List.all_cat /=))); try done; (try! smt(_ASIZE_ge0 _ASIZE_max)); do ?(split; try (move=> *; rewrite ?List.all_cat /=)); try done; smt(_ASIZE_ge0 _ASIZE_max).
qed.

lemma __a_rlen_read_upto8_proof _a _b_a _off _len :
      (__a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
rewrite /__a_rlen_read_upto8_spec; proc.
auto; rewrite /is_init /valid /= => &m /> *.
case: (8 <= len{m}) => h8; 1: smt().
have hl: 0 <= len{m} < 8 by smt().
rewrite (zf4 _ hl) (zf2 _ hl) (zf1 _ hl) /=.
smt().
qed.

lemma __a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (__a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
rewrite /__a_rlen_write_upto8_spec; proc.
auto; rewrite /is_init /valid /= => &m /> *.
case: (8 <= len{m}) => h8; 1: smt().
have hl: 0 <= len{m} < 8 by smt().
rewrite (zf4 _ hl) (zf2 _ hl) (zf1 _ hl) /=.
smt().
qed.

end ReadWriteArraySafety.
