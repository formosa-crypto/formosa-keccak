(******************************************************************************
   Keccak1600_updstate_finish.ec:

   Contracts of the single-lane `_finish_updstate` and of the status export
   `ststatus_updstate` (src/fips202/ref/keccak1600_updstate.jinc), used by
   ref/Keccak1600_updstate_ref.ec.
   (Kept apart from Keccak1600_updstate.ec and from the ref file: the
   low-level finish script is sensitive to the lemmas in scope.)
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.
from Jasmin require import JModel_x86.
from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray208.
from JazzEC require import Array3 Array25 Array26.
from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.
require import Keccak1600_statebytes Keccak1600_subreadwrite Keccak1600_updstate.
import IntOrder.
import BitEncoding.BS2Int.

(* ------------------------------------------------------------------------- *)
(* finish                                                                    *)
(* ------------------------------------------------------------------------- *)

lemma finish_updstate_ll: islossless M._finish_updstate by islossless.

hoare finish_updstate_spec_h _st:
 M._finish_updstate : st = _st ==> res = finish_updstate_spec _st.
proof.
proc. inline.
seq 18: (st = _st /\ 
         (trailb, r8, at) = ststatus_data_spec st.[25]). 
+ auto => />; rewrite /ststatus_data_spec /=; do split. 
  + rewrite /truncateu8 !to_uint_shr ..2:/# of_uintK pmod_small 1:/# of_int_mod /#.
  + rewrite /(\ult) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/#.
    rewrite (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small.
    + rewrite to_uint1 of_uintK to_uint_shr /#.
    rewrite of_uintK to_uint_shr 1:/# to_uint1 !(pmod_small _ W64.modulus) ..3:/#.
    rewrite -of_intD shlMP 1:/# /=. 
    case(200 < (to_uint _st.[25] %/ 256 %% 256 + 1) * 8);
      rewrite of_uintK ?(pmod_small _ W64.modulus) /#. 
  + rewrite /(\ult) /(\ule) of_uintK pmod_small 1:/# shl_shlw 1:/# to_uint_shl 1:/#.
    rewrite (W64.and_mod 8) 1:/# shr_shrw 1:/# to_uintD_small.
    + rewrite to_uint1 of_uintK to_uint_shr /#.
    rewrite of_uintK to_uint_shr 1:/# to_uint1 (W64.and_mod 8) 1:/# of_uintK .
    rewrite !(pmod_small _ W64.modulus) ..4:/#.
    rewrite -of_intD shlMP 1:/# /=.
    case(200 < (to_uint _st.[25] %/ 256 %% 256 + 1) * 8).
    + rewrite of_uintK (pmod_small _ W64.modulus) 1:/#. 
      case(200 <= to_uint _st.[25] %% 256 ) => *; rewrite of_uintK /#.
    + rewrite of_uintK (pmod_small _ W64.modulus) 1:/#. 
      case((to_uint _st.[25]%/256%%256+1)*8 <= to_uint _st.[25]%%256)=> *; rewrite of_uintK /#.
(* Finishing *)
wp. skip. move => &hr /= [#] H0 H1.
rewrite (Array26.ext_eq _ (finish_updstate_spec _st)) 2:/#. move => x x_bnd.
rewrite initE ifT 1:/# /get64_direct /pack8_t /finish_updstate_spec -!H0 -H1 /=.
move: H1. rewrite /ststatus_data_spec /= => [#] H1 H2 H3.
case(x < 25) => state_eq /=.
+ rewrite initE ifT 1:/# /= ifT 1:/#.
 pose a:= (xor_byte_at_st25
   (xor_byte_at_st25 (init ("_.[_]" st{hr})) at{hr} trailb{hr}) (r8{hr} - 1)
   (of_int 128)).[x].
+ rewrite (W64.ext_eq _ a) 2:/# => x0 x0_bnd.
  rewrite /a initE ifT 1:/# /= initE ifT 1:/# /set32_direct /= initE ifT 1:/# /=.
  rewrite initE ifF 1:/# ifT 1:/# /= initE ifT 1:/# /(\bits8) /= initE ifT 1:/# /=.
  rewrite initE ifT 1:/# /= initE ifT 1:/# /init64 /(\bits8) /= get_setE H2 1:/# /=.
  rewrite mulrC (Ring.IntID.mulrC _ x) modzMDl !divzMDl ..2:/# pdiv_small 1:/#.
  rewrite (pdiv_small (x0 %% 8)) 1:/# !addr0.
  case(200 < (to_uint st{hr}.[25] %/ 256 %% 256 + 1) * 8) => H.
  + case(x * 8 + x0 %/ 8 %% 8 = 200 - 1) => H'.
    rewrite /get8 initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= -modzDm -modzMm modz_mod modzMm modzDm -divz_eq /=.
    have->: 56 = 7 * 8 by smt(). rewrite divzMDl 1:/# modzMDl modz_mod addrA /= H3 H /=.
    rewrite get_setE 1:/#. have->: x = 24 by smt().
    case(200 <= to_uint st{hr}.[25] %% 256) => H''.
    + rewrite /= ifF 1:/# initE ifT 1:/# /= initE ifT 1:/# (pdiv_small (x0 %% 8)) 1:/# /=.
      rewrite /xor_byte_at_st25 /= shl_shlw 1:/# /= x0_bnd. 
      have->: 56 + x0 %% 8 = x0 by smt(). have->: x0 %% 8 = x0 - 56 by smt().
      rewrite /=. rewrite /of_int !get_bits2w ..2:/# (int2bs_cat 8 64) 1:/#.
      rewrite !pmod_small ..2:/# pdiv_small 1:/# int2bs0 nth_cat size_int2bs ifT /#.
    + rewrite pdiv_small 1:/# addr0.
      + case(199 = to_uint st{hr}.[25] %% 256) => H'''.
        + rewrite /= initE ifT 1:/# /= -H''' /=.
          rewrite /xor_byte_at_st25 /=  shl_shlw 1:/# /= x0_bnd.
          rewrite /= !shl_shlw 1:/# !shlMP 1:/# /of_int !get_bits2w ..3:/#.
          rewrite eq_sym !int2bs_mod (int2bs_cat 8 64) 1:/# (int2bs_cat 56 64) 1:/# mulrC.
          rewrite nth_cat !size_int2bs ifT 1:/# mulrC mulzK 1:/# mulrC. 
          rewrite int2bs_mulr_pow2 1:/# nth_cat size_cat size_nseq size_int2bs ifF 1:/#.
          rewrite !lez_maxr ..2:/# /=. have->: x0 %% 8 = x0 - 56 by smt().
          rewrite addrA. congr; congr; 1:smt(). rewrite eq_sym -{1}(W8.to_uintK trailb{hr}).
          rewrite /of_int get_bits2w 1:/# pmod_small 2:/#. rewrite H1 of_uintK /#.
        + rewrite /= initE ifT 1:/# /=. case(24 = to_uint st{hr}.[25] %% 256 %/ 8) => H''''.
          + rewrite /xor_byte_at_st25 /= get_setE 1:/# H'''' /= initE ifT 1:/# /=.
            rewrite /= !shl_shlw ..2:/# !shlMP ..2:/# /of_int !get_bits2w ..3:/#.
            rewrite eq_sym !int2bs_mod !(int2bs_cat 56 64) ..2:/# mulrC int2bs_mulr_pow2 1:/#.
            rewrite nth_cat size_cat size_nseq size_int2bs ifF 1:/# mulrC mulzK 1:/# mulrC. 
            rewrite (pdiv_small _ (2^56)). split. rewrite mulr_ge0. rewrite expr_ge0 /#.
            + move: (W8.to_uint_cmp trailb{hr}) => [??]. smt(). move =>*.
            + have->: 2^56 = 2^48 * 2^8 by smt().
              rewrite (ler_lt_trans (2^48 * to_uint trailb{hr})) 1:ler_wpmul2r. 
              + move: (W8.to_uint_cmp trailb{hr}) => /#. rewrite ler_weexpn2l /#. 
                rewrite ltr_pmul2l 1:/#. move: (W8.to_uint_cmp trailb{hr}) => /#.
            rewrite int2bs0 !lez_maxr..2:/# (Ring.IntID.mulrC _ (2^56)) int2bs_mulr_pow2 1:/#.
            rewrite nth_cat size_cat size_nseq size_int2bs ifF 1:/# !lez_maxr ..2:/#.
            rewrite nth_nseq 1:/# /=.
            have->: 56 + x0 %% 8 = x0 by smt(). have->: x0 %% 8 = x0 - 56 by smt(). smt().
          + rewrite /xor_byte_at_st25 /= get_setE 1:/# H'''' /=.
            rewrite /= shl_shlw 1:/# shlMP 1:/# /of_int !get_bits2w ..2:/# !int2bs_mod mulrC.
            rewrite int2bs_mulr_pow2 1:/#nth_cat size_nseq /#.
    + rewrite initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /=.
      rewrite initE ifT 1:/# /= divzMDl 1:/# pdiv_small 1:/# !modzMDl divzMDl 1:/# !modz_mod.
      rewrite (pdiv_small (x0 %% 8)) 1:/# /get8 /= get_setE 1:/#.
      case(8 * x + x0 %/ 8 %% 8 = at{hr}) => H''. 
      + rewrite initE ifT 1:/# /=initE ifT 1:/# /=.
        rewrite /xor_byte_at_st25 /= shl_shlw 1:/# /= initE ifT 1:/# /= !get_setE ..3:/#.
        case(x = 24) => x24.
        + rewrite initE ifT 1:/# /= x0_bnd /=. have->: at{hr} %% 8 * 8 + x0 %% 8 = x0 by smt().
          rewrite shl_shlw 1:/# shlMP 1:/# (Ring.IntID.mulrC _ (2^56)) /of_int int2bs_mod.
          have->: x0 - 8 * (at{hr} %% 8) = x0 %% 8 by smt(). 
          have->: (W64.bits2w (int2bs 64 (2 ^ 56 * 128 %% W64.modulus))).[x0] = false.
          rewrite int2bs_mod int2bs_mulr_pow2 1:/# get_bits2w 1:/# nth_cat nth_nseq 1:/#.
          rewrite size_nseq ifT /#. 
          rewrite /= -{1}(W8.to_uintK trailb{hr}) /of_int (int2bs_cat 8 64) 1:/#.
          rewrite (pdiv_small (W8.to_uint _)) 1:H1 1:/# int2bs0 get_bits2w 1:/# nth_cat.
          rewrite size_int2bs ifT 1:/# int2bs_mod get_bits2w /#.
        + rewrite ifT 1:/# shlMP 1:/# (Ring.IntID.mulrC _ (2^_)) /of_int int2bs_mod /=.
          have->: at{hr} %% 8 * 8 + x0 %% 8 = x0 by smt(). congr. 
          rewrite -H'' (Ring.IntID.mulrC _ x) modzMDl modz_mod int2bs_mulr_pow2 1:/#.
          rewrite get_bits2w 1:/# nth_cat size_nseq ifF 1:/# lez_maxr 1:/#. 
          have->: x0 - 8 * (x0 %/ 8 %% 8) = x0 %% 8 by smt(). 
          rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifT 1:/#.
          rewrite -{1}(to_uintK) /of_int get_bits2w 1:/# int2bs_mod /#.
      + rewrite initE ifT 1:/# /= initE ifT 1:/# /= mulrC divzMDl 1:/# pdiv_small 1:/#.
        rewrite modzMDl modz_mod pmod_small 1:/# -divz_eq /=.
        rewrite /xor_byte_at_st25 /=  shl_shlw 1:/# /=.
        rewrite /= !shl_shlw 1:/# !shlMP ..2:/# initE ifT 1:/# !get_setE ..3:/#.
        case(x = 24) => x24.
        + case(24 = at{hr} %/ 8) => H'''. 
          + rewrite -H''' -x24 (Ring.IntID.mulrC _ (2^56)) {2}/W64.of_int int2bs_mod.
            rewrite int2bs_mulr_pow2 1:/# /=.
            have->: (W64.of_int (to_uint trailb{hr} * 2 ^ (8 * (at{hr} %% 8)))).[x0] = false.
            + rewrite /of_int int2bs_mod get_bits2w 1:/# mulrC int2bs_mulr_pow2 1:/# nth_cat.
              rewrite size_nseq lez_maxr 1:/#. case( x0 < 8 * (at{hr} %% 8)) => Hx. 
              + rewrite nth_nseq /#. rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifF 1:/#.
                rewrite pdiv_small 1:H1 1:/# int2bs0 nth_nseq /#.
            have->: (W64.bits2w (nseq 56 false ++ int2bs 8 128)).[x0] = false. 
            + rewrite get_bits2w 1:/# nth_cat size_nseq ifT 1:/# nth_nseq /#. smt().
          + rewrite initE ifT 1:/# mulrC  /of_int int2bs_mod int2bs_mulr_pow2 1:/# /=.
          +  have->: (W64.bits2w (nseq 56 false ++ int2bs 8 128)).[x0] = false. 
            + rewrite get_bits2w 1:/# nth_cat size_nseq ifT 1:/# nth_nseq /#. smt().
        + case(24 = at{hr} %/ 8) => H'''; 1:rewrite -H''' ifF 1:/# initE ifT /#.
          case(x = at{hr} %/ 8) => ?. rewrite mulrC /of_int int2bs_mod int2bs_mulr_pow2 1:/#/=.
          + rewrite get_bits2w 1:/# nth_cat size_nseq lez_maxr 1:/#. 
            case( x0 < 8 * (at{hr} %% 8)) => Hx.
              + rewrite nth_nseq /#. rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifF 1:/#.
                rewrite (pdiv_small (to_uint trailb{hr})) 1:H1 1:/# int2bs0 nth_nseq /#.
            rewrite initE ifT /#.
  + case(x * 8 + x0 %/ 8 %% 8 = (to_uint st{hr}.[25] %/ 256 %% 256 + 1) * 8 - 1) => H'. 
    + rewrite /get8 initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /=.
      rewrite initE ifT 1:/# !divzMDl ..2:/# modzMDl (pmod_small (x0 %/ 8)) 1:/# -divz_eq /=.
      have->: 56 = 7 * 8 by smt(). rewrite addrA /= H3 H /=.
      rewrite get_setE 1:/#.
      case((to_uint st{hr}.[25] %/ 256 %% 256 + 1) * 8 <= to_uint st{hr}.[25] %% 256) => H''.
      + rewrite /= ifF 1:/# initE ifT 1:/# /= initE ifT 1:/# (pdiv_small (x0 %% 8)) 1:/# /=.
        rewrite /xor_byte_at_st25 /= shl_shlw 1:/# /=. 
        have->: 56 + x0 %% 8 = x0 by smt(). have->: x0 %% 8 = x0 - 56 by smt().
        rewrite u64_shl0 shl_shlw 1:/# shlMP 1:/# mulrC !modzMDl divzMDl 1:/# eq_sym.
        rewrite (Ring.IntID.mulrC _ (2^(8*((-1) %% 8)))) {3}/W64.of_int int2bs_mod.
        rewrite int2bs_mulr_pow2 1:/# /= get_setE 1:/# -H' ifT 1:/# /= get_setE 1:/#.
        rewrite divzMDl 1:/# divz_small 1:/# addr0. 
        have->: to_uint st{hr}.[25] %/ 256 %% 256 = x by smt().
        case(x = 0) => H'''.
        + rewrite /=. have->: (W64.of_int (to_uint trailb{hr})).[x0] = false.
          rewrite /of_int int2bs_mod get_bits2w 1:/# (int2bs_cat 8) 1:/# nth_cat size_int2bs.
          rewrite ifF 1:/# pdiv_small 1:H1 1:/# int2bs0 nth_nseq /#.
          rewrite /of_int /= !get_bits2w ..2:/# nth_cat size_nseq ifF /#.
        + rewrite initE ifT 1:/# /of_int /= !get_bits2w ..2:/# nth_cat size_nseq ifF /#.
      + rewrite (pdiv_small (x0 %% 8)) 1:/# addr0.
        case(8 * (to_uint st{hr}.[25] %/ 256 %% 256) + 7 = to_uint st{hr}.[25] %% 256) => H'''.
        + rewrite initE ifT 1:/# /= initE ifT 1:/# /=. have->: 56 = 7 * 8 by smt(). 
          rewrite modzMDl modz_mod (modz_dvd_pow 3 8 _ 2) 1:/#.
          rewrite /xor_byte_at_st25 /=  shl_shlw 1:/# /=.
            rewrite /= !shl_shlw 1:/# !shlMP ..2:/# initE ifT 1:/# /= !get_setE ..3:/#.
            rewrite !ifT ..2:/# /= eq_sym modzMDl (modz_dvd_pow 3 8 _ 2) 1:/#. 
            rewrite (Ring.IntID.mulrC (to_uint trailb{hr}))  (Ring.IntID.mulrC 128).
            rewrite {1 2}/W64.of_int !int2bs_mod !int2bs_mulr_pow2 ..2:/# !get_bits2w ..2:/#.
            rewrite nth_cat size_nseq ifF 1:/# (int2bs_cat 8) 1:/# nth_cat size_int2bs ifT 1:/#.
            rewrite lez_maxr 1:/#. have->:x0 - 8 * (to_uint st{hr}.[25]%%2^3) = x0 %% 8 by smt().
            rewrite nth_cat size_nseq ifF 1:/# (int2bs_cat 8) 1:/# nth_cat size_int2bs ifT 1:/#.
            rewrite lez_maxr 1:/# /=. have->:x0 - 56 = x0 %% 8 by smt().
            have->: to_uint st{hr}.[25] %% 8 * 8 + x0 %% 8 = x0 by smt().
            rewrite eq_sym -{1}(W8.to_uintK (trailb{hr})) /of_int !get_bits2w ..2:/#.
            rewrite !int2bs_mod /#.
        + rewrite initE ifT 1:/# /= initE ifT 1:/# /=. have->: 56 = 7 * 8 by smt(). 
          rewrite modzMDl modz_mod mulrC divzMDl 1:/# modzMDl /=.
          rewrite /xor_byte_at_st25 /= shl_shlw 1:/# /= !shl_shlw 1:/# !shlMP ..2:/#.
          rewrite initE ifT 1:/# /= !get_setE ..3:/# divzMDl 1:/# /=.
          rewrite ifT 1:/#. have->: 56 + x0 %% 8 = x0 by smt().
          case(to_uint st{hr}.[25] %/ 256 %% 256 = to_uint st{hr}.[25] %% 256 %/ 8) => H''''.
          + rewrite/= eq_sym modzMDl (modz_dvd_pow 3 8 _ 2) 1:/#. 
            rewrite (Ring.IntID.mulrC (to_uint trailb{hr}))  (Ring.IntID.mulrC 128) H''''.
            rewrite {1 2}/W64.of_int !int2bs_mod !int2bs_mulr_pow2 ..2:/# !get_bits2w ..2:/#.
            rewrite nth_cat size_nseq ifF 1:/# (int2bs_cat 8) 1:/# nth_cat size_int2bs ifF 1:/#.
            rewrite (pdiv_small (to_uint trailb{hr})) 1:H1 1:/# int2bs0 nth_cat size_nseq ifF 1:/# nth_nseq 1:/#.
            rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifT 1:/# /= /of_int get_bits2w 1:/#.
            rewrite !int2bs_mod /#.
          + rewrite/= eq_sym modzMDl initE ifT 1:/# /of_int !get_bits2w ..2:/# !int2bs_mod.
            rewrite mulrC int2bs_mulr_pow2 1:/# nth_cat size_nseq ifF 1:/# (int2bs_cat 8) 1:/#.
            rewrite nth_cat size_int2bs ifT /#. 
    + rewrite initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /=.
      rewrite initE ifT 1:/# /= !get_setE 1:/# divzMDl 1:/# divz_small 1:/# !modzMDl.
      rewrite divzMDl 1:/# !modz_mod (pdiv_small (x0%%8)) 1:/# !addr0.
      case(8 * x + x0 %/ 8 %% 8 = at{hr}) => H''.
      + rewrite /get8 initE ifT 1:/# /= initE ifT 1:/# /=.
        have->: at{hr} %% 8 * 8 + x0 %% 8 = x0 by smt().
        rewrite /xor_byte_at_st25 /=  shl_shlw 1:/# /=.
        rewrite /= !shl_shlw 1:/# !shlMP ..2:/# initE ifT 1:/# /= !get_setE ..3:/#.
        rewrite divzMDl 1:/# modzMDl.
        case(x = ((to_uint st{hr}.[25] %/ 256 %% 256 + 1) * 8 - 1) %/ 8) => H''''.
        + rewrite !ifT ..2:/# /of_int mulrC (Ring.IntID.mulrC _ (2^(8 * ((-1) %% 8)))).
          rewrite !int2bs_mod !int2bs_mulr_pow2 ..2:/# /= !get_bits2w ..2:/# !nth_cat.
          rewrite size_nseq ifF 1:/# size_nseq (int2bs_cat 8) 1:/# nth_cat size_int2bs.
          rewrite ifT 1:/# !lez_maxr ..2:/#. have->: x0 - 8*(at{hr}%%8) = x0%%8 by smt(). 
          rewrite ifT 1:/# nth_nseq 1:/# -{1}(W8.to_uintK) /of_int get_bits2w 1:/#.
          rewrite int2bs_mod /#.
        + rewrite ifF 1:/# ifT 1:/# /of_int mulrC int2bs_mod int2bs_mulr_pow2 1:/# /=.
          rewrite get_bits2w 1:/# nth_cat size_nseq ifF 1:/# (int2bs_cat 8) 1:/#.
          rewrite nth_cat size_int2bs ifT 1:/# lez_maxr 1:/#  -{1}(W8.to_uintK) /of_int.
          rewrite get_bits2w 1:/# int2bs_mod /#.
      + rewrite initE ifT 1:/# /= initE ifT 1:/# /= mulrC divzMDl 1:/# pdiv_small 1:/#.
        rewrite modzMDl modz_mod pmod_small 1:/# -divz_eq addr0 /xor_byte_at_st25 /=.
        rewrite shl_shlw 1:/# /= !shl_shlw 1:/# !shlMP ..2:/# initE ifT 1:/# /=.
        rewrite !get_setE ..3:/# divzMDl 1:/# modzMDl divNz ..2:/# div0z add0r -addrA subrr.
        case(x = to_uint st{hr}.[25] %/ 256 %% 256) => H'''.
        + rewrite ifT 1:/#. case(to_uint st{hr}.[25] %/ 256 %% 256 = at{hr} %/ 8) => H''''.
          + rewrite ifT 1:/# /of_int !int2bs_mod mulrC (Ring.IntID.mulrC _ (2^(8*((-1)%%8)))).
            rewrite !int2bs_mulr_pow2 ..2:/# /= !get_bits2w ..2:/# !nth_cat !size_nseq.
            rewrite !lez_maxr ..2:/#. case(x0 < 8 * (at{hr} %% 8)) =>*; rewrite ifT 1:/# /=.            
            + rewrite !nth_nseq /#. rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifF 1:/#.
              rewrite (pdiv_small (to_uint trailb{hr})) 1:H1 1:/# int2bs0 !nth_nseq /#.
          + rewrite initE ifF 1:/# ifT 1:/# mulrC /of_int int2bs_mod int2bs_mulr_pow2 1:/# /=.
            rewrite get_bits2w 1:/# !nth_cat !size_nseq ifT 1:/# nth_nseq /#.
        + rewrite ifF 1:/#. case(x = at{hr} %/ 8) => H''''.
          + rewrite /of_int !int2bs_mod mulrC int2bs_mulr_pow2 1:/# /= get_bits2w 1:/#.
            rewrite nth_cat size_nseq lez_maxr 1:/#. case(x0 < 8 * (at{hr} %% 8)) =>*.            
            + rewrite !nth_nseq /#. rewrite (int2bs_cat 8) 1:/# nth_cat size_int2bs ifF 1:/#.
              rewrite (pdiv_small (to_uint trailb{hr})) 1:H1 1:/# int2bs0 !nth_nseq /#.
          + rewrite initE ifT /#.
move: state_eq. have->: (! x < 25) = (x = 25) by smt(). move => w_eq.
rewrite initE ifT 1:/# /= ifF 1:/#.
+ rewrite (W64.ext_eq _ (clear_at_trailb st{hr}.[25])) 2:/# => x0 x0_bnd.
  rewrite initE ifT 1:/# /= initE ifT 1:/# /= /set32_direct initE ifT 1:/# /=.
  case(x0 < 32) => x0_small. 
  + rewrite ifT 1:/# /get32_direct /pack4_t /(\bits8) /= initE ifT 1:/# /=. 
    rewrite initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= /(\bits8) initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= /init64 /= get_setE 1:/# ifF 1:/# initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /=. rewrite /(\bits8) initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= get_setE 1:/# ifF 1:/# initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= mulrC !modzMDl !divzMDl ..4:/# mulrC divzMDl 1:/#.
    have->: 200 = 25 * 8 by smt(). rewrite divzMDl 1:/# !modzMDl mulrC -addrA w_eq /=.
    rewrite !modz_mod !(pdiv_small (x0%%8)) 1:/# pdiv_small 1:/# !addr0 pdiv_small 1:/#.
    rewrite pdiv_small 1:/# !modz_mod pmod_small 1:/# -divz_eq /=.
    rewrite /clear_at_trailb /of_int int2bs_mod /=. congr. 
    rewrite !get_bits2w ..2:/# (int2bs_cat 32 64) 1:/# nth_cat size_int2bs ifT 1:/#.
    congr. rewrite eq_sym -int2bs_mod /#.
  + rewrite ifF 1:/# /get32_direct /pack4_t /(\bits8) /= initE ifT 1:/# /=. 
    rewrite initE ifT 1:/# /= /(\bits8) initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= /init64 /(\bits8) get_setE 1:/# ifF 1:/# initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /=. rewrite /(\bits8) initE ifT 1:/# /= initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= get_setE 1:/# ifF 1:/# initE ifT 1:/# /=.
    rewrite initE ifT 1:/# /= mulrC !modzMDl !divzMDl ..3:/# mulrC divzMDl 1:/#.
    rewrite !modzMDl mulrC divzMDl 1:/# pdiv_small 1:/# !modzMDl !modz_mod.
    rewrite !(pdiv_small (x0%%8)) 1:/# /= pdiv_small 1:/# modz_mod pdiv_small 1:/#.
    rewrite modz_mod w_eq pmod_small 1:/# -divz_eq /=.
    rewrite /clear_at_trailb /of_int int2bs_mod /=. 
    rewrite !get_bits2w 1:/# (int2bs_cat 32 64) 1:/# nth_cat size_int2bs ifF 1:/#.
    rewrite /=. rewrite (int2bs_cat_nseq_true_false 32) 1:/# nseq0 cats0 nth_nseq /#.
qed.

hoare finish_updstate_h _r8 _tb _l:
 M._finish_updstate
 : absorbing_spec _r8 _tb _l st
 ==> squeezing_spec _r8 (ABSORB1600 _tb _r8 _l) 0 res.
proof.
exlim st => _st.
conseq (finish_updstate_spec_h _st); first by move=> />.
by move=> &hr [#] <- Habs r ->; apply finish_spec_absorbing.
qed.

phoare finish_updstate_ph _r8 _tb _l:
 [ M._finish_updstate
 : absorbing_spec _r8 _tb _l st
 ==> squeezing_spec _r8 (ABSORB1600 _tb _r8 _l) 0 res
 ] = 1%r.
proof. by conseq finish_updstate_ll (finish_updstate_h _r8 _tb _l). qed.

(* ------------------------------------------------------------------------- *)
(* the status export                                                         *)
(* ------------------------------------------------------------------------- *)

lemma ststatus_updstate_ll: islossless M.ststatus_updstate.
proof. islossless. qed.

hoare ststatus_updstate_h _st:
 M.ststatus_updstate
 : st = _st
 ==> W8.to_uint res.[0] = ststatus_r8 _st.[25]
  /\ W8.to_uint res.[1] = ststatus_at_norm _st.[25]
  /\ res.[2] = ststatus_trailb _st.[25].
proof.
proc; wp; ecall (ststatus_data_h ststatus); wp; skip => &hr -> /= r ->; rewrite ststatus_data_specE /=.
have [Hr0 Hr1] : 0 <= ststatus_r8 _st.[25] <= 200 by rewrite /ststatus_r8 /=; smt(W64.to_uint_cmp).
have [Ha0 Ha1] : 0 <= ststatus_at_norm _st.[25] <= 200 by rewrite /ststatus_at_norm /ststatus_r8 /ststatus_at /=; smt(W64.to_uint_cmp).
split; first by rewrite /truncateu8 W8.of_uintK W64.of_uintK; smt(modz_small pow2_64).
split; first by rewrite /truncateu8 W8.of_uintK W64.of_uintK; smt(modz_small pow2_64).
by rewrite /WArray208.get8 /WArray208.init64 WArray208.initiE //= /ststatus_trailb W8u8.bits8_div // /truncateu8 W64.shr_div_le //=.
qed.

phoare ststatus_updstate_ph _st:
 [ M.ststatus_updstate
 : st = _st
 ==> W8.to_uint res.[0] = ststatus_r8 _st.[25]
  /\ W8.to_uint res.[1] = ststatus_at_norm _st.[25]
  /\ res.[2] = ststatus_trailb _st.[25]
 ] = 1%r.
proof. by conseq ststatus_updstate_ll (ststatus_updstate_h _st). qed.
