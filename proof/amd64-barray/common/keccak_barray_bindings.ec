(* ==================================================================== *)
(* Circuit bindings for the byte arrays of the barray extraction        *)
(* (Keccak1600_Jazz.ec), and for the views of Keccak1600_barrays.ec.    *)
(*                                                                      *)
(* - one [BArrayBS] clone per array size (bitstring view, get8, set8);  *)
(* - one [GetSetK] clone per (array size, word size) that fits;         *)
(* - one [SubBArrayBS] clone per sub-array theory;                      *)
(* - the views [st25], [st5], [stavx2], [st4x] (and the inverses        *)
(*   [st200], [stavx2_of], [st4x_of]) as "b2a" / "a2b": a view is a     *)
(*   reinterpretation of the same bits, so [circuit] sees through it    *)
(*   without unfolding;                                                 *)
(* - [ArrayN.init] as "painit", for the remaining views                 *)
(*   ([st4x_get], [ust_state], ...).                                    *)
(* ==================================================================== *)
require import AllCore List IntDiv QFABV.
from Jasmin require import JModel_x86 JByte_array.
require import Keccak_bindings Barray_abs_bindings.
from JazzEC require import Array5 Array7 Array24 Array25.
from JazzEC require import BArray3 BArray32 BArray40 BArray160 BArray192 BArray200
                           BArray208 BArray224 BArray800 BArray808
                           SBArray208_200 SBArray808_800.
require import Keccak1600_barrays.

(* -------------------------------------------------------------------- *)
(* Byte arrays.                                                         *)
clone BArrayBS as BArray3BS with theory BA <- BArray3 proof gt0_size by done.
clone BArrayBS as BArray32BS with theory BA <- BArray32 proof gt0_size by done.
clone BArrayBS as BArray40BS with theory BA <- BArray40 proof gt0_size by done.
clone BArrayBS as BArray160BS with theory BA <- BArray160 proof gt0_size by done.
clone BArrayBS as BArray192BS with theory BA <- BArray192 proof gt0_size by done.
clone BArrayBS as BArray200BS with theory BA <- BArray200 proof gt0_size by done.
clone BArrayBS as BArray208BS with theory BA <- BArray208 proof gt0_size by done.
clone BArrayBS as BArray224BS with theory BA <- BArray224 proof gt0_size by done.
clone BArrayBS as BArray800BS with theory BA <- BArray800 proof gt0_size by done.
clone BArrayBS as BArray808BS with theory BA <- BArray808 proof gt0_size by done.

(* -------------------------------------------------------------------- *)
(* Word accesses.                                                       *)
clone BArray3BS.GetSet16 as BArray3_16 proof le_size by done.
clone BArray32BS.GetSet16 as BArray32_16 proof le_size by done.
clone BArray32BS.GetSet32 as BArray32_32 proof le_size by done.
clone BArray32BS.GetSet64 as BArray32_64 proof le_size by done.
clone BArray32BS.GetSet128 as BArray32_128 proof le_size by done.
clone BArray32BS.GetSet256 as BArray32_256 proof le_size by done.
clone BArray40BS.GetSet16 as BArray40_16 proof le_size by done.
clone BArray40BS.GetSet32 as BArray40_32 proof le_size by done.
clone BArray40BS.GetSet64 as BArray40_64 proof le_size by done.
clone BArray40BS.GetSet128 as BArray40_128 proof le_size by done.
clone BArray40BS.GetSet256 as BArray40_256 proof le_size by done.
clone BArray160BS.GetSet16 as BArray160_16 proof le_size by done.
clone BArray160BS.GetSet32 as BArray160_32 proof le_size by done.
clone BArray160BS.GetSet64 as BArray160_64 proof le_size by done.
clone BArray160BS.GetSet128 as BArray160_128 proof le_size by done.
clone BArray160BS.GetSet256 as BArray160_256 proof le_size by done.
clone BArray192BS.GetSet16 as BArray192_16 proof le_size by done.
clone BArray192BS.GetSet32 as BArray192_32 proof le_size by done.
clone BArray192BS.GetSet64 as BArray192_64 proof le_size by done.
clone BArray192BS.GetSet128 as BArray192_128 proof le_size by done.
clone BArray192BS.GetSet256 as BArray192_256 proof le_size by done.
clone BArray200BS.GetSet16 as BArray200_16 proof le_size by done.
clone BArray200BS.GetSet32 as BArray200_32 proof le_size by done.
clone BArray200BS.GetSet64 as BArray200_64 proof le_size by done.
clone BArray200BS.GetSet128 as BArray200_128 proof le_size by done.
clone BArray200BS.GetSet256 as BArray200_256 proof le_size by done.
clone BArray208BS.GetSet16 as BArray208_16 proof le_size by done.
clone BArray208BS.GetSet32 as BArray208_32 proof le_size by done.
clone BArray208BS.GetSet64 as BArray208_64 proof le_size by done.
clone BArray208BS.GetSet128 as BArray208_128 proof le_size by done.
clone BArray208BS.GetSet256 as BArray208_256 proof le_size by done.
clone BArray224BS.GetSet16 as BArray224_16 proof le_size by done.
clone BArray224BS.GetSet32 as BArray224_32 proof le_size by done.
clone BArray224BS.GetSet64 as BArray224_64 proof le_size by done.
clone BArray224BS.GetSet128 as BArray224_128 proof le_size by done.
clone BArray224BS.GetSet256 as BArray224_256 proof le_size by done.
clone BArray800BS.GetSet16 as BArray800_16 proof le_size by done.
clone BArray800BS.GetSet32 as BArray800_32 proof le_size by done.
clone BArray800BS.GetSet64 as BArray800_64 proof le_size by done.
clone BArray800BS.GetSet128 as BArray800_128 proof le_size by done.
clone BArray800BS.GetSet256 as BArray800_256 proof le_size by done.
clone BArray808BS.GetSet16 as BArray808_16 proof le_size by done.
clone BArray808BS.GetSet32 as BArray808_32 proof le_size by done.
clone BArray808BS.GetSet64 as BArray808_64 proof le_size by done.
clone BArray808BS.GetSet128 as BArray808_128 proof le_size by done.
clone BArray808BS.GetSet256 as BArray808_256 proof le_size by done.

(* -------------------------------------------------------------------- *)
(* Sub-arrays.                                                          *)
clone SubBArrayBS as SBArray208_200BS with
  theory SBA <- SBArray208_200, theory BigBS <- BArray208BS, theory SmallBS <- BArray200BS
proof le_size by done.

clone SubBArrayBS as SBArray808_800BS with
  theory SBA <- SBArray808_800, theory BigBS <- BArray808BS, theory SmallBS <- BArray800BS
proof le_size by done.

(* -------------------------------------------------------------------- *)
(* Polymorphic array init.                                              *)
bind op [Array5.t] Array5.init "painit".
realize bvpainitP.
proof. by move=> f; rewrite /Array5.to_list; apply eq_in_mkseq => i hi /=; rewrite Array5.initiE. qed.

bind op [Array7.t] Array7.init "painit".
realize bvpainitP.
proof. by move=> f; rewrite /Array7.to_list; apply eq_in_mkseq => i hi /=; rewrite Array7.initiE. qed.

bind op [Array24.t] Array24.init "painit".
realize bvpainitP.
proof. by move=> f; rewrite /Array24.to_list; apply eq_in_mkseq => i hi /=; rewrite Array24.initiE. qed.

bind op [Array25.t] Array25.init "painit".
realize bvpainitP.
proof. by move=> f; rewrite /Array25.to_list; apply eq_in_mkseq => i hi /=; rewrite Array25.initiE. qed.

(* -------------------------------------------------------------------- *)
(* Views.                                                               *)
lemma to_list_st25w a : Array25.to_list (st25 a) = mkseq (fun i => BArray200.get64 a i) 25.
proof. by rewrite /Array25.to_list; apply eq_in_mkseq => i hi /=; rewrite st25E. qed.

lemma to_list_st5w c : Array5.to_list (st5 c) = mkseq (fun i => BArray40.get64 c i) 5.
proof. by rewrite /Array5.to_list; apply eq_in_mkseq => i hi /=; rewrite st5E. qed.

lemma to_list_stavx2w a : Array7.to_list (stavx2 a) = mkseq (fun i => BArray224.get256 a i) 7.
proof. by rewrite /Array7.to_list; apply eq_in_mkseq => i hi /=; rewrite stavx2E. qed.

lemma to_list_st4xw a : Array25.to_list (st4x a) = mkseq (fun i => BArray800.get256 a i) 25.
proof. by rewrite /Array25.to_list; apply eq_in_mkseq => i hi /=; rewrite st4xE. qed.

bind op [BArray200.t & W64.t & Array25.t] st25 "b2a".
realize size_ok by done.
realize b2aP by move=> a; rewrite to_list_st25w (BArray200_64.tobits_get64 a 25).

bind op [BArray200.t & W64.t & Array25.t] st200 "a2b".
realize size_ok by done.
realize a2bP by move=> s; rewrite (BArray200_64.tobits_get64 _ 25) // -to_list_st25w st200K.

bind op [BArray40.t & W64.t & Array5.t] st5 "b2a".
realize size_ok by done.
realize b2aP by move=> c; rewrite to_list_st5w (BArray40_64.tobits_get64 c 5).

bind op [BArray224.t & W256.t & Array7.t] stavx2 "b2a".
realize size_ok by done.
realize b2aP by move=> a; rewrite to_list_stavx2w (BArray224_256.tobits_get256 a 7).

bind op [BArray224.t & W256.t & Array7.t] stavx2_of "a2b".
realize size_ok by done.
realize a2bP by move=> s; rewrite (BArray224_256.tobits_get256 _ 7) // -to_list_stavx2w stavx2_ofK.

bind op [BArray800.t & W256.t & Array25.t] st4x "b2a".
realize size_ok by done.
realize b2aP by move=> a; rewrite to_list_st4xw (BArray800_256.tobits_get256 a 25).

bind op [BArray800.t & W256.t & Array25.t] st4x_of "a2b".
realize size_ok by done.
realize a2bP by move=> s; rewrite (BArray800_256.tobits_get256 _ 25) // -to_list_st4xw st4x_ofK.
