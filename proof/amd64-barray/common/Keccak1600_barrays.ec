(******************************************************************************
   Keccak1600_barrays.ec:

   Views from the jasmin2ec `barray` representation (monomorphic byte arrays
   BArrayN) to the word arrays used by the specification (and by the
   array-level lemmas shared with the old extraction model).

   Contracts over extracted procedures are stated through these views:
     st25 st = _st ==> st25 res = f _st
******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86 JByte_array.

from CryptoSpecs require import FIPS202_Keccakf1600.

from JazzEC require import Array5 Array7 Array25.
from JazzEC require import BArray40 BArray192 BArray200 BArray208 BArray224
                           BArray800 BArray808 SBArray208_200 SBArray808_800.

(* 25-lane state: BArray200 <-> W64.t Array25.t (= state) *)
op st25 (a: BArray200.t) : state = Array25.init (BArray200.get64 a).
op st200 (s: state) : BArray200.t =
 BArray200.init (fun i => s.[i %/ 8] \bits8 (i %% 8)).

(* 5-lane column buffer (ref permutation): BArray40 <-> W64.t Array5.t *)
op st5 (c: BArray40.t) : W64.t Array5.t = Array5.init (BArray40.get64 c).

(* AVX2 (1-way) packed state: BArray224 <-> W256.t Array7.t *)
op stavx2 (a: BArray224.t) : W256.t Array7.t = Array7.init (BArray224.get256 a).

(* AVX2 4-way interleaved state: BArray800 <-> W256.t Array25.t (state4x) *)
op st4x (a: BArray800.t) : W256.t Array25.t = Array25.init (BArray800.get256 a).
(* lane [k] (0<=k<4) of the 4-way state, as a 25-lane state *)
op st4x_get (a: BArray800.t) (k: int) : state =
 Array25.init (fun i => BArray800.get64 a (4*i + k)).

(* updstate (ref): u64[26] = state ++ status word *)
op ust_state (st: BArray208.t) : state = Array25.init (BArray208.get64 st).
abbrev ust_status (st: BArray208.t) = BArray208.get64 st 25.

(* updstate (4-way): u64[101] = state4x ++ status word *)
op ust_st4x (st: BArray808.t) : W256.t Array25.t =
 Array25.init (BArray808.get256 st).
abbrev ust4x_status (st: BArray808.t) = BArray808.get64 st 100.
