(******************************************************************************
   Keccak1600_imem_avx2.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

require import WArray768.
from JazzEC require import Jazz_avx2.

require import Array4 Array5 Array7 Array24 Array25.

from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

(*
addstate_imem_avx2
*)
lemma addstate_imem_avx2_ll: islossless M.__addstate_imem_avx2
 by islossless.

hoare addstate_imem_avx2_h _st _buf _len _trailb:
 M.__addstate_imem_avx2
 : st=_st /\ buf=_buf /\ lEN=_len /\ tRAILB=_trailb
 ==> true.
proof.
admit.
qed.

(*
absorb_imem_avx2
*)
lemma absorb_imem_avx2_ll: islossless M.__absorb_imem_avx2.
proof.
proc*.
admit.
qed.

hoare absorb_imem_avx2_h _st _buf _len _r8 _trailb:
 M.__absorb_imem_avx2
 : st=_st /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_trailb
 ==> true.
admit.
qed.


(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ======================================
*)

(*
pstate_imem_avx2
*)
lemma pstate_imem_avx2_ll: islossless M.__pstate_imem_avx2.
admitted.

hoare pstate_imem_avx2_h _pst _at _buf _len _trailb:
 M.__pstate_imem_avx2
 : pst=_pst /\ aT=_at /\ buf=_buf /\ lEN=_len /\ tRAILB=_trailb
 ==> true.
admitted.

(*
pabsorb_imem_avx2
*)
lemma pabsorb_imem_avx2_ll: islossless M.__pabsorb_imem_avx2.
admitted.

hoare pabsorb_imem_avx2_h _pst _at _st _buf _len _r8 _trailb:
 M.__pabsorb_imem_avx2
 : pst=_pst /\ aT=_at /\ st=_st /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_trailb
 ==> true.
admitted.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

(*
dumpstate_imem_avx2
*)
lemma dumpstate_imem_avx2_ll: islossless M.__dumpstate_imem_avx2
 by islossless.

hoare dumpstate_imem_avx2_h _buf _len _st:
 M.__dumpstate_imem_avx2
 : buf=_buf /\ lEN=_len /\ st=_st
 ==> true.
admitted.

(*
squeeze_imem_avx2
*)
lemma squeeze_imem_avx2_ll: islossless M.__squeeze_imem_avx2.
admitted.

hoare squeeze_imem_avx2_h _buf _len _st _r8:
 M.__squeeze_imem_avx2
 : buf=_buf /\ lEN=_len /\ st=_st /\ rATE8=_r8
 ==> true.
admitted.
