require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require import Array999 WArray999.

require import Keccak1600_fixedsizes_avx2x4.

clone import KeccakArrayAvx2x4 as A999avx2x4
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done.

equiv a999_addstate_bcast_avx2x4_eq:
 M.__addstate_bcast_avx2x4 ~ MM.__addstate_bcast_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_addstate_avx2x4_eq:
 M.__addstate_avx2x4 ~ MM.__addstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_bcast_avx2x4_eq:
 M.__absorb_bcast_avx2x4 ~ MM.__absorb_bcast_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_avx2x4_eq:
 M.__absorb_avx2x4 ~ MM.__absorb_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_dumpstate_avx2_eq:
 M.__dumpstate_avx2x4 ~ MM.__dumpstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_avx2x4_eq:
 M.__squeeze_avx2x4 ~ MM.__squeeze_avx2x4
 : ={arg} ==> ={res}
by sim.

