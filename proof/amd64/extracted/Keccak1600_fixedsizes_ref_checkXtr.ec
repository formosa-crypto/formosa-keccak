require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require import Array999 WArray999.

require import Keccak1600_fixedsizes_ref.

clone import KeccakArrayRef as A999ref
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done.

equiv a999_addstate_ref_eq:
 M.__addstate_ref ~ MM.__addstate_ref
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_ref_eq:
 M.__absorb_ref ~ MM.__absorb_ref
 : ={arg} ==> ={res}
by sim.

equiv a999_dumpstate_ref_eq:
 M.__dumpstate_ref ~ MM.__dumpstate_ref
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_ref_eq:
 M.__squeeze_ref ~ MM.__squeeze_ref
 : ={arg} ==> ={res}
by sim.

