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

equiv a999_addstate_eq:
 M.__addstate ~ MM.__addstate
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_eq:
 M.__absorb ~ MM.__absorb
 : ={arg} ==> ={res}
by sim.

equiv a999_dumpstate_eq:
 M.__dumpstate ~ MM.__dumpstate
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_eq:
 M.__squeeze ~ MM.__squeeze
 : ={arg} ==> ={res}
by sim.

