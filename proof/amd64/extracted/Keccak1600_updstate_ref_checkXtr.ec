require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require Keccak1600_Jazz.
from JazzEC require import Array999 WArray999.

require import Keccak1600_updstate_ref.

clone import KeccakUpdstateRef as A999updstateref
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done, _ASIZE_u64 by done.

equiv a999_add_updstate_eq:
 M._add_updstate ~ MM._add_updstate
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_updstate_eq:
 M._absorb_updstate ~ MM._absorb_updstate
 : ={arg} ==> ={res}
by sim.

equiv a999_dump_updstate_eq:
 M._dump_updstate ~ MM._dump_updstate
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_updstate_eq:
 M._squeeze_updstate ~ MM._squeeze_updstate
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_updstate_export_eq:
 M.absorb_updstate ~ MM.absorb_updstate
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_updstate_export_eq:
 M.squeeze_updstate ~ MM.squeeze_updstate
 : ={arg} ==> ={res}
by sim.
