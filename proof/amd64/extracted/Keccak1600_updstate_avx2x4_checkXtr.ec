require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require import Array999 WArray999.

require import Keccak1600_updstate_avx2x4.

clone import KeccakUpdstateAvx2x4 as A999updstateavx2x4
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done.

equiv a999_ststatus_data_avx2x4_eq:
 M._ststatus_data_avx2x4 ~ MM._ststatus_data_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_add_updstate_avx2x4_eq:
 M._add_updstate_avx2x4 ~ MM._add_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_add_bcast_updstate_avx2x4_eq:
 M._add_bcast_updstate_avx2x4 ~ MM._add_bcast_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_updstate_avx2x4_eq:
 M._absorb_updstate_avx2x4 ~ MM._absorb_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_absorb_bcast_updstate_avx2x4_eq:
 M._absorb_bcast_updstate_avx2x4 ~ MM._absorb_bcast_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_dump_updstate_avx2x4_eq:
 M._dump_updstate_avx2x4 ~ MM._dump_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_updstate_avx2x4_eq:
 M._squeeze_updstate_avx2x4 ~ MM._squeeze_updstate_avx2x4
 : ={arg} ==> ={res}
by sim.
