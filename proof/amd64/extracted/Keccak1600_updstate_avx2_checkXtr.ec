require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require import Array999 WArray999.

require import Keccak1600_updstate_avx2.

clone import KeccakUpdstateAvx2 as A999updstateavx2
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done.

equiv a999_ststatus_data_eq:
 M._ststatus_data ~ MM._ststatus_data
 : ={arg} ==> ={res}
by sim.

equiv a999_add_updstate_avx2_eq:
 M._add_updstate_avx2 ~ MM._add_updstate_avx2
 : ={arg} ==> ={res}
by sim.

equiv a999_dump_updstate_avx2_eq:
 M._dump_updstate_avx2 ~ MM._dump_updstate_avx2
 : ={arg} ==> ={res}
by sim.

equiv a999_update_updstate_avx2_eq:
 M._update_updstate_avx2 ~ MM._update_updstate_avx2
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_updstate_avx2_eq:
 M._squeeze_updstate_avx2 ~ MM._squeeze_updstate_avx2
 : ={arg} ==> ={res}
by sim.
