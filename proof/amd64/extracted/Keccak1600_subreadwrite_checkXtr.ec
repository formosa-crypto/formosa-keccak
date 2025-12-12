require import AllCore IntDiv List.

from Jasmin require import JModel.

(** This script performs a sanity check to verify if the modules
 used for correctness proofs are in sync. with the Jasmin source code *)

from JazzEC require import Keccak1600_Jazz_ASIZE.
from JazzEC require import Array999 WArray999.

require import Keccak1600_subreadwrite.

clone import ReadWriteArray as A999ref
 with op _ASIZE <- 999,
      theory A <- Array999,
      theory WA <- WArray999
      proof _ASIZE_ge0 by done.

equiv a999_a_ilen_read_upto8_at_eq:
 M.__a_ilen_read_upto8_at ~ MM.__a_ilen_read_upto8_at
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_read_upto16_at_eq:
 M.__a_ilen_read_upto16_at ~ MM.__a_ilen_read_upto16_at
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_read_upto32_at_eq:
 M.__a_ilen_read_upto32_at ~ MM.__a_ilen_read_upto32_at
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_read_bcast_upto8_at_eq:
 M.__a_ilen_read_bcast_upto8_at ~ MM.__a_ilen_read_bcast_upto8_at
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_write_upto8_eq:
 M.__a_ilen_write_upto8 ~ MM.__a_ilen_write_upto8
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_write_upto16_eq:
 M.__a_ilen_write_upto16 ~ MM.__a_ilen_write_upto16
 : ={arg} ==> ={res}
by sim.

equiv a999_a_ilen_write_upto32_eq:
 M.__a_ilen_write_upto32 ~ MM.__a_ilen_write_upto32
 : ={arg} ==> ={res}
by sim.

equiv a999_a_rlen_read_upto8_eq:
 M.__a_rlen_read_upto8 ~ MM.__a_rlen_read_upto8
 : ={arg} ==> ={res}
by sim.

equiv a999_a_rlen_write_upto8_eq:
 M.__a_rlen_write_upto8 ~ MM.__a_rlen_write_upto8
 : ={arg} ==> ={res}
by sim.

