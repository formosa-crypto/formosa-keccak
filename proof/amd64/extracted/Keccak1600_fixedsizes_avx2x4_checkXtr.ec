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

(* The ASIZE extraction instantiates KECCAK_PERMUTATION with a different
   scalar component (3+512, from toEC_keccak1600_avx2.jazz) than the memory
   extraction (2+512, the default): the x4 dispatcher masks the scalar byte
   out, so both dispatch identically, but [sim] cannot see through the
   distinct literals.  The lemma below bridges the two dispatchers, and is
   passed as a hint to [sim] in the equivalences that use the permutation. *)
equiv a999_keccakf1600_avx2x4_eq:
 M._keccakf1600_avx2x4 ~ Keccak1600_Jazz.M._keccakf1600_avx2x4
 : ={arg} ==> ={res}.
proof.
proc.
seq 1 1: (={a} /\ ={kECCAK_F}).
 by inline*; auto => />; congr; circuit.
if => //; first by sim.
if => //; first by sim.
by sim.
qed.

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
 : ={arg} ==> ={res}.
proof.
proc.
sim (M._keccakf1600_avx2x4 ~ Keccak1600_Jazz.M._keccakf1600_avx2x4 : true).
by conseq a999_keccakf1600_avx2x4_eq.
qed.

equiv a999_absorb_avx2x4_eq:
 M.__absorb_avx2x4 ~ MM.__absorb_avx2x4
 : ={arg} ==> ={res}.
proof.
proc.
sim (M._keccakf1600_avx2x4 ~ Keccak1600_Jazz.M._keccakf1600_avx2x4 : true).
by conseq a999_keccakf1600_avx2x4_eq.
qed.

equiv a999_dumpstate_avx2_eq:
 M.__dumpstate_avx2x4 ~ MM.__dumpstate_avx2x4
 : ={arg} ==> ={res}
by sim.

equiv a999_squeeze_avx2x4_eq:
 M.__squeeze_avx2x4 ~ MM.__squeeze_avx2x4
 : ={arg} ==> ={res}.
proof.
proc.
sim (M._keccakf1600_avx2x4 ~ Keccak1600_Jazz.M._keccakf1600_avx2x4 : true).
by conseq a999_keccakf1600_avx2x4_eq.
qed.

