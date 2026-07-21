(******************************************************************************
   Keccakf1600.ec:

   Correctness proof for the Keccak Permutation implementation
******************************************************************************)
require import List Real Int IntDiv List CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array5 Array24 Array25.

require import Keccakf1600_ref.
require import Keccakf1600_basic.

import BitEncoding.BitChunking.


hoare keccakf1600_h _a:
 M._keccakf1600 :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc.
seq 1: #pre; first by inline*; auto => />.
if => //.
 admit (* opt *).
if => //.
 by ecall (keccakf1600_basic_h _a).
if => //.
 admit (* st25avx2 *).
by ecall (keccakf1600_ref_h _a).
qed.

lemma keccakf1600_ll: islossless M._keccakf1600.
proof.
proc.
inline __KECCAK_F.
sp; if => //.
 admit (* opt *).
if => //.
 by call keccakf1600_basic_ll.
if => //.
 admit (* st25avx2 *).
by call keccakf1600_ref_ll.
qed.

phoare keccakf1600_ph _a:
 [ M._keccakf1600
 : a = _a
 ==> res = keccak_f1600_op _a
 ] = 1%r.
proof. by conseq keccakf1600_ll (keccakf1600_h _a). qed.

