require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.

require import Keccak_bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array100 WArray200 WArray800.

require import Avx2_extra.
require import Keccakf1600_avx2x4_generic.
require import Keccakf1600_avx2x4_orig.
require import Keccakf1600_avx2x4_native.

hoare keccakf1600_avx2x4_h' _a:
 M.__keccakf1600_avx2x4 :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
(* Choose de appropriate lemma: (orig/native) *)
by ecall (keccakf1600_avx2x4_native_h a).
qed.

lemma keccakf1600_avx2x4_ll': islossless M.__keccakf1600_avx2x4.
proof.
proc.
(* Choose de appropriate lemma: (orig/native) *)
by call keccakf1600_avx2x4_native_ll.
qed.

phoare keccakf1600_avx2x4_ph' _a:
 [ M.__keccakf1600_avx2x4
 : a = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq keccakf1600_avx2x4_ll' (keccakf1600_avx2x4_h' _a).
qed.

lemma keccakf1600_avx2x4_ll: islossless M._keccakf1600_avx2x4.
proof.
by proc; call keccakf1600_avx2x4_ll'.
qed.

(* FINAL CORRECTNESS THEOREM *)
hoare keccakf1600_avx2x4_h _a:
  M._keccakf1600_avx2x4
 : a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
by proc; call (keccakf1600_avx2x4_h' _a).
qed.

phoare keccakf1600_avx2x4_ph _a:
 [ M._keccakf1600_avx2x4
 : a = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof.
by proc; call (keccakf1600_avx2x4_ph' _a).
qed.

