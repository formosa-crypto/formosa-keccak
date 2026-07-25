require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.

require import Keccak_bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array1 Array100 WArray200 WArray800.

require import Avx2_extra.

lemma keccakf1600_4x_pround_ref_ll: islossless M._keccakf1600_4x_pround_ref.
proof. by islossless. qed.


(*pragma +Circuit:timing.*)

hoare keccak_pround_avx2x4_ref_h' _st4x:
 M._keccakf1600_4x_pround_ref:
 a = _st4x
 /\ r8 = rOL8.[0] /\ r56 = rOL56.[0]
 ==> res = st4x_keccak_pround _st4x.
proof.
proc; simplify.
by circuit.
qed.

from JazzEC require import Array24.

lemma st4x_keccak_roundP2 rc1 rc2 st4x:
 st4x_pack
  ( keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_get st4x 0))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_get st4x 1))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_get st4x 2))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_get st4x 3)))
 =  (st4x_keccak_iota rc2
     (st4x_keccak_pround
      (st4x_keccak_iota rc1
       (st4x_keccak_pround st4x)))).
proof.
rewrite -(st4x_unpackK (st4x_keccak_iota _ _)).
rewrite !st4x_keccak_iotaE /keccak_round_op /keccak_iota_op.
rewrite st4x_packK /=.
rewrite tP => i Hi.
rewrite initiE //= eq_sym initiE //=.
rewrite !st4x_get_pack0 /=.
rewrite !st4x_get_pack1 /=.
rewrite !st4x_get_pack2 /=.
by rewrite !st4x_get_pack3 /=.
qed.

hoare __keccakf1600_avx2x4_ref_h _a:
 M.__keccakf1600_avx2x4_ref :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
while (0 <= c <= 24 /\ c %% 2 = 0 /\
       rC = rc_spec /\
       r8 = rOL8.[0] /\
       r56 = rOL56.[0] /\
       a = st4x_map (keccak_round_i c) _a).
 wp; ecall (keccak_pround_avx2x4_ref_h' e).
 wp; ecall (keccak_pround_avx2x4_ref_h' a); auto => &m /> Hc1 _ Hc2 Hc; split.
  smt().
 split.
  smt(). 
 rewrite (:c{m}+2=c{m}+1+1) 1:/#.
 rewrite iotaSr /= 1:/#.
 rewrite iotaSr /= 1:/#.
 rewrite /st4x_map !foldl_rcons /= /swap_.
 pose st0:= (st4x_get _ _).
 pose st1:= (st4x_get _ _).
 pose st2:= (st4x_get _ _).
 pose st3:= (st4x_get _ _).
 pose st4x1 := (st4x_pack _).
 move: (st4x_keccak_roundP2 rc_spec.[c{m}] rc_spec.[c{m} + 1] st4x1).
 rewrite st4x_get_pack0 st4x_get_pack1 st4x_get_pack2 st4x_get_pack3 /=.
 by move => -> /=.
auto => |>; split.
 rewrite iota0 //= tP => i Hi.
 rewrite initiE //= (st4x_getiE _ 0) // !st4x_getiE //.
 rewrite u256_pack4E.
 rewrite !bits64E.
 apply W256.ext_eq => k Hk.
 rewrite pack4wE // get_of_list 1:/#.
 smt(W64.initiE). 
by move=> c ???; have ->: c = 24; smt().
qed.

lemma __keccakf1600_avx2x4_ref_ll: islossless M.__keccakf1600_avx2x4_ref.
proof.
proc.
wp; while (true) (24-c).
 move=> z.
 wp; call keccakf1600_4x_pround_ref_ll.
 by wp; call keccakf1600_4x_pround_ref_ll; auto => /> &m ? /#.
by auto => /#.
qed.

phoare __keccakf1600_avx2x4_ref_ph _a:
 [ M.__keccakf1600_avx2x4_ref
 : a = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq __keccakf1600_avx2x4_ref_ll (__keccakf1600_avx2x4_ref_h _a).
qed.

hoare keccakf1600_avx2x4_ref_h _a:
 M._keccakf1600_avx2x4_ref :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof. by proc; ecall (__keccakf1600_avx2x4_ref_h a). qed.

lemma keccakf1600_avx2x4_ref_ll: islossless M._keccakf1600_avx2x4_ref.
proof. by proc; call __keccakf1600_avx2x4_ref_ll. qed.

