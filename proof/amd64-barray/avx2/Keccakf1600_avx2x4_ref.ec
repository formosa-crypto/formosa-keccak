require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.

require import Keccak_bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import BArray3 BArray32 BArray40 BArray160 BArray192 BArray200 BArray208 BArray224 BArray800 BArray808 SBArray208_200 SBArray808_800.
require import Keccak1600_barrays.
require import Keccak_barray_bindings.
from JazzEC require import Array1 Array100 WArray200 WArray800.

require import Avx2_extra.

lemma keccakf1600_4x_pround_ref_ll: islossless M._keccakf1600_4x_pround_ref.
proof. by islossless. qed.


(*pragma +Circuit:timing.*)

hoare keccak_pround_avx2x4_ref_h' _st4x:
 M._keccakf1600_4x_pround_ref:
 st4x a = _st4x
 /\ r8 = BArray32.get256 rOL8 0 /\ r56 = BArray32.get256 rOL56 0
 ==> st4x res = st4x_keccak_pround _st4x.
proof.
proc; simplify.
by circuit.
qed.

from JazzEC require import Array24.

lemma st4x_keccak_roundP2 rc1 rc2 st4x:
 st4x_pack
  ( keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_lane st4x 0))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_lane st4x 1))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_lane st4x 2))
  , keccak_round_op rc2
     (keccak_round_op rc1
        (st4x_lane st4x 3)))
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

lemma st4x_xor0 a w:
 st4x (BArray800.set256d a 0 (w `^` BArray800.get256d a 0)) = (st4x a).[0 <- w `^` (st4x a).[0]].
proof. by rewrite st4x_set256d // st4xE. qed.

hoare __keccakf1600_avx2x4_ref_h _a:
 M.__keccakf1600_avx2x4_ref :
 st4x a = _a
 ==> st4x res = st4x_map keccak_f1600_op _a.
proof.
proc.
while (0 <= c <= 24 /\ c %% 2 = 0 /\
       rC = kECCAK1600_RC /\
       r8 = BArray32.get256 rOL8 0 /\
       r56 = BArray32.get256 rOL56 0 /\
       st4x a = st4x_map (keccak_round_i c) _a).
 wp; ecall (keccak_pround_avx2x4_ref_h' (st4x e)).
 wp; ecall (keccak_pround_avx2x4_ref_h' (st4x a)); auto => &m /> Hc1 _ Hc2 Hst Hc r1 E1 r2.
 rewrite /swap_ /= st4x_xor0 E1 Hst => E2.
 rewrite st4x_xor0 E2 (kECCAK1600_RC_E c{m}) 1:/# (kECCAK1600_RC_E (c{m} + 1)) 1:/#.
 rewrite (:c{m}+2=c{m}+1+1) 1:/#.
 rewrite iotaSr /= 1:/#.
 rewrite iotaSr /= 1:/#.
 rewrite /st4x_map !foldl_rcons /= /swap_.
 pose st0:= (st4x_lane _ _).
 pose st1:= (st4x_lane _ _).
 pose st2:= (st4x_lane _ _).
 pose st3:= (st4x_lane _ _).
 pose st4x1 := (st4x_pack _).
 move: (st4x_keccak_roundP2 rc_spec.[c{m}] rc_spec.[c{m} + 1] st4x1).
 rewrite st4x_get_pack0 st4x_get_pack1 st4x_get_pack2 st4x_get_pack3 /=.
 by move => -> /=; smt().
auto => |> &hr; move: (st4x a{hr}) => sa; split.
 rewrite iota0 //= tP => i Hi.
 rewrite initiE //= (st4x_getiE _ 0) // !st4x_getiE //.
 rewrite u256_pack4E.
 rewrite !bits64E.
 apply W256.ext_eq => k Hk.
 rewrite pack4wE // get_of_list 1:/#.
 smt(W64.initiE). 
by move=> a0 c ????; have ->: c = 24; smt().
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
 : st4x a = _a
 ==> st4x res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq __keccakf1600_avx2x4_ref_ll (__keccakf1600_avx2x4_ref_h _a).
qed.

hoare keccakf1600_avx2x4_ref_h _a:
 M._keccakf1600_avx2x4_ref :
 st4x a = _a
 ==> st4x res = st4x_map keccak_f1600_op _a.
proof. by proc; ecall (__keccakf1600_avx2x4_ref_h (st4x a)). qed.

lemma keccakf1600_avx2x4_ref_ll: islossless M._keccakf1600_avx2x4_ref.
proof. by proc; call __keccakf1600_avx2x4_ref_ll. qed.

