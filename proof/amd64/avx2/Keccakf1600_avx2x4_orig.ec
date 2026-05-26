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

require import Keccakf1600_avx2x4_generic.
require import Avx2_extra.

op st_inv (_:state) = true.

module Maux = {
 proc p1(st4x2 st4x1: state4x): state4x = {
  st4x1 <- st4x_pack_spec st4x1;
  st4x2 <@ M._keccakf1600_4x_pround(st4x2, st4x1, rOL8.[0], rOL56.[0]);
  st4x2 <- st4x_from_4st (st4x_unpack st4x2);
  return st4x2;
 }
 proc p1_(st4x2 st4x1: state4x): state4x = {
  var r8, r56;
  st4x1 <- st4x_pack_spec st4x1;
  r8 <- rOL8.[0];
  r56 <- rOL56.[0];
  st4x2 <@ M._keccakf1600_4x_pround(st4x2, st4x1, r8, r56);
  st4x2 <- st4x_from_4st (st4x_unpack st4x2);
  return st4x2;
 }
 proc p2(st4x2 st4x1: state4x): state4x = {
  st4x1 <- st4x_unpack_spec st4x1;
  st4x2 <@ p1(st4x2,st4x1);
  st4x2 <- st4x_pack (st4x_to_4st st4x2);
  return st4x2;
 }
 proc p2_(st4x2 st4x1: state4x): state4x = {
  var r8, r56;
  r8 <- rOL8.[0];
  r56 <- rOL56.[0];
  st4x2 <@ M._keccakf1600_4x_pround(st4x2, st4x1, r8, r56);
  return st4x2;
 }
}.

hoare keccak_pround_unpacked_h _st4x:
 Maux.p1:
 st4x1 = _st4x
 ==> (st4x_to_4st res).`1 = keccak_pround_op (st4x_to_4st _st4x).`1
     /\ (st4x_to_4st res).`2 = keccak_pround_op (st4x_to_4st _st4x).`2
     /\ (st4x_to_4st res).`3 = keccak_pround_op (st4x_to_4st _st4x).`3
     /\ (st4x_to_4st res).`4 = keccak_pround_op (st4x_to_4st _st4x).`4.
proof.
proc; inline*; simplify.
time by circuit.
qed.

lemma keccakf1600_4x_pround_ll: islossless M._keccakf1600_4x_pround.
proof. by islossless. qed.

phoare keccak_pround_unpacked_ph _st4x:
 [ Maux.p1
 : st4x1 = _st4x
 ==> (st4x_to_4st res).`1 = keccak_pround_op (st4x_to_4st _st4x).`1
     /\ (st4x_to_4st res).`2 = keccak_pround_op (st4x_to_4st _st4x).`2
     /\ (st4x_to_4st res).`3 = keccak_pround_op (st4x_to_4st _st4x).`3
     /\ (st4x_to_4st res).`4 = keccak_pround_op (st4x_to_4st _st4x).`4
 ] = 1%r.
proof.
have ll: islossless Maux.p1.
 by proc; wp; call keccakf1600_4x_pround_ll; auto.
by conseq ll (keccak_pround_unpacked_h _st4x).
qed.

equiv keccak_pround_avx2x4_eq:
 M._keccakf1600_4x_pround
 ~ Maux.p2
 : a{1} = st4x1{2} /\ e{1}=st4x2{2}
   /\ r8{1} = rOL8.[0] /\ r56{1} = rOL56.[0]
 ==> ={res}.
proof.
proc.
inline*.
by circuit.
qed.

op st4x_keccak_pround =
 st4x_map keccak_pround_op.

phoare keccak_pround_avx2x4_ph _st4x:
 [ M._keccakf1600_4x_pround:
 a = _st4x
 /\ r8 = rOL8.[0] /\ r56 = rOL56.[0]
 ==> res = st4x_keccak_pround _st4x] = 1%r.
proof.
bypr => &m /> -> ->.
have ->:
 Pr[M._keccakf1600_4x_pround(e{m}, a{m}, rOL8.[0], rOL56.[0]) @ &m :
   res = st4x_keccak_pround a{m}]
 = Pr[Maux.p2(e{m}, a{m}) @ &m :
   res = st4x_keccak_pround a{m}].
byequiv keccak_pround_avx2x4_eq => /#.
byphoare (_: st4x1=a{m} ==> _) => //.
proc; simplify.
wp; call (keccak_pround_unpacked_ph (st4x_unpack_spec a{m})).
auto => /> st4x; rewrite /st4x_unpack_spec !st4x_from_4stK /st4x_keccak_pround.
rewrite /st4x_map.
by move=> <- <- <- <- /#.
qed.

hoare keccak_pround_avx2x4_h _st4x:
 M._keccakf1600_4x_pround:
 a = _st4x
 /\ r8 = rOL8.[0] /\ r56 = rOL56.[0]
 ==> res = st4x_keccak_pround _st4x.
proof.
bypr => &m /> -> ->.
have ->:
 Pr[M._keccakf1600_4x_pround(e{m}, a{m}, rOL8.[0], rOL56.[0]) @ &m :
   res <> st4x_keccak_pround a{m}]
 = Pr[Maux.p2(e{m}, a{m}) @ &m :
   res <> st4x_keccak_pround a{m}].
byequiv keccak_pround_avx2x4_eq => /#.
byphoare (_: st4x1=a{m} ==> _) => //.
hoare.
proc; simplify.
wp; ecall (keccak_pround_unpacked_h st4x1).
auto => /> st4x; rewrite /st4x_unpack_spec !st4x_from_4stK /st4x_keccak_pround.
rewrite /st4x_map.
by move=> <- <- <- <- /#.
qed.

(* Mas o que gostava mesmo era de 
 provar o último lema directamente! *)
hoare keccak_pround_avx2x4_h' _st4x:
 M._keccakf1600_4x_pround:
 a = _st4x
 /\ r8 = rOL8.[0] /\ r56 = rOL56.[0]
 ==> res = st4x_keccak_pround _st4x.
proof.
proc; simplify.
(* não consegue lidar com isto... (grande demais?)*)
abort. (*
circuit.
*)

from JazzEC require import Array24.
abbrev keccak_round_i i st =
 foldl (fun s i => keccak_round_op rc_spec.[i] s) st (iota_ 0 i).

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

hoare keccakf1600_avx2x4_orig_h _a:
 M.__keccakf1600_avx2x4_orig :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
while (0 <= c <= 24 /\ c %% 2 = 0 /\
       rC = rc_spec /\
       r8 = rOL8.[0] /\
       r56 = rOL56.[0] /\
       a = st4x_map (keccak_round_i c) _a).
 wp; ecall (keccak_pround_avx2x4_h e).
 wp; ecall (keccak_pround_avx2x4_h a); auto => &m /> Hc1 _ Hc2 Hc; split.
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

lemma keccakf1600_avx2x4_orig_ll: islossless M.__keccakf1600_avx2x4_orig.
proof.
proc.
wp; while (true) (24-c).
 move=> z.
 wp; call keccakf1600_4x_pround_ll.
 by wp; call keccakf1600_4x_pround_ll; auto => /> &m ? /#.
by auto => /#.
qed.

phoare keccakf1600_avx2x4_orig_ph _a:
 [ M.__keccakf1600_avx2x4_orig
 : a = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq keccakf1600_avx2x4_orig_ll (keccakf1600_avx2x4_orig_h _a).
qed.

(*
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

*)
