(******************************************************************************
   Keccakf1600_ref.ec:

   Correctness proof for the Keccak BASIC implementation
******************************************************************************)
require import List Real Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array5 Array24 Array25.

require import Keccak_bindings.

require import Keccakf1600_ref.

op complement_lane i (st: W64.t Array25.t) =
 st.[i <- invw st.[i]].

op complement_lanes st =
 foldr complement_lane st [1; 2; 8; 12; 17; 20].

lemma complement_lanesI st:
 complement_lanes (complement_lanes st) = st
by circuit.

op keccak_pround_complement_lanes_op st =
 complement_lanes (keccak_pround_op (complement_lanes st)).

lemma complement_lanes_basic_ll: islossless M.__complement_lanes_basic
by islossless.

hoare complement_lanes_basic_h _a:
 M.__complement_lanes_basic
 : st=_a ==> res = complement_lanes _a.
proof.
proc; inline*.
cfold 32; cfold 26; cfold 20; cfold 14; cfold 8; cfold 2.
by wp 30; circuit.
qed.

lemma keccakf1600_pround_basic_ll: islossless  M.__pround_basic_inlined
by islossless.

hoare keccakf1600_pround_basic_h _a:
 M.__pround_basic_inlined
 : a=_a ==> res = keccak_pround_complement_lanes_op _a.
proof.
proc; simplify.
proc change 29: { t684 <- x682 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 33: { t689 <- x687 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 37: { t694 <- x692 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 41: { t699 <- x697 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 45: { t704 <- x702 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 52: { b1720 <- x717 `|<<<|` 44; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 55: { b2728 <- x725 `|<<<|` 43; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 58: { b3736 <- x733 `|<<<|` 21; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 61: { b4744 <- x741 `|<<<|` 14; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 85: { t767 <- x765 `|<<<|` 28; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 88: { b1776 <- x773 `|<<<|` 20; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 91: { b2784 <- x781 `|<<<|` 3; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 94: { b3792 <- x789 `|<<<|` 45; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 97: { b4800 <- x797 `|<<<|` 61; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 121: { b0824 <- x821 `|<<<|` 1; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 124: { b1832 <- x829 `|<<<|` 6; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 127: { b2840 <- x837 `|<<<|` 25; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 130: { b3848 <- x845 `|<<<|` 8; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 133: { b4856 <- x853 `|<<<|` 18; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 159: { b0882 <- x879 `|<<<|` 27; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 162: { b1890 <- x887 `|<<<|` 36; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 165: { b2898 <- x895 `|<<<|` 10; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 168: { b3906 <- x903 `|<<<|` 15; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 171: { b4914 <- x911 `|<<<|` 56; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 197: { b0940 <- x937 `|<<<|` 62; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 200: { b1948 <- x945 `|<<<|` 55; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 203: { b2956 <- x953 `|<<<|` 39; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 206: { b3964 <- x961 `|<<<|` 41; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
proc change 209: { b4972 <- x969 `|<<<|` 2; }; first by (auto => /> &m; rewrite /ROL_64 /=; circuit).
circuit.
qed.


op keccak_round_complement_lanes_op (c : W64.t) (A : state) : W64.t Array25.t =
  keccak_iota_op c (keccak_pround_complement_lanes_op A).

lemma keccak_iota_complement_lanes c A:
 keccak_iota_op c (keccak_pround_complement_lanes_op A)
 = complement_lanes (keccak_iota_op c (keccak_pround_op (complement_lanes A)))
by circuit.

abbrev keccak_double_round_complement_lanes A i =
  keccak_round_complement_lanes_op rc_spec.[2 * i + 1] (keccak_round_complement_lanes_op rc_spec.[2 * i] A).

hoare __keccakf1600_basic_h _a:
 M.__keccakf1600_basic :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc.
ecall (complement_lanes_basic_h a).
while (2 <= c <= 24 /\ 2 %| c /\
       complement_lanes (keccak_f1600_op _a) = foldl keccak_double_round_complement_lanes a (range (c %/ 2) 12)).
 wp; ecall (keccakf1600_pround_basic_h e).
 wp; ecall (keccakf1600_pround_basic_h a).
 auto => /> &m Hc1 _ Hc_2 IH.
 move => Hc2; split; first smt().
 split; first smt().
 move: IH; rewrite (range_cat (c{m} %/ 2 + 1)) 1..2:/#.
 rewrite /swap_ /=.
 rewrite /rc_spec rangeS foldl_cat /= => -> /= /#.
wp; ecall (keccakf1600_pround_basic_h e).
wp; ecall (keccakf1600_pround_basic_h a).
wp; ecall (complement_lanes_basic_h a).
auto => />; split.
 rewrite /swap_ /=.
 pose F := foldl _ _ _.
 have ->: F = foldl keccak_double_round_complement_lanes (complement_lanes _a) (range 0 12).
  rewrite eq_sym /F range_ltn 1:// /=; congr.
  by rewrite /keccak_round_complement_lanes_op /rc_spec /= /#.
 rewrite /range /rc_spec -iotaredE /=.
 rewrite /keccak_round_complement_lanes_op.
 rewrite 24!keccak_iota_complement_lanes 24!complement_lanesI; congr.
 by rewrite /keccak_f1600_op /rc_spec -iotaredE /= /#.
move => a c /= ????.
have ->/=: c = 24 by smt().
rewrite range_geq 1:/# /= => <-.
by rewrite complement_lanesI.
qed.

lemma __keccakf1600_basic_ll: islossless M.__keccakf1600_basic.
proof.
proc.
have Hll:= keccakf1600_pround_basic_ll.
call complement_lanes_basic_ll.
wp; while (0 <= c <= 24) (23 - c).
 move=> z.
 wp; call Hll.
 wp; call Hll.
 by auto => /> &m ?_ ? /#.
wp; call Hll.
wp; call Hll.
wp; call complement_lanes_basic_ll.
by auto => /> c ??? /#.
qed.

phoare __keccakf1600_basic_ph _a:
 [ M.__keccakf1600_basic
 : a = _a
 ==> res = keccak_f1600_op _a
 ] = 1%r.
proof. by conseq __keccakf1600_basic_ll (__keccakf1600_basic_h _a). qed.

lemma keccakf1600_basic_ll: islossless M._keccakf1600_basic.
proof.
proc; inline _keccakf1600_basic.
by call __keccakf1600_basic_ll.
qed.

hoare keccakf1600_basic_h _a:
 M._keccakf1600_basic :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc; inline _keccakf1600_basic.
by call (__keccakf1600_basic_h _a).
qed.
