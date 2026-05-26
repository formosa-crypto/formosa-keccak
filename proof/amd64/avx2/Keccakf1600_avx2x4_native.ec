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


module Maux = {
  proc f1600_loopbody_native_aux (st:W256.t Array25.t, rol8:W256.t,
                                rol56:W256.t, rC:W64.t,
                                y10:W256.t, y14:W256.t, y8:W256.t,
                                y15:W256.t, y9:W256.t, y13:W256.t, y3:W256.t,
                                y7:W256.t, y2:W256.t) : W256.t Array25.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t = {
    var y4:W256.t;
    var y0:W256.t;
    var y11:W256.t;
    var y12:W256.t;
    var y1:W256.t;
    var y6:W256.t;
    var y5:W256.t;
    y4 <- st.[5];
    y0 <- (y9 `^` st.[20]);
    st.[7] <- y9;
    y9 <- y10;
    y11 <- st.[6];
    y12 <- st.[16];
    st.[11] <- y3;
    y1 <- (y4 `^` st.[10]);
    y10 <- st.[2];
    st.[8] <- y4;
    y12 <- (y12 `^` y3);
    y6 <- st.[1];
    y4 <- st.[14];
    st.[18] <- y14;
    y0 <- (y0 `^` y1);
    y1 <- (y11 `^` y8);
    y11 <- (y7 `^` st.[17]);
    st.[15] <- y10;
    y12 <- (y12 `^` y1);
    y1 <- (y9 `^` y15);
    y3 <- st.[9];
    st.[12] <- y8;
    y11 <- (y11 `^` y1);
    y1 <- (y14 `^` st.[13]);
    y12 <- (y12 `^` y6);
    y8 <- st.[3];
    y11 <- (y11 `^` y10);
    y10 <- (y13 `^` st.[23]);
    y3 <- (y3 `^` y4);
    st.[21] <- y4;
    y4 <- (VPSRL_4u64 y12 (W128.of_int 63));
    y5 <- (VPSRL_4u64 y11 (W128.of_int 63));
    y0 <- (y0 `^` st.[0]);
    y10 <- (y10 `^` y1);
    y1 <- st.[4];
    y10 <- (y10 `^` y8);
    y14 <- y1;
    y1 <- (y2 `^` st.[19]);
    st.[22] <- y14;
    y1 <- (y1 `^` y3);
    y3 <- (VPSLL_4u64 y12 (W128.of_int 1));
    y3 <- (y3 `|` y4);
    y4 <- (VPSLL_4u64 y11 (W128.of_int 1));
    y1 <- (y1 `^` y14);
    y4 <- (y4 `|` y5);
    y14 <- (VPSRL_4u64 y10 (W128.of_int 63));
    y3 <- (y3 `^` y1);
    y5 <- (VPSLL_4u64 y10 (W128.of_int 1));
    y4 <- (y4 `^` y0);
    y5 <- (y5 `|` y14);
    y6 <- (y4 `^` y6);
    y5 <- (y5 `^` y12);
    y12 <- (VPSRL_4u64 y1 (W128.of_int 63));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 1));
    y7 <- (y5 `^` y7);
    y9 <- (y5 `^` y9);
    y1 <- (y1 `|` y12);
    y12 <- (y3 `^` st.[0]);
    y1 <- (y1 `^` y11);
    y11 <- (VPSRL_4u64 y0 (W128.of_int 63));
    y0 <- (VPSLL_4u64 y0 (W128.of_int 1));
    y13 <- (y1 `^` y13);
    y8 <- (y1 `^` y8);
    y0 <- (y0 `|` y11);
    y0 <- (y0 `^` y10);
    y10 <- (y4 `^` st.[6]);
    y2 <- (y0 `^` y2);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 20));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 44));
    y10 <- (y10 `|` y11);
    y11 <- (y5 `^` y15);
    y15 <- (VPBROADCAST_4u64 rC);
    y14 <- (VPSRL_4u64 y11 (W128.of_int 21));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 43));
    y11 <- (y11 `|` y14);
    y14 <- ((invw y10) `&` y11);
    y14 <- (y14 `^` y15);
    y15 <- (y14 `^` y12);
    y14 <- (VPSRL_4u64 y13 (W128.of_int 43));
    y13 <- (VPSLL_4u64 y13 (W128.of_int 21));
    st.[0] <- y15;
    y13 <- (y13 `|` y14);
    y14 <- ((invw y11) `&` y13);
    y15 <- (y14 `^` y10);
    y14 <- (VPSRL_4u64 y2 (W128.of_int 50));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 14));
    st.[1] <- y15;
    y2 <- (y2 `|` y14);
    y14 <- ((invw y13) `&` y2);
    y11 <- (y14 `^` y11);
    st.[2] <- y11;
    y11 <- ((invw y2) `&` y12);
    y12 <- ((invw y12) `&` y10);
    y11 <- (y11 `^` y13);
    st.[3] <- y11;
    y11 <- (y12 `^` y2);
    y2 <- (VPSRL_4u64 y8 (W128.of_int 36));
    y8 <- (VPSLL_4u64 y8 (W128.of_int 28));
    st.[4] <- y11;
    y8 <- (y8 `|` y2);
    y2 <- (y0 `^` st.[9]);
    y10 <- (VPSRL_4u64 y2 (W128.of_int 44));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 20));
    y2 <- (y2 `|` y10);
    y10 <- (y3 `^` st.[10]);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 61));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 3));
    y10 <- (y10 `|` y11);
    y11 <- ((invw y2) `&` y10);
    y11 <- (y11 `^` y8);
    st.[5] <- y11;
    y11 <- (y4 `^` st.[16]);
    y12 <- (VPSRL_4u64 y11 (W128.of_int 19));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 45));
    y11 <- (y11 `|` y12);
    y12 <- ((invw y10) `&` y11);
    y12 <- (y12 `^` y2);
    st.[6] <- y12;
    y12 <- (VPSRL_4u64 y7 (W128.of_int 3));
    y7 <- (VPSLL_4u64 y7 (W128.of_int 61));
    y7 <- (y7 `|` y12);
    y12 <- ((invw y11) `&` y7);
    y10 <- (y12 `^` y10);
    y12 <- ((invw y7) `&` y8);
    y8 <- ((invw y8) `&` y2);
    y2 <- (VPSRL_4u64 y6 (W128.of_int 63));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 1));
    y14 <- (y12 `^` y11);
    y6 <- (y6 `|` y2);
    y2 <- (VPSRL_4u64 y9 (W128.of_int 58));
    y12 <- (y8 `^` y7);
    y9 <- (VPSLL_4u64 y9 (W128.of_int 6));
    st.[9] <- y12;
    y7 <- (y0 `^` st.[19]);
    y9 <- (y9 `|` y2);
    y2 <- (y1 `^` st.[13]);
    y7 <- (VPSHUFB_256 y7 rol8);
    y11 <- (VPSRL_4u64 y2 (W128.of_int 39));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 25));
    y11 <- (y11 `|` y2);
    y2 <- ((invw y9) `&` y11);
    y8 <- ((invw y11) `&` y7);
    y12 <- (y2 `^` y6);
    y2 <- (y3 `^` st.[20]);
    y8 <- (y8 `^` y9);
    st.[10] <- y12;
    y12 <- (VPSRL_4u64 y2 (W128.of_int 46));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 18));
    y2 <- (y12 `|` y2);
    y12 <- ((invw y7) `&` y2);
    y15 <- (y12 `^` y11);
    y11 <- ((invw y2) `&` y6);
    y6 <- ((invw y6) `&` y9);
    y12 <- (y11 `^` y7);
    st.[13] <- y12;
    y12 <- (y6 `^` y2);
    y6 <- (y0 `^` st.[22]);
    y0 <- (y0 `^` st.[21]);
    st.[14] <- y12;
    y2 <- (VPSRL_4u64 y6 (W128.of_int 37));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 27));
    y2 <- (y2 `|` y6);
    y6 <- (y3 `^` st.[8]);
    y3 <- (y3 `^` st.[7]);
    y7 <- (VPSRL_4u64 y6 (W128.of_int 28));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 36));
    y7 <- (y7 `|` y6);
    y6 <- (y4 `^` st.[12]);
    y4 <- (y4 `^` st.[11]);
    y12 <- (VPSRL_4u64 y6 (W128.of_int 54));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 10));
    y12 <- (y12 `|` y6);
    y6 <- (y5 `^` st.[17]);
    y5 <- (y5 `^` st.[15]);
    y9 <- ((invw y7) `&` y12);
    y11 <- (VPSRL_4u64 y6 (W128.of_int 49));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 15));
    y9 <- (y9 `^` y2);
    y11 <- (y11 `|` y6);
    y6 <- ((invw y12) `&` y11);
    y6 <- (y6 `^` y7);
    st.[16] <- y6;
    y6 <- (y1 `^` st.[23]);
    y1 <- (y1 `^` st.[18]);
    y6 <- (VPSHUFB_256 y6 rol56);
    y13 <- ((invw y11) `&` y6);
    y13 <- (y13 `^` y12);
    st.[17] <- y13;
    y13 <- ((invw y6) `&` y2);
    y2 <- ((invw y2) `&` y7);
    y2 <- (y2 `^` y6);
    y6 <- (VPSRL_4u64 y4 (W128.of_int 62));
    y13 <- (y13 `^` y11);
    st.[19] <- y2;
    y2 <- (VPSRL_4u64 y5 (W128.of_int 2));
    y5 <- (VPSLL_4u64 y5 (W128.of_int 62));
    y2 <- (y2 `|` y5);
    y5 <- (VPSRL_4u64 y1 (W128.of_int 9));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 55));
    y4 <- (VPSLL_4u64 y4 (W128.of_int 2));
    y1 <- (y5 `|` y1);
    y5 <- (VPSRL_4u64 y0 (W128.of_int 25));
    y4 <- (y6 `|` y4);
    y0 <- (VPSLL_4u64 y0 (W128.of_int 39));
    y5 <- (y5 `|` y0);
    y0 <- ((invw y1) `&` y5);
    y0 <- (y0 `^` y2);
    st.[20] <- y0;
    y0 <- (VPSRL_4u64 y3 (W128.of_int 23));
    y3 <- (VPSLL_4u64 y3 (W128.of_int 41));
    y0 <- (y0 `|` y3);
    y7 <- ((invw y0) `&` y4);
    y3 <- ((invw y5) `&` y0);
    y7 <- (y7 `^` y5);
    y5 <- ((invw y4) `&` y2);
    y2 <- ((invw y2) `&` y1);
    y5 <- (y5 `^` y0);
    y3 <- (y3 `^` y1);
    y2 <- (y2 `^` y4);
    st.[23] <- y5;
    return (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
  }
 proc p1(st4x: state4x, rc: W64.t): state4x = {
  var y10, y14, y8, y15, y9, y13, y3, y7, y2;
  var rol8, rol56;
  rol8 <- W256.of_int
       13620818001941277694121380808605999856886653716761013959207994299728839901191;
  rol56 <- W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841;
  st4x <- st4x_pack_spec st4x;
  (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ M.__regs_fetch(st4x);
  (st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@
   f1600_loopbody_native_aux( st4x, rol8, rol56, rc,
                            y10, y14, y8, y15, y9, y13, y3, y7, y2);
  st4x <@ M.__regs_unfetch(st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2);
  st4x <- st4x_from_4st (st4x_unpack st4x);
  return st4x;
 }
 proc p2(st4x: state4x, rc: W64.t): state4x = {
  var y10, y14, y8, y15, y9, y13, y3, y7, y2;
  var rol8, rol56;
  rol8 <- W256.of_int
       13620818001941277694121380808605999856886653716761013959207994299728839901191;
  rol56 <- W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841;
  (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ M.__regs_fetch(st4x);
  (st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@
   f1600_loopbody_native_aux( st4x, rol8, rol56, rc,
                            y10, y14, y8, y15, y9, y13, y3, y7, y2);
  st4x <@ M.__regs_unfetch(st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2);
  return st4x;
 }
 proc p3(st4x: state4x): state4x = {
  var y10, y14, y8, y15, y9, y13, y3, y7, y2;
  var rol8, rol56, rc;
  rol8 <- W256.of_int
       13620818001941277694121380808605999856886653716761013959207994299728839901191;
  rol56 <- W256.of_int 10910488462195273559651782724632284871561478246514020268633800075540923875841;
  rc <- W64.zero;
(*  st4x <- st4x_pack_spec st4x;*)
  (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ M.__regs_fetch(st4x);
  (st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@
   f1600_loopbody_native_aux( st4x, rol8, rol56, rc,
                            y10, y14, y8, y15, y9, y13, y3, y7, y2);
  st4x <@ M.__regs_unfetch(st4x, y10, y14, y8, y15, y9, y13, y3, y7, y2);
(*  st4x <- st4x_from_4st (st4x_unpack st4x); *)
  return st4x;
 }
 proc p4(st4x: state4x): state4x = {
  var r8, r56, st4x2;
  r8 <- rOL8.[0];
  r56 <- rOL56.[0];
  st4x2 <@ M._keccakf1600_4x_pround(st4x2, st4x, r8, r56);
  st4x <- st4x2;
  return st4x;
 }
}. 

(* Attempt #1: direct equivalence proof *)
equiv keccak__eq:
 Maux.p3
 ~ Maux.p4
 : ={st4x}
 ==> ={res}.
proof.
proc; simplify.
inline*.
abort(*
by circuit.
qed.
*).

(* attempt #2: correctness against a spec (4 lanes) *)
hoare keccakf1600_avx2x4_native_unpacked_h _st4x _rc:
 Maux.p1:
 st4x = _st4x /\ rc = _rc
 ==> (st4x_to_4st res).`1 = keccak_round_op _rc (st4x_to_4st _st4x).`1
     /\ (st4x_to_4st res).`2 = keccak_round_op _rc (st4x_to_4st _st4x).`2
     /\ (st4x_to_4st res).`3 = keccak_round_op _rc (st4x_to_4st _st4x).`3
     /\ (st4x_to_4st res).`4 = keccak_round_op _rc (st4x_to_4st _st4x).`4
.
proof.
proc; inline*; simplify.
do 24! cfold 28.
wp -24.
abort (* It HANGS!!! 
by circuit.
qed.
*).

op st4x_keccak_round c =
 st4x_map (keccak_round_op c).

(* attempt #3: correctness against a spec (direct) *)
hoare keccakf1600_avx2x4_native_unpacked_h _st4x _rc:
 Maux.p2:
 st4x = _st4x /\ rc = _rc
 ==> res = st4x_keccak_round _rc _st4x.
proof.
proc; inline*; simplify.
do 24! cfold 27.
wp -24.
abort (* 
by circuit.
qed.
*).

lemma f1600_loopbody_native_ll: islossless M.__f1600_loopbody_native.
proof. by islossless. qed.

(*
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
*)
print M.
phoare keccak_pround_avx2x4_ph _st4x _i:
 [ M.test_keccakf1600x4_native:
 st = _st4x
 /\ c = _i
 ==> res = st4x_keccak_round (kECCAK1600_RC.[to_uint _i]) _st4x] = 1%r.
proof.
admitted(*
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
*).

(*
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

abbrev st_keccak_iota rc (st:state) =
 st.[0 <- st.[0] `^` rc].
abbrev st4x_keccak_iota rc (st4x:state4x) =
 st4x.[0 <- VPBROADCAST_4u64 rc `^` st4x.[0]].


lemma VPBROADCAST_4u64_bits64 w k:
 0 <= k < 4 =>
 VPBROADCAST_4u64 w \bits64 k = w.
proof.
move=> Hk; have: k\in iota_ 0 4 by smt(mem_iota).
move: {Hk} k; apply/List.allP.
rewrite -iotaredE /=.
by circuit.
qed.

lemma sliceget64_256_25E k i st4x:
 0 <= k < 4 =>
 0 <= i < 25 =>
 sliceget64_256_25 st4x (8 * (4 * i + k) * 8)
 = st4x.[i] \bits64 k.
proof.
move=> Hk Hi.
rewrite /sliceget64_256_25 ifT 1:/# get64E bits64E /=.
apply W64.ext_eq => b Hb.
rewrite !initiE //= pack8E initiE //= initiE 1:/# /= initiE 1:/# /=.
by rewrite bits8iE 1:/# /#.
qed.


lemma st4x_keccak_iotaE rc st4x:
 st4x_keccak_iota rc st4x
 = st4x_map (fun st=>st.[0 <- st.[0] `^` rc]) st4x.
proof.
rewrite tP => i Hi.
rewrite get_setE //.
rewrite initiE //= !get_setE // !initiE //=.
rewrite -(W4u64.unpack64K) u256_pack4E.
congr.
rewrite unpack64E.
rewrite W4u64.Pack.init_of_list; congr.
rewrite -iotaredE /=.
case: (i=0) => Ei.
 rewrite (sliceget64_256_25E 0 0) // (sliceget64_256_25E 1 0) //.
 rewrite (sliceget64_256_25E 2 0) // (sliceget64_256_25E 3 0) //.
 by rewrite xorwC !xorb64E !VPBROADCAST_4u64_bits64 //.
rewrite (sliceget64_256_25E 0 i) // (sliceget64_256_25E 1 i) //.
by rewrite (sliceget64_256_25E 2 i) // (sliceget64_256_25E 3 i) //.
qed.

lemma st4x_get_map f st4x k:
 0 <= k < 4 =>
 st4x_get (st4x_map f st4x) k
 = f (st4x_get st4x k).
proof.
move=> Hk.
have: k=0 \/ k=1 \/ k=2 \/ k=3 by smt().
move=> [->|]; first by rewrite st4x_get_pack0.
move=> [->|]; first by rewrite st4x_get_pack1.
move=> [->|]; first by rewrite st4x_get_pack2.
move=> ->; by rewrite st4x_get_pack3.
qed.

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
*)

abbrev keccak_round_i i st =
 foldl (fun s i => keccak_round_op rc_spec.[i] s) st (iota_ 0 i).

hoare keccakf1600_avx2x4_native_h _a:
 M.__keccakf1600_avx2x4_native :
 st = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
admitted(*
while (0 <= i <= 24 /\
       rc = rc_spec /\
       rol8 = rOL8 /\
       rol56 = rOL56 /\
       st = st4x_map (keccak_round_i i) _a).
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
*).

lemma keccakf1600_avx2x4_native_ll: islossless M.__keccakf1600_avx2x4_native.
proof.
proc.
inline __regs_unfetch __regs_fetch.
wp; while (true) (24-i).
 move=> z.
 wp; call f1600_loopbody_native_ll.
 by auto => /> &m ? /#.
wp; call f1600_loopbody_native_ll.
by inline*; auto => /#.
qed.

phoare keccakf1600_avx2x4_native_ph _a:
 [ M.__keccakf1600_avx2x4_native
 : st = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq keccakf1600_avx2x4_native_ll (keccakf1600_avx2x4_native_h _a).
qed.

