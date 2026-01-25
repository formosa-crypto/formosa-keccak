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

op st4x_to_4st (st4x: state4x): state*state*state*state =
 ( init_25_64 (fun i => sliceget64_256_25 st4x ((200*0+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*1+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*2+8*i)*8))
 , init_25_64 (fun i => sliceget64_256_25 st4x ((200*3+8*i)*8))
 ).



op st4x_from_4st (sts: state*state*state*state): state4x =
 init_25_256
  (fun i =>
    sliceget256_64_100
     (init_100_64
      (fun j =>
        if j < 25 then sts.`1.[j]
        else if j < 50 then sts.`2.[j-25]
        else if j < 75 then sts.`3.[j-50]
        else sts.`4.[j-75]))
      (32*i*8)
    ).

lemma st4x_from_4stK sts:
 st4x_to_4st (st4x_from_4st sts) = sts.
proof.
move: sts => [st0 st1 st2 st3].
rewrite /st4x_to_4st /=.
by do split;
 rewrite tP => i Hi;
 rewrite initiE //= /sliceget64_256_25 ifT 1:/# get64E;
 apply W64.ext_eq => k Hk;
 rewrite pack8E;
 rewrite initiE 1:/# /= initiE 1:/# /=;
 rewrite initiE 1:/# /= initiE 1:/# /=;
 rewrite /sliceget256_64_100 ifT 1:/#;
 rewrite get256E pack32E /= bits8iE 1:/#;
 rewrite initiE 1:/# /= initiE 1:/# /=;
 rewrite initiE 1:/# /= initiE 1:/# /=;
 rewrite !bits8iE /#. 
qed.

lemma st4x_from_4stK' st0 st1 st2 st3:
 st4x_to_4st
  (init_25_256
     (fun (i : int) =>
        sliceget256_64_100
          (init_100_64
             (fun (j : int) =>
                if j < 25 then st0.[j]
                else
                  if j < 50 then st1.[j - 25]
                  else if j < 75 then st2.[j - 50] else st3.[j - 75]))
          (32 * i * 8)))
 = (st0, st1, st2, st3).
proof. by apply (st4x_from_4stK (st0,st1,st2,st3)). qed.

lemma st4x_to_4stK st4x:
 st4x_from_4st (st4x_to_4st st4x) = st4x.
proof.
rewrite /st4x_to_4st /= tP => i Hi. 
rewrite initiE //= /sliceget256_64_100 ifT 1:/# get256E pack32E.
apply W256.ext_eq => k Hk.
rewrite initiE //= initiE 1:/# /=.
rewrite initiE 1:/# /= initiE 1:/# /= bits8iE 1:/#.
pose j:= (32 * i * 8 %/ 8 + k %/ 8) %/ 8.
case: (j < 25) => C1.
 rewrite initiE 1:/# /=;
 rewrite /sliceget64_256_25 ifT 1:/# get64E pack8E initiE 1:/# /=;
 by rewrite initiE 1:/# /= initiE 1:/# /= bits8iE /#.
case: (j < 50) => C2.
 rewrite initiE 1:/# /=;
 rewrite /sliceget64_256_25 ifT 1:/# get64E pack8E initiE 1:/# /=;
 by rewrite initiE 1:/# /= initiE 1:/# /= bits8iE /#.
case: (j < 75) => C3;
 rewrite initiE 1:/# /=;
 rewrite /sliceget64_256_25 ifT 1:/# get64E pack8E initiE 1:/# /=;
 by rewrite initiE 1:/# /= initiE 1:/# /= bits8iE /#.
qed.

lemma st4x_from_4st_inj sts1 sts2:
 st4x_from_4st sts1 = st4x_from_4st sts2 => sts1 = sts2.
proof.
move=> H.
by rewrite -(st4x_from_4stK sts1) H st4x_from_4stK.
qed.

lemma st4x_from_4st_inj' (st0a st1a st2a st3a st0b st1b st2b st3b: state):
 init_25_256
  (fun (i : int) =>
     sliceget256_64_100
       (init_100_64
          (fun (j : int) =>
             if j < 25 then st0a.[j]
             else
               if j < 50 then st1a.[j - 25]
               else if j < 75 then st2a.[j - 50] else st3a.[j - 75]))
       (32 * i * 8)) =
 init_25_256
  (fun (i : int) =>
     sliceget256_64_100
       (init_100_64
          (fun (j : int) =>
             if j < 25 then st0b.[j]
             else
               if j < 50 then st1b.[j - 25]
               else if j < 75 then st2b.[j - 50] else st3b.[j - 75]))
       (32 * i * 8)) =>
 (st0a,st1a,st2a,st3a)=(st0b,st1b,st2b,st3b).
proof.
move=> H. 
by rewrite -(st4x_from_4stK' st0a st1a st2a st3a) H st4x_from_4stK'.
qed.

require import Avx2_extra.

op st4x_pack_spec (sts: state4x): state4x =
 st4x_pack (st4x_to_4st sts).

op st4x_unpack_spec (st4x: state4x) =
 st4x_from_4st (st4x_unpack st4x).

op st4x_inv (_: state4x) = true.

lemma st4x_get_pack0' (st0 st1 st2 st3: state):
 init_25_64
  (fun (i : int) =>
     sliceget64_256_25
       (init_25_256
          (fun (i0 : int) => u256_pack4 st0.[i0] st1.[i0] st2.[i0] st3.[i0]))
       (8 * (4 * i) * 8))
 = st0.
proof.
by circuit.
qed.

lemma st4x_get_pack1' (st0 st1 st2 st3: state):
 st4x_get
  (init_25_256 (fun (i : int) => u256_pack4 st0.[i] st1.[i] st2.[i] st3.[i]))
  1
 = st1.
proof.
by circuit.
qed.

lemma st4x_get_pack2' (st0 st1 st2 st3: state):
 st4x_get
  (init_25_256 (fun (i : int) => u256_pack4 st0.[i] st1.[i] st2.[i] st3.[i]))
  2
 = st2.
proof.
by circuit.
qed.

lemma st4x_get_pack3' (st0 st1 st2 st3: state):
 st4x_get
  (init_25_256 (fun (i : int) => u256_pack4 st0.[i] st1.[i] st2.[i] st3.[i]))
  3
 = st3.
proof.
by circuit.
qed.

lemma st4x_get_pack0 sts:
 st4x_get (st4x_pack sts) 0 = sts.`1.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack1 sts:
 st4x_get (st4x_pack sts) 1 = sts.`2.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack2 sts:
 st4x_get (st4x_pack sts) 2 = sts.`3.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.

lemma st4x_get_pack3 sts:
 st4x_get (st4x_pack sts) 3 = sts.`4.
proof.
move: sts => [st0 st1 st2 st3] /=.
by circuit.
qed.


lemma st4x_packK_ALT sts:
 st4x_unpack (st4x_pack sts) = sts.
proof.
move: sts => [st0 st1 st2 st3].
rewrite /st4x_unpack.
by rewrite st4x_get_pack0 st4x_get_pack1 st4x_get_pack2 st4x_get_pack3.
qed.

lemma st4x_unpackK_ALT st4x:
 st4x_pack (st4x_unpack st4x) = st4x.
proof.
by circuit.
qed.

lemma st4x_unpack_inj st4x1 st4x2:
 st4x_unpack st4x1 = st4x_unpack st4x2
 => st4x1 = st4x2.
proof.
move=> H.
by rewrite -{1}st4x_unpackK H st4x_unpackK.
qed.


hoare st4x_pack_h _st0 _st1 _st2 _st3:
 M.__st4x_pack:
 st0 = _st0 /\ st1 = _st1 /\ st2 = _st2 /\ st3 = _st3
 ==> res = st4x_pack (_st0, _st1, _st2, _st3).
proof.
proc.
proc change ^while.1: { x0 <- sliceget256_64_25 st0 (32*i*8); };
 1: by auto => /#.
proc change ^while.2: { x1 <- sliceget256_64_25 st1 (32*i*8); };
 1: by auto => /#.
proc change ^while.3: { x2 <- sliceget256_64_25 st2 (32*i*8); };
 1: by auto => /#.
proc change ^while.4: { x3 <- sliceget256_64_25 st3 (32*i*8); };
 1: by auto => /#.
unroll for 2.
proc change 60: { st4x <- sliceset64_256_25 st4x (8*(4 * 24 + 0)*8) t0; };
 1: by auto => /#.
proc change 61: { st4x <- sliceset64_256_25 st4x (8*(4 * 24 + 1)*8) t1; };
 1: by auto => /#.
proc change 62: { st4x <- sliceset64_256_25 st4x (8*(4 * 24 + 2)*8) t2; };
 1: by auto => /#.
proc change 63: { st4x <- sliceset64_256_25 st4x (8*(4 * 24 + 3)*8) t3; };
 1: by auto => /#.
inline*; simplify.
swap 127 8; wp 134.
by circuit.
qed.

lemma st4x_pack_ll: islossless M.__st4x_pack.
proc. by unroll for 2; islossless. qed.

phoare st4x_pack_ph _st0 _st1 _st2 _st3:
 [ M.__st4x_pack
 : st0 = _st0 /\ st1 = _st1 /\ st2 = _st2 /\ st3 = _st3
 ==> res = st4x_pack (_st0, _st1, _st2, _st3)
 ] = 1%r.
proof. 
by conseq st4x_pack_ll (st4x_pack_h _st0 _st1 _st2 _st3).
qed.

hoare st4x_unpack_h _st4x:
 M.__st4x_unpack:
 st4x = _st4x
 ==> res = st4x_unpack _st4x.
proof.
proc; simplify.
proc change ^while.6: { st0 <- sliceset256_64_25 st0 (4*8*i*8) x0; };
 1: by auto => /#.
proc change ^while.7: { st1 <- sliceset256_64_25 st1 (4*8*i*8) x1; };
 1: by auto => /#.
proc change ^while.8: { st2 <- sliceset256_64_25 st2 (4*8*i*8) x2; };
 1: by auto => /#.
proc change ^while.9: { st3 <- sliceset256_64_25 st3 (4*8*i*8) x3; };
 1: by auto => /#.
proc change 3: { t0 <- sliceget64_256_25 st4x (8*(4*24)*8); };
 1: by auto => /#.
proc change 4: { t1 <- sliceget64_256_25 st4x (8*(4*24+1)*8); };
 1: by auto => /#.
proc change 5: { t2 <- sliceget64_256_25 st4x (8*(4*24+2)*8); };
 1: by auto => /#.
proc change 6: { t3 <- sliceget64_256_25 st4x (8*(4*24+3)*8); };
 1: by auto => /#.
unroll for 2.
swap 55 8.
wp 62.
inline*.
by circuit.
qed.

lemma st4x_unpack_ll: islossless M.__st4x_unpack.
proof. by proc; unroll for 2; islossless. qed.

phoare st4x_unpack_ph _st4x:
 [ M.__st4x_unpack
 : st4x = _st4x
 ==> res = st4x_unpack _st4x
 ] = 1%r.
proof. by conseq st4x_unpack_ll (st4x_unpack_h _st4x). qed.

op st_inv (_:state) = true.

module Maux = {
 proc p1(st4x2 st4x1: state4x): state4x = {
  st4x1 <- st4x_pack_spec st4x1;
  st4x2 <@ M._keccakf1600_4x_pround(st4x2, st4x1, rOL8, rOL56);
  st4x2 <- st4x_from_4st (st4x_unpack st4x2);
  return st4x2;
 }
 proc p1_(st4x2 st4x1: state4x): state4x = {
  var r8, r56;
  st4x1 <- st4x_pack_spec st4x1;
  r8 <- rOL8;
  r56 <- rOL56;
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
  r8 <- rOL8;
  r56 <- rOL56;
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
by circuit.
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
   /\ r8{1} = rOL8 /\ r56{1} = rOL56
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
 /\ r8 = rOL8 /\ r56 = rOL56
 ==> res = st4x_keccak_pround _st4x] = 1%r.
proof.
bypr => &m /> -> ->.
have ->:
 Pr[M._keccakf1600_4x_pround(e{m}, a{m}, rOL8, rOL56) @ &m :
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
 /\ r8 = rOL8 /\ r56 = rOL56
 ==> res = st4x_keccak_pround _st4x.
proof.
bypr => &m /> -> ->.
have ->:
 Pr[M._keccakf1600_4x_pround(e{m}, a{m}, rOL8, rOL56) @ &m :
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
 /\ r8 = rOL8 /\ r56 = rOL56
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

hoare keccakf1600_avx2x4_h' _a:
 M.__keccakf1600_avx2x4 :
 a = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
while (0 <= c <= 24 /\ c %% 2 = 0 /\
       rC = rc_spec /\
       r8 = rOL8 /\
       r56 = rOL56 /\
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

lemma keccakf1600_avx2x4_ll': islossless M.__keccakf1600_avx2x4.
proof.
proc.
wp; while (true) (24-c).
 move=> z.
 wp; call keccakf1600_4x_pround_ll.
 by wp; call keccakf1600_4x_pround_ll; auto => /> &m ? /#.
by auto => /#.
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

