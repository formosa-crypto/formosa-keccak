(******************************************************************************
   Keccakf1600_ref.ec:

   Correctness proof for the Keccak REF implementation
******************************************************************************)
require import List Real Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array5 Array24 Array25.

(** lemmata (move?) *)

lemma ROL_64_by0 (w: W64.t): w `|<<<|` 0 = w.
proof. by apply  W64.all_eq_eq; rewrite /all_eq /=. qed.

lemma ROL_64_val w i:
 (ROL_64 w (W8.of_int i)).`3 = w `|<<<|` (i %% 64).
proof.
rewrite /ROL_64 /shift_mask /=.
rewrite modz_dvd 1:/#.
case: (i %% 64 = 0) => [->|//].
by apply W64.all_eq_eq; rewrite /all_eq.
qed.

hoare rol_u64_h _x _r:
 M.__rol_u64_ref
 : x = _x /\ i = _r%%64
 ==> res = _x  `|<<<|` _r%%64.
proof.
proc; simplify.
case: (i=0).
 by rcondf 1; auto => /> ->; rewrite ROL_64_by0.
rcondt 1; auto => /> E.
rewrite /ROL_64 /shift_mask /=.
by rewrite !modz_dvd 1..2:/# E.
qed.

lemma rol_u64_ll: islossless M.__rol_u64_ref
 by islossless.

phoare rol_u64_ph _x _r:
 [ M.__rol_u64_ref
 : x = _x /\ i = _r%%64 ==> res = _x  `|<<<|` _r%%64 ] = 1%r
by conseq rol_u64_ll (rol_u64_h _x _r).


(* *)

hoare theta_sum_ref_h _a:
 M.__theta_sum_ref :
  a = _a ==> res = keccak_C _a.
proof.
proc.
do 6! unroll for ^while.
auto => />.
by rewrite -Array5.ext_eq_all /all_eq /keccak_C /idx /invidx /=.
qed.

hoare theta_rol_ref_h _c:
 M.__theta_rol_ref :
  c = _c ==> res = keccak_D _c.
proof.
proc.
unroll for ^while; inline*; auto => />.
rewrite -ext_eq_all /all_eq /keccak_D /idx /invidx /=.
by rewrite /ROL_64 /shift_mask /init_5_64 /rol_64 /=; smt(W64.xorwC).
qed.

hoare keccak_rho_offsets_h _i:
  M.keccakf1600_rho_offsets:
  0 <= i < 25 /\ i = _i ==> res = to_uint rhotates.[_i].
proof.
proc.
while (0 <= t <= 24 /\ i=_i /\ 0 <= x < 5 /\ 0 <= y < 5 /\
       (x,y,r) = foldl (fun (a:_*_*_) t =>
                           ( a.`2
                           , (2*a.`1+3*a.`2)%%5
                           , if i=idx(a.`1,a.`2) then (t+1)*(t+2) %/ 2 %% 64 else a.`3)) 
                       (1,0,0) (iota_ 0 t)).
 auto => &m [[Ht [Hi [Hx [Hy IH]]]] Hc]; split.
  move=> P /=; split; first smt().
  by rewrite iotaSr 1:/# foldl_rcons /= -IH /= /#. 
 move=> P /=; split; first smt().
 by rewrite iotaSr 1:/# foldl_rcons /= -IH /= /#. 
auto => /> Hi0 Hi1; split.
 by rewrite -iotaredE /=.
move=> r t x y ???; have ->: t=24 by smt().
move => _ _ _ _.
have: _i \in iota_ 0 25 by smt(mem_iota).
move: {Hi0 Hi1} _i; apply/List.allP.
by rewrite -iotaredE /rhotates /= /#.
qed.

lemma rhotates_idx_mod64 _i:
 0 <= _i < 25 =>
 to_uint rhotates.[_i] %% 64 = to_uint rhotates.[_i].
proof.
move=> Hi; have: _i \in iota_ 0 25.
 by rewrite mem_iota; smt(idx_bnd).
by move: {Hi} _i ; rewrite -allP -iotaredE /= initiE /=.
qed.

hoare rhotates_spec_h _x _y:
  M.keccakf1600_rhotates :
  x = _x /\ y = _y /\ 0<=_x<5 /\ 0<=_y<5 ==> res = to_uint rhotates.[idx(_x,_y)].
proof.
proc.
call (keccak_rho_offsets_h (idx(_x,_y))).
by inline*; auto => /> * /#.
qed.

hoare rol_sum_ref_h _a _y:
 M.__rol_sum_ref :
  a = _a /\ d = keccak_D (keccak_C _a) /\ y = _y /\ 0 <= y < 5
  ==> forall x, 0 <= x < 5 => res.[x] = (keccak_pi_op (keccak_rho_op (keccak_theta_op _a))).[idx(x,_y)].
proof.
proc; simplify.
while (#pre /\ 0 <= x <= 5 /\
       forall i, 0 <= i < x =>
        b.[i] =
        rol_64 (_a.[idx (i + 3 * _y, i)] 
                `^` (keccak_D (keccak_C _a)).[(i+3*_y)%%5])
        (rhotates.[idx (i + 3 * _y, i)])).
 wp; ecall (rol_u64_h b.[x] r).
 wp; ecall (rhotates_spec_h x_ y_).
 auto => /> &m Hy1 Hy2 Hx1 _ IH Hx2; split; first smt().
 move=> Hz1 Hz2; split.
  by rewrite rhotates_idx_mod64 /#.
 move => _; split; first by smt().
 move => i Hi1 Hi2.
 case: (i = x{m}) => E.
  rewrite E get_setE 1:/# ifT 1:/#.
  rewrite get_setE 1:/# ifT 1:/#.
  rewrite get_setE 1:/# ifT 1:/#.
  by rewrite rhotates_idx_mod64 /rol_64 1:/# modz_mod /idx_op /#.
 by rewrite get_setE 1:/# ifF 1:/# IH 1:/#.
auto => /> Hy1 Hy2; split; first by smt().
move => A k ???; have ->:k=5 by smt().
move => IH x Hx1 Hx2.
rewrite IH 1:/#.
pose R:= rhotates.[_] (*obs: lock reduction *).
rewrite /rol_64 /init_25_64 /=.
rewrite Array25.initiE 1:/#; beta. 
rewrite -/(idx_op (x,_y)) -/(invidx_op _) idxK' /idx_op /=.
rewrite Array25.initiE 1:/# //= /rol_64 !modz_mod.
rewrite Array25.initiE 1:/# //= /rol_64; congr; congr; smt(). 
qed.

hoare ANDN_64_h _a _b:
 M.__ANDN_64 :
 a = _a /\ b = _b ==> res = invw _a `&` _b.
proof. by proc; auto. qed.

phoare ANDN_64_ph _a _b:
 [ M.__ANDN_64 :
   a = _a /\ b = _b ==> res = invw _a `&` _b ] = 1%r.
proof. by proc; auto. qed.

hoare set_row_ref_h _a _e _b _y:
 M.__set_row_ref :
  e = _e /\ b = _b /\ y = _y /\ 0 <= y < 5
  /\ (forall x, 0 <= x < 5 =>
      _b.[x] = (keccak_pi_op (keccak_rho_op (keccak_theta_op _a))).[idx(x,_y)])
  /\ (forall k, 0 <= k < 5*_y => e.[k] = (keccak_pround_op _a).[k])
  ==> forall k, 0 <= k < 5*_y + 5 => res.[k] = (keccak_pround_op _a).[k].
proof.
proc; simplify.
while (#[/2:6]pre /\ 0 <= x <= 5 /\ 
       forall k, 0 <= k < x+5*_y => e.[k] = (keccak_pround_op _a).[k]).
 wp; ecall (ANDN_64_h b.[x1] b.[x2]).
 auto => /> &m Hy1 Hy2 Hb Hx1 _ IH Hx2; split; first smt().
 move=> k Hk1 Hk2.
 case: (k = x{m}+_y*5) => E.
  by rewrite !Hb 1..3:/# eq_sym initiE 1:/# /= get_setE 1:/# E /= xorwC /#.
 by rewrite get_setE 1:/# ifF 1:/# -IH /#.
by auto => /> Hy1 Hy2 _ H e k ???; have ->: k=5; smt().
qed.

hoare pround_ref_h _a:
 M._pround_ref :
  a = _a ==> res = keccak_pround_op _a.
proof.
proc; simplify.
while (0 <= y <= 5 /\ #pre /\
       d = keccak_D (keccak_C _a) /\
       forall k, 0 <= k < 5*y => 
        e.[k] = (keccak_pround_op _a).[k]).
 wp; ecall (set_row_ref_h a e b y).
 simplify; ecall (rol_sum_ref_h a y); simplify.
 auto => /> &m Hy1 _ IH Hy2 b Hb e He; split; smt().
wp; ecall (theta_rol_ref_h c).
ecall (theta_sum_ref_h a).
auto => /> &m; split; first smt().
move=> e y ???; have ->: y=5 by smt().
by move=> /= H; apply Array25.ext_eq => k Hk; apply H.
qed.

lemma pround_ref_ll: islossless M._pround_ref.
proof.
proc; inline*.
do 43! unroll for ^while.
by islossless.
qed.

require import List.
import BitEncoding.BitChunking.

abbrev keccak_double_round A i =
 keccak_round_op rc_spec.[2*i+1] (keccak_round_op rc_spec.[2*i] A).

hoare __keccakf1600_ref_h _a:
 M.__keccakf1600_ref :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc.
while (2 <= c <= 24 /\ 2 %| c /\
       keccak_f1600_op _a = foldl keccak_double_round a (range (c %/ 2) 12)).
 wp; ecall (pround_ref_h e).
 wp; ecall (pround_ref_h a).
 auto => /> &m Hc1 _ Hc_2 IH.
 move => Hc2; split; first smt().
 split; first smt().
 move: IH; rewrite (range_cat (c{m} %/ 2 + 1)) 1..2:/#.
 by rewrite /rc_spec rangeS foldl_cat /= => -> /#.
wp; ecall (pround_ref_h e).
wp; ecall (pround_ref_h a).
auto => />; split.
 by rewrite /keccak_f1600_op /range /rc_spec -iotaredE.
move => a c /= ????.
have ->/=: c = 24 by smt().
by rewrite range_geq /=.
qed.

lemma __keccakf1600_ref_ll: islossless M.__keccakf1600_ref.
proof.
proc.
have Hll:= pround_ref_ll.
wp; while (0 <= c <= 24) (23 - c).
 move=> z.
 wp; call pround_ref_ll.
 wp; call pround_ref_ll.
 by auto => /> &m ?_ ? /#.
wp; call pround_ref_ll.
wp; call pround_ref_ll.
by auto => /> c ??? /#.
qed.

phoare __keccakf1600_ref_ph _a:
 [ M.__keccakf1600_ref
 : a = _a
 ==> res = keccak_f1600_op _a
 ] = 1%r.
proof. by conseq __keccakf1600_ref_ll (__keccakf1600_ref_h _a). qed.

lemma keccakf1600_ref_ll: islossless M._keccakf1600_ref.
proof.
proc; inline _keccakf1600_ref.
by call __keccakf1600_ref_ll.
qed.

hoare keccakf1600_ref_h _a:
 M._keccakf1600_ref :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc; inline _keccakf1600_ref.
by call (__keccakf1600_ref_h _a).
qed.
