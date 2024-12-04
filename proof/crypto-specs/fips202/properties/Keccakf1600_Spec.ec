(******************************************************************************
   Keccak1600_Spec.ec:

   Properties of the Keccak1600 specification.

******************************************************************************)
require import AllCore List Int IntDiv.
require StdOrder.
import StdOrder.IntOrder.

require import EclibExtra.

require import FIPS202_Keccakf1600.

require import Array5 Array24.


(* State-matrix indexes *)
lemma idx_bnd x y:
 0 <= idx(x,y) < 25.
proof. by rewrite /idx /= /#. qed.

op invidx (i: int): int*int = (i %% 5, i %/ 5).

lemma invidxK i:
 0 <= i < 25 =>
 idx (invidx i) = i.
proof.
rewrite -(add0z 25) andaE -mem_iota.
by move: i; rewrite -allP -iotaredE /idx /invidx /=.
qed.

lemma idxK x y:
 0 <= x < 5 => 0 <= y < 5 =>
 invidx (idx (x,y)) = (x,y).
proof.
move => Hx; rewrite -(add0z 5) andaE -mem_iota.
move: y; rewrite -allP.
move: Hx; rewrite -(add0z 5) andaE -mem_iota.
by move: x; rewrite -allP -!iotaredE /idx /invidx /=.
qed.

lemma idxK' x y:
 invidx (idx (x,y)) = (x%%5,y%%5).
proof.
by rewrite (:idx(x,y)=idx(x%%5,y%%5)) 1:/# idxK /#.
qed.


(** precomputed rho-offsets *)
op rhotates: int Array25.t =
 Array25.of_list 0 [  0;  1; 62; 28; 27
                   ; 36; 44;  6; 55; 20
                   ;  3; 10; 43; 25; 39
                   ; 41; 45; 15; 21;  8
                   ; 18;  2; 61; 56; 14 ].


(** Round-constants *)
op rc_spec: W64.t Array24.t =
  Array24.of_list
    witness
    (map W64.of_int
      [                   1
      ;               32898
      ; 9223372036854808714
      ; 9223372039002292224
      ;               32907
      ;          2147483649
      ; 9223372039002292353
      ; 9223372036854808585
      ;                 138
      ;                 136
      ;          2147516425
      ;          2147483658
      ;          2147516555
      ; 9223372036854775947
      ; 9223372036854808713
      ; 9223372036854808579
      ; 9223372036854808578
      ; 9223372036854775936
      ;               32778
      ; 9223372039002259466
      ; 9223372039002292353
      ; 9223372036854808704
      ;          2147483649
      ; 9223372039002292232
      ]).


(******************************************************************************
   Functional Specification of Keccakf1600
******************************************************************************)

op keccak_C (A: state): W64.t Array5.t =
 Array5.init (fun x => A.[x+5*0] `^` A.[x+5*1]
                      `^` A.[x+5*2] `^` A.[x+5*3] `^` A.[x+5*4]).

op keccak_D (C: W64.t Array5.t): W64.t Array5.t =
 Array5.init (fun x => C.[(x-1)%%5]
                       `^` (C.[(x+1)%%5] `|<<<|` 1)).

op keccak_theta_op (A: state ): state =
 Array25.init (fun i => A.[i] `^` (keccak_D (keccak_C A)).[i %% 5]).

op keccak_rho_op (A: state): state =
 Array25.init (fun i => A.[i] `|<<<|` rhotates.[i]).

op keccak_pi_op (A: state): state =
 Array25.init (fun i => let (x,y) = invidx i in A.[idx(x+3*y, x)]).

op keccak_chi_op (A: state): state =
 Array25.init
  (fun i => let (x,y) = invidx i in
            A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)])).

op keccak_iota_op c (A: state) =
 A.[0 <- A.[0] `^` c].

op keccak_round_op c (A: state) =
 keccak_iota_op c (keccak_chi_op (keccak_pi_op (keccak_rho_op (keccak_theta_op A)))).

op keccak_f1600_op (A: state) =
 foldl (fun s ir => keccak_round_op rc_spec.[ir] s) A (iota_ 0 24).


(********************
  Correctness proof
*********************)

op keccak_theta_spec (A A': state ): bool =
  all (fun i => A'.[i] = A.[i] `^` (keccak_D (keccak_C A)).[i %% 5]) (iota_ 0 25).

lemma keccak_thetaP (A A': state):
 A' = keccak_theta_op A
 <=> keccak_theta_spec A A'.
proof.
by rewrite /keccak_theta_spec /keccak_theta_op -iotaredE -ext_eq_all /all_eq.
qed.

hoare keccak_theta_h _A:
 Keccakf1600.keccak_theta : a = _A ==> res = keccak_theta_op _A.
proof.
conseq (: _ ==> keccak_theta_spec _A res).
 by move=> /> r /keccak_thetaP.
proc.
swap 2 2.
seq 3: (#pre /\ c = keccak_C _A).
 unroll for 3.
 unroll for 21; unroll for 17; unroll for 13; unroll for 9; unroll for 5; auto => /> .
 by rewrite -ext_eq_all /all_eq /keccak_C /idx /invidx /=.
seq 3: (#pre /\ d = keccak_D c).
 unroll for 3; auto => />.
 by rewrite -ext_eq_all /all_eq /keccak_D /idx /invidx /=; smt(W64.xorwC).
unroll for 2.
unroll for 15; unroll for 12; unroll for 9; unroll for 6; unroll for 3.
wp; skip => &m E @/keccak_theta_spec @/idx /=.
by rewrite -iotaredE /= /#.
qed.

lemma keccak_theta_ll:
 islossless Keccakf1600.keccak_theta.
proof.
islossless.
+ while (true) (5-x) => //.
   move=> z; wp; while (true) (5-y).
    by move=> z'; auto => /> /#.
   by auto => /> /#.
  by auto => /> /#.
+ while (true) (5-x) => //.
   by move=> z; auto => /> /#.
  by auto => /> /#.
+ while (true) (5-x) => //.
   move=> z; wp; while (true) (5-y).
    by move=> z'; auto => /> /#.
   by auto => /> /#.
  by auto => /> /#.
qed.

phoare keccak_theta_ph _A:
 [ Keccakf1600.keccak_theta:
   a = _A ==> res = keccak_theta_op _A
 ] = 1%r.
proof.
by conseq keccak_theta_ll (keccak_theta_h _A).
qed.

op rhotates_perm =
 Array25.of_list 0 [1; 10; 7; 11; 17; 18; 3; 5; 16; 8; 21; 24; 4; 15; 23; 19; 13; 12; 2; 20; 14; 22; 9; 6; 1].

lemma rhotates_permS x y t:
 t \in iota_ 0 24 =>
 (x,y) = invidx rhotates_perm.[t] =>
 rhotates_perm.[t + 1] = idx (y, (2 * x + 3 * y) %% 5).
proof.
by move: t; rewrite -allP -iotaredE /invidx /rhotates_perm /idx /=.
qed.

lemma rhotates_permP t:
 t \in iota_ 0 24 =>
 rhotates.[rhotates_perm.[t]]
 = (t+1)*(t+2) %/ 2 %% 64.
proof.
by move: t; rewrite -allP -iotaredE /rhotates /rhotates_perm /=.
qed.

op keccak_rho_loopI (st:state) k =
 foldl (fun (st:state) i=> st.[rhotates_perm.[i] <- st.[rhotates_perm.[i]] `|<<<|` rhotates.[rhotates_perm.[i]]]) st (iota_ 0 k).

hoare keccak_rho_h _st:
 Keccakf1600.keccak_rho:
  a=_st ==> res = keccak_rho_op _st. 
proof.
proc.
while (0 <= t <= 24 /\
       0 <= x < 5 /\ 0 <= y < 5 /\
       idx(x,y) = rhotates_perm.[t] /\
       a = keccak_rho_loopI _st t).
 auto => /> &m Ht1 _ Hx1 Hx2 Hy1 Hy2 Hidx Ht2; split; first smt().
 split; first smt().
 split.
  rewrite (rhotates_permS x{m} y{m}) //; first smt(mem_iota).
  by rewrite -Hidx idxK /#.
 rewrite /keccak_rho_loopI iotaSr //= foldl_rcons /=; congr; congr.
  by rewrite Hidx.
 by rewrite rhotates_permP; smt(mem_iota).
auto => />; split; first smt(iota0).
move=> t *; have->: t=24 by smt().
rewrite -ext_eq_all /all_eq /= /keccak_rho_op /keccak_rho_loopI.
rewrite initiE 1:// /=.
rewrite -iotaredE /rhotates /rhotates_perm /=.
by rewrite W64_rol0.
qed.

lemma keccak_rho_ll:
 islossless Keccakf1600.keccak_rho.
proof.
islossless.
while (true) (24-t).
 by move=> z; auto => /> /#.
by auto => /> /#.
qed.

phoare keccak_rho_ph _st:
 [ Keccakf1600.keccak_rho:
   a=_st ==> res = keccak_rho_op _st
 ] = 1%r. 
proof.
by conseq keccak_rho_ll (keccak_rho_h _st).
qed.

op keccak_pi_spec (A A': state) =
 all (fun i => let (x,y) = invidx i in A'.[idx(x,y)] = A.[idx(x+3*y, x)]) (iota_ 0 25).

lemma keccak_piP A A':
 A' = keccak_pi_op A
 <=> keccak_pi_spec A A'.
proof.
by rewrite /keccak_pi_spec /keccak_pi_op /idx /invidx -iotaredE -!ext_eq_all /all_eq /=.
qed.

hoare keccak_pi_h _A:
 Keccakf1600.keccak_pi : a = _A ==> res = keccak_pi_op _A.
proof.
conseq (: _ ==> keccak_pi_spec _A res).
 by move=> /> r /keccak_piP.
proc.
while (0 <= x <= 5 /\
       forall j y, 0 <= j < x => 0 <= y < 5 => 
                   a.[idx(j,y)] = b.[idx(j+3*y,j)]).
 wp; while (0 <= y <= 5 /\
            (forall j y, 0 <= j && j < x => 0 <= y && y < 5 => 
                         a.[idx (j,y)] = b.[idx (j+3*y, j)]) /\
            forall k, 0 <= k < y => a.[idx(x,k)] = b.[idx(x+3*k,x)]).
  auto => /> &1 Hy1 _ IH HH Hy2; split; first smt().
  split.
   move => j i *.
   rewrite get_setE 1:/#.
   case: (i=y{1} /\ j=x{1}) => E.
    by rewrite ifT /#.
   smt().
  move=> k Hk1 Hk2.
  rewrite get_setE. 
   by rewrite /idx /#.
  case: (k=y{1}) => E.
   by rewrite E ifT /#.
  by rewrite HH /#.
 auto => /> &m Hx1 Hx2 IH Hx.
 split; first smt().
 move=> A y ???.
 have ->: y=5 by smt().
 move=>IH2A IH2; split; first smt().
 move => /> j y1 *.
 case: (j = x{m}) => E.
  by rewrite E IH2 //= /#.
 by rewrite IH2A //= /#.
auto => /> *. 
split; first smt().
move=> A x ???; have ->: x=5 by smt().
by move => IH; rewrite /keccak_pi_spec -iotaredE /invidx /= /#.
qed.

lemma keccak_pi_ll:
 islossless Keccakf1600.keccak_pi.
proof.
islossless.
while (true) (5-x).
 move=> z; wp; while (true) (5-y).
  by move=> z'; auto => /> /#.
 by auto=> /> /#.
by auto=> /> /#.
qed.

phoare keccak_pi_ph _A:
 [ Keccakf1600.keccak_pi:
   a = _A ==> res = keccak_pi_op _A
 ] = 1%r.
proof.
by conseq keccak_pi_ll (keccak_pi_h _A).
qed.

op keccak_chi_spec (A A': state) =
 forall x y,
  0 <= x < 5 => 0 <= y < 5 =>
    A'.[idx(x,y)]
    = A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)]).

op keccak_chi_spec' (A A': state) =
 all (fun x=> 
       all (fun y=> 
             A'.[idx(x,y)] = A.[idx(x,y)] `^` (invw A.[idx(x+1, y)] `&` A.[idx(x+2, y)]))
           (iota_ 0 5))
     (iota_ 0 5).

lemma keccak_chi_spec_eq A A':
 keccak_chi_spec A A' <=> keccak_chi_spec' A A'.
proof.
rewrite /keccak_chi_spec /keccak_chi_spec'; split.
move=> H; apply/List.allP => x /mem_iota /= Hx.
 by apply/List.allP => y /mem_iota /= Hy; apply H => /#.
move=> /List.allP H x y Hx Hy.
move: (H x _); first smt(mem_iota).
rewrite /= allP => {H} H.
move: (H y _); first smt(mem_iota).
done.
qed.

lemma keccak_chiP A A':
 A' = keccak_chi_op A
 <=> keccak_chi_spec A A'.
proof.
rewrite keccak_chi_spec_eq /keccak_chi_spec' /keccak_chi_op.
by rewrite -ext_eq_all /all_eq /invidx /idx -!iotaredE /= /#.
qed.

hoare keccak_chi_h _A:
 Keccakf1600.keccak_chi : a = _A ==> res = keccak_chi_op _A.
proof.
conseq (: a=_A ==> keccak_chi_spec _A res).
 by move=> /> r /keccak_chiP.
proc.
while (#pre /\ 0 <= x <= 5 /\  
       forall i j, 0 <= i < x => 0 <= j < 5 =>
        b.[idx(i,j)]
           = a.[idx(i,j)] `^`
             (invw a.[idx(i+1,j)] `&` a.[idx(i+2,j)])).
 wp; while (#pre /\ 0 <= y <= 5 /\
            forall j, 0 <= j < y =>
             b.[idx(x,j)]
             = a.[idx(x,j)] `^`
               (invw a.[idx(x+1,j)] `&` a.[idx(x+2,j)])).
  auto => /> &m Hy1 _ H1 Hy2 Hx1 _ H2 Hx2; split.
   move => i j Hi1 Hi2 Hj1 Hj2.
   rewrite /= get_setE 1:/# ifF 1:/#.
   by apply H1.
  split; first smt().
  move=> j Hj1 Hj2.
  case: (j = y{m}) => E.
   by rewrite !E get_setE 1:/# ifT 1://.
  rewrite /= get_setE 1:/# ifF 1:/#.
  by rewrite H2 /#.
 auto => /> &m Hy1 _ H Hy2; split; first smt().
 move=> A k ? H1 ??; have ->: k=5 by smt().
 move=> H2; split; first by smt().
 move=> i j Hi1 Hi2 Hj1 Hj2.
 case: (i = x{m}) => E.
  by rewrite !E H2.
 by rewrite H1 /#.
auto => />; split; first by smt().
move=> A j ???; have ->: j=5 by smt().
done.
qed.

lemma keccak_chi_ll:
 islossless Keccakf1600.keccak_chi.
proof.
proc.
islossless.
while (true) (5-x).
 move=> z; wp; while (true) (5-y).
  by move=> z'; auto => /> /#.
 by auto=> /> /#.
by auto=> /> /#.
qed.

phoare keccak_chi_ph _A:
 [ Keccakf1600.keccak_chi:
   a = _A ==> res = keccak_chi_op _A
 ] = 1%r.
proof.
by conseq keccak_chi_ll (keccak_chi_h _A).
qed.




(** Round-constants *)
op getbit x p = (x %/ 2^p) %% 2.
op resetbit x p = x - getbit x p * 2^p.
op setbit x p = (2^p + resetbit x p).
op flipbit x p = if getbit x p<>0 then resetbit x p else setbit x p.
op xorbit x p b = if b=1 then flipbit x p else x.
op finc x (i:int) =
 let b = x %/ 128 %% 2 in
 xorbit (xorbit (xorbit (xorbit (x*2 %% 256) 0 b) 4 b) 5 b) 6 b.

lemma xorbit_bitset (w:W8.t) i b:
 0 <= i < 8 =>
 to_uint w.[i <- w.[i] ^ b] = xorbit (to_uint w) i (b2i b).
proof.
move=> Hi; rewrite /xorbit.
rewrite /flipbit /setbit /resetbit /getbit.
move: (W8.get_to_uint w i); rewrite Hi /= => <-.
case: b => Eb; last first.
 by rewrite b2i0 /= addbF set_notmod.
by rewrite addbT b2i1 /= W8_to_uint_set // b2i_get /#.
qed.

op keccak_rc_op (t: int): int (*bool*) = 
 (foldl finc 1 (iotared 1 (t%%255))) %% 2.
op keccak_RC_op (ir: int): int (*u64*) =
 (foldl (fun x j => x + keccak_rc_op (j+7*ir) * 2^(2^j-1)) 0 (iotared 0 7)) %% W64.modulus.

lemma rc_spec_correct i:
 0 <= i < 24 =>
 W64.of_int (keccak_RC_op i) = rc_spec.[i].
proof.
move=> Hi; have: i \in iota_ 0 24 by smt(mem_iota).
by move: {Hi} i; rewrite -allP -iotaredE /rc_spec /keccak_RC_op /keccak_rc_op
 /finc /xorbit /flipbit /setbit /resetbit /getbit /=.
qed.

hoare keccak_rc_h _t:
  Keccakf1600.keccak_rc:
  t = _t ==> b2i res = keccak_rc_op _t.
proof.
proc.
sp; if; last first.
 by auto => />; rewrite /keccak_rc_op => -> /=.
wp; while (1 <= i <= t%%255+1 /\ to_uint r = foldl finc 1 (iotared 1 (i-1))).
 auto => &m H r8 r2; move: H => /> Hi1 _ IH Hi2; split; first smt().
 rewrite !xorbit_bitset //. 
 rewrite iotaredE (:i{m}=i{m}-1+1) 1:/# iotaSr 1:/#.
 rewrite foldl_rcons -iotaredE -IH addrC /finc /=.
 by rewrite /r8 b2i_get /r2 //  to_uint_shl //=. 
auto => /> Ht; split; first smt(). 
move=> i r ???; have ->: i=_t%%255+1 by smt().
rewrite /keccak_rc_op => <-.
by rewrite get_to_uint /#.
qed.

hoare keccak_RC_h _i:
  Keccakf1600.keccak_RC:
  0 <= ir < 24 /\ ir = _i ==> res = rc_spec.[_i].
proof.
conseq (:_ ==> res = W64.of_int (keccak_RC_op _i)).
 by move=> &m => />; smt(rc_spec_correct).
proc.
while (0 <= j <= keccak_l+1 /\
       to_uint rc = foldl (fun (x j : int) => x + keccak_rc_op (j + 7 * ir) * 2 ^ (2 ^ j - 1)) 0 (iota_ 0 j) /\
       forall k, 2^j-1 <= k => !rc.[k]).
 wp; ecall (keccak_rc_h (j + 7 * ir)).
 auto => /> &m Hj1 _ IH Hbnd Hj2 r H; split; first smt().
 have [??]: 0 <= 2 ^ j{m} - 1 && 2 ^ j{m} - 1 < 64.
  split; first smt(gt0_pow2). 
  by have /#: 2 ^ j{m} <= 2^6 by apply ler_weexpn2l => /#.
 split; last first.
  rewrite exprS 1:/#.
  move=> k Hk.
  rewrite get_setE 1:/# ifF 1:/#.
  by apply Hbnd => /#. 
 rewrite iotaSr 1:/# foldl_rcons -IH /= -H.
 by rewrite W64_to_uint_set /#.
auto => /> ??; split.
 by rewrite -iotaredE /=.
move=> j rc ???; have ->/=: j=7 by smt().
rewrite /keccak_RC_op iotaredE => <-.
by rewrite to_uint_mod to_uintK.
qed.


op keccak_iota_spec c (A A': state) =
 A' = A.[0 <- A.[0] `^` c].

lemma keccak_iotaP c A A':
 A' = keccak_iota_op c A
 <=> keccak_iota_spec c A A'
by done.

hoare keccak_iota_h _ir _A:
 Keccakf1600.keccak_iota : a = _A /\ ir = _ir /\ 0 <= ir < 24 ==> res = keccak_iota_op rc_spec.[_ir] _A.
proof.
proc.
by wp; ecall (keccak_RC_h ir); auto => /> *.
qed.

lemma keccak_rc_ll:
 islossless Keccakf1600.keccak_rc.
proof.
islossless.
while (true) (255-i).
 by move=> z; auto => /> /#.
by auto => /> * /#.
qed.

lemma keccak_iota_ll:
 islossless Keccakf1600.keccak_iota.
proof.
islossless.
while (true) (keccak_l+1-j).
 by move=> z; wp; call keccak_rc_ll; auto => /> /#.
by auto => /> /#.
qed.

phoare keccak_iota_ph _ir _A:
 [ Keccakf1600.keccak_iota:
   a = _A /\ ir = _ir /\ 0 <= ir < 24
   ==> res = keccak_iota_op rc_spec.[_ir] _A
 ] = 1%r.
proof.
by conseq keccak_iota_ll (keccak_iota_h _ir _A).
qed.


hoare keccak_round_h _ir _A:
 Keccakf1600.keccak_Rnd:
 st = _A /\ ir=_ir /\ 0 <= ir < 24
 ==> res = keccak_round_op rc_spec.[_ir] _A.
proof.
proc.
ecall (keccak_iota_h ir st).
ecall (keccak_chi_h st).
ecall (keccak_pi_h st).
ecall (keccak_rho_h st).
ecall (keccak_theta_h st).
by auto => />.
qed.

lemma keccak_round_ll:
 islossless Keccakf1600.keccak_Rnd.
proof.
proc.
call keccak_iota_ll.
call keccak_chi_ll.
call keccak_pi_ll.
call keccak_rho_ll.
by call keccak_theta_ll.
qed.

phoare keccak_round_ph _ir _A:
 [ Keccakf1600.keccak_Rnd:
   st = _A /\ ir=_ir /\ 0 <= ir < 24
   ==> res = keccak_round_op rc_spec.[_ir] _A
 ] = 1%r.
proof.
by conseq keccak_round_ll (keccak_round_h _ir _A).
qed.

hoare keccak_f1600_h _A:
 Keccakf1600.keccak_f1600 : st = _A ==> res = keccak_f1600_op _A.
proof.
proc.
inline Keccakf1600.keccak_p1600.
wp; while (0 <= ir <= 24 /\
           st0 = foldl (fun s i => keccak_round_op rc_spec.[i] s) _A (iota_ 0 ir)).
 wp; ecall (keccak_round_h ir st0).
 auto => /> *; split; first smt().
 by rewrite iotaSr // foldl_rcons.
auto => />; split; first by rewrite iota0.
by move => ir ???; have ->: ir=24 by smt().
qed.

lemma keccak_f1600_ll:
 islossless Keccakf1600.keccak_f1600.
proof.
islossless.
while (true) (24-ir).
 by move=> z; wp; call keccak_round_ll; auto => /#.
by auto => /> /#.
qed.

phoare keccak_f1600_ph _A:
 [ Keccakf1600.keccak_f1600:
   st = _A ==> res = keccak_f1600_op _A
 ] = 1%r.
proof.
by conseq keccak_f1600_ll (keccak_f1600_h _A).
qed.

