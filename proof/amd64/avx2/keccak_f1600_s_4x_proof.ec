(******************************************************************************
   Keccak_f1600_s_4x_proof.ec:

   Correctness proof for the 4x_AVX2 implementation


   The 4x_AVX2 implementation is essentially a 4-way SIMD implementation of the
  REF1 scalar implementation. The proof strategy is hence to prove equivalence
  between any lane with REF1, and deriving the parallel execution from generic
  HL reasoning.

******************************************************************************)
require import List Real Distr Int IntDiv CoreMap.


require import WArray768.

require import Keccak_f1600_Spec_facts.
require import Keccak_f1600_s_spec_proof.
require import Keccak_f1600_s_ref1_proof.


from JExtract require import Jextracted.


(** lemmata (move?) *)

(* add this to JWord, and relax the hyp. in rol_xor_shft accordingly *)
lemma rol_or_shft (w : W64.t) (r : int):
   0 <= r && r < 64 =>
   w `|<<<|` r = (w `<<` (of_int r)%W8) `|` (w `>>` (of_int (64 - r))%W8).
proof.
move => Hr; apply W64.ext_eq => i Hi.
rewrite rolwE Hi /= shlwE Hi /= shrwE Hi /=.
smt(W64.get_out).
qed.


import Ring.IntID.

lemma bits8_bits (w: W256.t) (k: int):
 w \bits8 k = W8.bits2w (bits w (8*k) 8).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

lemma bits64_bits (w: W256.t) (k: int):
 w \bits64 k = W64.bits2w (bits w (64*k) 64).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

(* useful to eval constants... *)
lemma bits8_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits8 k
 = W8.of_int (to_uint w %/ (2^(8*k)) %% 2^8).
proof.
move=> Hk; rewrite bits8_bits.
apply W8.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W8.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma bits64_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits64 k
 = W64.of_int (to_uint w %/ (2^(64*k)) %% 2^64).
proof.
move=> Hk; rewrite bits64_bits.
apply W64.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W64.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma get256_init256 (a: W256.t Array24.t) i:
 0 <= i < 24 =>
 get256 (init256 ("_.[_]" a)) i = a.[i].
proof.
move=> Hi; rewrite /get256_direct /init256 -(unpack8K a.[i]).
congr; apply W32u8.Pack.ext_eq => x Hx.
rewrite initiE //= unpack8E !initiE 1..2:/# /=; congr.
 congr; smt().
smt().
qed.



(** Packed 4x-state *)
type state4x = W256.t Array25.t.

op (\a25bits64) (a: state4x) (k: int): state =
 Array25.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op (\a24bits64) (a: W256.t Array24.t) (k: int): W64.t Array24.t =
 Array24.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op (\a5bits64) (a: W256.t Array5.t) (k: int): W64.t Array5.t =
 Array5.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op a25pack4 (l: state list): state4x =
 Array25.init (fun i => pack4 (map (fun (s: state) => s.[i]) l)).

op a25unpack4 (st4: state4x): state list =
 map (fun k=> st4 \a25bits64 k) (iota_ 0 4).

lemma a25bits64iE x k i:
 0 <= i < 25 =>
 (x \a25bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a24bits64iE x k i:
 0 <= i < 24 =>
 (x \a24bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a5bits64iE x k i:
 0 <= i < 5 =>
 (x \a5bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a25unpack4K s4:
 a25pack4 (a25unpack4 s4) = s4.
proof.
rewrite /a25pack4 /a25unpack4.
apply ext_eq => i Hi; rewrite initiE //=.
rewrite -iotaredE /= !a25bits64iE //=.
rewrite -{5}(unpack64K s4.[i]); congr.
by rewrite unpack64E init_of_list -iotaredE /=. 
qed.

lemma a25pack4_bits64 k (stl: state list):
 0 <= k < 4 =>
 a25pack4 stl \a25bits64 k = nth st0 stl k.
proof.
move=> Hk; apply Array25.ext_eq => i Hi.
rewrite mapiE //= initiE //= pack4bE //=.
rewrite of_listE initiE //=.
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

op a5pack4 (l: (W64.t Array5.t) list): W256.t Array5.t =
 Array5.init (fun i => pack4 (map (fun (x: W64.t Array5.t) => x.[i]) l)).

op match_state4x (st0 st1 st2 st3: state) (st4x: state4x) =
 st4x = a25pack4 [st0; st1; st2; st3].

lemma a25pack4_eq stl st4x:
 a25pack4 stl = st4x
 <=>
 all (fun k=>st4x \a25bits64 k = nth st0 stl k) (iota_ 0 4).
proof.
split.
 move => <-; apply/List.allP => k. 
 rewrite mem_iota => Hk /=; apply a25pack4_bits64; smt().
move=> /List.allP H.
apply ext_eq => i Hi.
rewrite initiE //=.
rewrite -(unpack64K st4x.[i]); congr.
apply W4u64.Pack.ext_eq => k Hk.
rewrite of_listE unpack64E !initiE //=.
rewrite -a25bits64iE // H; first smt(mem_iota).
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

lemma a5bits64_set (c: W256.t Array5.t) x y i:
 0 <= i < 4 =>
 0 <= x < 5 =>
 c.[x <- y] \a5bits64 i
 = (c \a5bits64 i).[x <- y \bits64 i].
proof.
move=> Hi Hx; apply Array5.ext_eq => j Hj.
rewrite a5bits64iE 1:// !get_setE 1..2:/#.
case: (j=x) => E //.
by rewrite a5bits64iE.
qed.

lemma xorw_bits64 (w1 w2: W256.t) k:
 0 <= k < 4 =>
 w1 `^` w2 \bits64 k = (w1 \bits64 k) `^` (w2 \bits64 k).
proof.
move=> Hk; rewrite -{1}(unpack64K w1) -{1}(unpack64K w2). 
by rewrite xorb4u64E pack4bE // map2iE // !unpack64E !initiE.
qed.

lemma invw_bits64 (w: W256.t) k:
 0 <= k < 4 =>
 invw w \bits64 k = invw (w \bits64 k).
proof. by move=> Hk; rewrite -{1}(unpack64K w) invw64E //. qed.


(******************************************************************************
   Equivalence between lane '_k' and REF1
******************************************************************************)

lemma theta_sum_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__theta_sum_4x_avx2 ~ M.__theta_sum_ref1:
         a{1} \a25bits64 _k = a{2} ==> res{1} \a5bits64 _k = res{2} ].
proof.
move=> Hk; proc.
while (={y} /\ 1<=y{2}<=5 /\ #pre /\
       c{1} \a5bits64 _k = c{2}).
 wp; while (#pre /\ ={x} /\ 0<=x{2}<=5).
  auto => /> &1 &2 Hy1 _ Hy2 Hx1 _ Hx2.
  split.
   rewrite a5bits64iE 1:/# a5bits64_set 1..2:/#.
   by rewrite  a25bits64iE 1:/# xorw_bits64.
  smt().
 auto => />; smt().
wp; while (={x} /\ 0<=x{2}<=5 /\ #pre /\
           forall i, 0<=i<x{2} => (c{1} \a5bits64 _k).[i] = c{2}.[i]).
 auto => /> &1 &2 Hx1 _ H Hx2; split; first smt().
 move=> i Hi1 Hi2.
 case: (i = x{2}) => E.
  rewrite !get_setE 1:/# E /= a5bits64_set 1..2:/#.
  by rewrite get_setE 1:/# /= a25bits64iE 1:/#.
 rewrite get_setE 1:/# E /= -H 1:/# a5bits64_set 1..2:/#.
 by rewrite get_setE 1:/# ifF 1:/#.
auto => />; split; first smt().
move=> cL cR x _?_?; have ->: x=5 by smt().
move=> H; apply Array5.ext_eq => i Hi.
by rewrite -H 1:/#.
qed.

lemma rol8P _x _k:
 0 <= _k < 4 =>
 ((JModel.VPSHUFB_256 _x ROL8) \bits64 _k)
 = (_x \bits64 _k) `|<<<|` 8.
proof.
move=> Hk; have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/List.allP; rewrite -iotaredE /=.
rewrite /JModel.VPSHUFB_256 /JModel.VPSHUFB_128 /JModel.VPSHUFB_128_B /=.
rewrite !bits8_red // !of_uintK /=.
by rewrite -!all_eqP /all_eq /=.
qed.

lemma rol56P _x _k:
 0 <= _k < 4 =>
 ((JModel.VPSHUFB_256 _x ROL56) \bits64 _k) = (_x \bits64 _k) `|<<<|` 56.
proof.
move=> Hk; have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/List.allP; rewrite -iotaredE /=.
rewrite /JModel.VPSHUFB_256 /JModel.VPSHUFB_128 /JModel.VPSHUFB_128_B /=.
rewrite !bits8_red // !of_uintK /=.
by rewrite -!all_eqP /all_eq /=.
qed.

(* possibly useful if function __rol_4x_avx2 is include in library... 
lemma rol_4x_h _k _x _r:
 0 <= _k < 4 => 
 hoare [ M.__rol_4x_avx2
       : x = _x /\ r = _r%%64 /\ r8 = ROL8 /\ r56 = ROL56
         ==> res \bits64 _k = (_x \bits64 _k) `|<<<|` _r%%64 ].
proof.
move => Hk; proc; simplify.
case: (r=0).
 by rcondf 1; auto => /> ->; rewrite ROL_64_by0.
case: (r=8).
 rcondt 1 => //; rcondt 1 => //.
 by auto => /> *; rewrite rol8P /#.
case: (r=56). 
 rcondt 1 => //; rcondf 1 => //; rcondt 1 => //.
 by auto => /> *; rewrite rol56P /#.
rcondt 1 => //; rcondf 1 => //; rcondf 1 => //.
auto => /> *.
have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
move: _k; apply/allP; rewrite -iotaredE /=.
rewrite /VPSRL_4u64 /VPSLL_4u64 /=.
smt(W64.orwC rol_or_shft).
qed.

lemma rol_4x_ll: islossless M.__rol_4x_avx2
 by islossless.

lemma rol_4x_ph _k _x _r:
 0 <= _k < 4 => 
 phoare [ M.__rol_4x_avx2
        : x = _x /\ r = _r%%64 /\ r8 = ROL8 /\ r56 = ROL56
          ==> res \bits64 _k = (_x \bits64 _k) `|<<<|` _r%%64 ] = 1%r.
proof. by move=> Hk; conseq rol_4x_ll (rol_4x_h _k _x _r Hk). qed.
*)

lemma rol_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__rol_4x_avx2 ~ M.__rol_u64_ref1:
         x{1} \bits64 _k = x{2}
         /\ r{1}=i{2} /\ 0 <= i{2} < 64
         /\ r8{1} = ROL8 /\ r56{1} = ROL56
         ==> res{1} \bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
if => //.
auto => /> &1 &2 Hi1 Hi2 _; split.
 by move => _; rewrite rol8P // /ROL_64 /shift_mask /=.
move=> _; split.
 by move => _; rewrite rol56P // /ROL_64 /shift_mask /=.
move=> _.
have {Hk}: _k \in iota_ 0 4 by smt(mem_iota).
rewrite ROL_64_val modz_small 1:/#.
move: _k; apply/List.allP; rewrite -iotaredE /=.
by rewrite /VPSRL_4u64 /VPSLL_4u64 /=; smt(W64.orwC rol_or_shft).
qed.

lemma theta_rol_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__theta_rol_4x_avx2 ~ M.__theta_rol_ref1:
         c{1} \a5bits64 _k = c{2}
         /\ r8{1} = ROL8
         /\ r56{1} = ROL56
         ==> res{1} \a5bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (={x} /\ 0<=x{2}<=5 /\ #pre /\
       forall i, 0<=i<x{2} => (d{1} \a5bits64 _k).[i] = d{2}.[i]).
 wp; call (rol_4x_eq _k Hk).
 auto => /> &1 &2 Hx1 _ IH Hx2.
 rewrite !get_setE 1..2:/# /=; split.
  by rewrite a5bits64iE 1:/#.
 move=> _ d1; split; first smt().
 move => i Hi1 Hi2.
 case: (i=x{2}) => E.
  rewrite !get_setE 1..3:/# E /=.
  rewrite a5bits64iE 1:/# get_setE 1:/# /=.
  by rewrite a5bits64iE 1:/#.
 rewrite a5bits64iE 1:/#.
 rewrite !get_setE 1..4:/# /= E /=.
 by rewrite -IH 1:/# a5bits64iE 1:/#.
auto => />; split; first smt().
move=> d1 d2 x ?_??; have ->: x=5 by smt().
by move=> H; apply Array5.ext_eq => /#.
qed.

lemma rol_sum_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__rol_sum_4x_avx2 ~ M.__rol_sum_ref1:
         a{1} \a25bits64 _k = a{2} /\ d{1} \a5bits64 _k = d{2}
         /\ ={y}
         /\ r8{1} = ROL8
         /\ r56{1} = ROL56
         ==> res{1} \a5bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (={x} /\ 0<=x{2}<=5 /\ #pre /\
       forall i, 0<=i<x{2} => (b{1} \a5bits64 _k).[i] = b{2}.[i]).
 wp; call (rol_4x_eq _k); wp.
 ecall {1} (rhotates_spec_ph x_{1} y_{1}).
 ecall {2} (rhotates_spec_ph x_{2} y_{2}).
 auto => /> &1 &2 Hx1 _ IH Hx2; split; first smt().
 move=> _ _; split.
  by rewrite !get_setE 1..4:/# /= a5bits64iE 1:/# a25bits64iE 1:/# -rhotates_idx_mod64 /#.
 move=> *; split; first smt(). 
 move => i Hi1 Hi2.
 case: (i=x{2}) => E.
  rewrite get_setE 1:/# E /=.
  by rewrite a5bits64iE 1:/# get_setE 1:/# /=.
 rewrite a5bits64iE 1:/#.
 rewrite !get_setE 1..2:/# /= E /=.
 by rewrite -IH 1:/# a5bits64iE 1:/#.
auto => />; split; first smt().
move=> bL bR x ?_??; have ->: x=5 by smt().
by move => H; apply Array5.ext_eq => /#.
qed.

lemma set_row_4x_eq _k _y:
 0 <= _k < 4 =>
 equiv [ M.__set_row_4x_avx2 ~ M.__set_row_ref1:
         (forall i, 0 <= i < 5*y{2} => (e{1} \a25bits64 _k).[i] = e{2}.[i])
         /\ b{1} \a5bits64 _k = b{2}
         /\ ={y} /\ y{2}=_y /\ 0 <= _y < 5 /\ rc{1} \bits64 _k = s_rc{2}
         ==> forall i, 0 <= i < 5*(_y+1) => (res{1} \a25bits64 _k).[i] = res{2}.[i] ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ ={x} /\ 0 <= x{2} <= 5 /\
       forall i, 0 <= i < x{2}+y{2}*5 =>
        (e{1} \a25bits64 _k).[i] = e{2}.[i]).
 wp; ecall {2} (ANDN_64_ph b.[x1]{2} b.[x2]{2}).
 auto => /> &1 &2 Hy1 Hy2 H Hx1 _ IH Hx2; split.
  move=> Ex Ey; split; first smt().
  move => i ??; have ->: i=0 by smt().
  rewrite !a25bits64iE 1:/# !a5bits64iE 1..3:/# !get_setE 1..2:/# /=.
  by rewrite invw_bits64 //.
 move=> Exy; split.
  move=> i Hi1 Hi2.
  rewrite a25bits64iE 1:/# !get_setE 1..2:/# !ifF 1..2:/# -IH 1:/#.
  by rewrite a25bits64iE /#.
 split; first smt().
 move=> i Hi1 Hi2.
 case: (i=x{2}+_y*5) => E.
  rewrite get_setE 1:/# E /= a25bits64iE 1:/# !a5bits64iE 1..3:/#.
  by rewrite get_setE 1:/# /= invw_bits64 //.
 rewrite a25bits64iE 1:/# !get_setE 1..2:/# E /= -IH 1:/#.
 by rewrite a25bits64iE /#.
auto => /> &1 &2 H ??; split; first smt().
move=> eL eR x ? _ _ ??; have ->: x=5 by smt().
by move=> IH /#.
qed.

lemma round_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__round_4x_avx2 ~ M.__round_ref1:
         a{1} \a25bits64 _k = a{2}
         /\ rc{1} \bits64 _k = s_rc{2}
         /\ r8{1} = ROL8
         /\ r56{1} = ROL56
         ==> res{1} \a25bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ ={y} /\ 0 <= y{2} <= 5 /\
       d{1} \a5bits64 _k = d{2} /\
       forall i, 0 <= i < 5*y{2} => (e{1}\a25bits64 _k).[i] = e{2}.[i]).
 exlim y{2} => _y.
 wp; call (set_row_4x_eq _k _y Hk).
 call (rol_sum_4x_eq _k Hk).
 by auto => /> /#.
wp; call (theta_rol_4x_eq _k Hk).
call (theta_sum_4x_eq _k Hk); auto => /> &1 &2; split; first smt().
move=> eL eR y ? _ ??; have ->: y=5 by smt().
by move=> H; apply Array25.ext_eq => i Hi /#.
qed.

lemma keccakf1600_4x_eq _k:
 0 <= _k < 4 =>
 equiv [ M.__keccakf1600_4x_avx2 ~ M.__keccakf1600_ref1:
         a{1} \a25bits64 _k = a{2}
         ==> res{1} \a25bits64 _k = res{2} ].
proof.
move=> Hk; proc; simplify.
while (#pre /\ r8{1}=ROL8 /\ r56{1}=ROL56 /\
       rC{1} \a24bits64 _k = s_RC{2} /\
       to_uint c{1}=32*to_uint c{2} /\
       2 %| to_uint c{2} /\ 2 <= to_uint c{2} <= 24).
 wp; call (round_4x_eq _k Hk).
 wp; call (round_4x_eq _k Hk).
 auto => /> &1 &2; rewrite !ultE !of_uintK /= => Ec Hcdiv Hc1 _ _ Hc2.
 rewrite !Ec; split.
  by rewrite get256_init256 1:/# a24bits64iE /#.
 move => _; split.
  by rewrite (:32*to_uint c{2}+32=32*(to_uint c{2}+1)) 1:/# get256_init256 1:/# a24bits64iE /#.
 by move => _; rewrite !to_uintD_small /#.
wp; call (round_4x_eq _k Hk).
wp; call (round_4x_eq _k Hk).
auto; move: Hk => /> Hk1 Hk2.
have Hk: _k \in iota_ 0 4 by smt(mem_iota).
split.
 rewrite {1}(:0=32*0) // get256_init256 1:/# get_of_list //=.
 by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /= !bits64_red 1..4:/# !of_uintK /=.
move=> _; split.
 rewrite {1}(:32=32*1) // get256_init256 1:/# get_of_list //=.
 by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /= !bits64_red 1..4:/# !of_uintK /=.
move=> _; apply Array24.ext_eq => i Hi.
rewrite a24bits64iE 1://.
have: i\in iota_ 0 24 by smt(mem_iota).
move: {Hi} i; rewrite -allP -iotaredE /= !bits64_red // !of_uintK.
by move: {Hk1 Hk2} _k Hk; rewrite -allP -iotaredE /=.
qed.

(******************************************************************************
   Lift lane-equivalence into 4-way parallel execution
******************************************************************************)

op map_state4x (f:state->state) (st:state4x): state4x =
 a25pack4 (map f (a25unpack4 st)).

lemma map_state4x_neq r a:
 r <> map_state4x keccak_f1600_op a
 <=> (r \a25bits64 0) <> keccak_f1600_op (a \a25bits64 0) \/
     (r \a25bits64 1) <> keccak_f1600_op (a \a25bits64 1) \/
     (r \a25bits64 2) <> keccak_f1600_op (a \a25bits64 2) \/
     (r \a25bits64 3) <> keccak_f1600_op (a \a25bits64 3).
proof.
rewrite /map_state4x eq_sym a25pack4_eq -iotaredE /=.
rewrite !(nth_map st0); first 4 by rewrite /a25unpack4 size_map size_iota.
by rewrite /a25unpack4 -iotaredE /= /#.
qed.

hoare __keccakf1600_4x_h (_a: state4x) (_c: W64.t):
 M.__keccakf1600_4x_avx2 :
 a = _a
 ==> res = map_state4x keccak_f1600_op _a.
proof.
bypr => &m ->.
have ->:
 Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
   : res <> map_state4x keccak_f1600_op _a ]
 = Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
     : predU
        (predU 
          (fun r=> r \a25bits64 0 <> keccak_f1600_op (_a \a25bits64 0))
          (fun r=> r \a25bits64 1 <> keccak_f1600_op (_a \a25bits64 1)))
        (predU
          (fun r=> r \a25bits64 2 <> keccak_f1600_op (_a \a25bits64 2))
          (fun r=> r \a25bits64 3 <> keccak_f1600_op (_a \a25bits64 3))) res].
 rewrite Pr [mu_eq] 2:/#.
 by move => &hr; rewrite /predU /= map_state4x_neq /#.
have L: forall (p1 p2: state4x -> bool),
 Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
   : predU p1 p2 res ] = 0%r
 <=>
 Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
   : p1 res ] = 0%r
 /\ Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
      : p2 res ] = 0%r.
 move=> p1 p2; rewrite /predU /=.
 rewrite Pr [mu_or].
 have ?: Pr[M.__keccakf1600_4x_avx2(_a) @ &m : p1 res /\ p2 res]
         <= Pr[M.__keccakf1600_4x_avx2(_a) @ &m : p1 res ].
  by rewrite Pr [mu_sub] /#.
 have ?: Pr[M.__keccakf1600_4x_avx2(_a) @ &m : p1 res /\ p2 res]
         <= Pr[M.__keccakf1600_4x_avx2(_a) @ &m : p2 res ].
  by rewrite Pr [mu_sub] /#.
 smt(mu_bounded).
rewrite !L /predU /= => {L}.
have: all (fun k => 
            Pr[ M.__keccakf1600_4x_avx2(_a) @ &m
              : res \a25bits64 k <> keccak_f1600_op (_a \a25bits64 k)] = 0%r)
          (iota_ 0 4); last by rewrite -iotaredE /=.
apply/List.allP => k /mem_iota /= Hk.
byphoare (: a = _a ==> _) => //.
hoare; simplify.
conseq (keccakf1600_4x_eq k _) (keccakf1600_ref1_h (_a \a25bits64 k)); last smt().
 move=> />.
 by exists (_a \a25bits64 k) => />.
by move=> />.
qed.
