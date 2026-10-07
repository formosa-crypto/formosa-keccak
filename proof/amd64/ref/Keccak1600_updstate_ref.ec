(******************************************************************************
   Keccak1600_updstate_ref.ec:

   Correctness of the single-lane "updstate" (streaming) Keccak1600
   procedures (src/fips202/ref/keccak1600_updstate{,_ASIZE}.jinc):
   init / absorb (memory and array buffers) / finish / squeeze (memory and
   array buffers).

   The state carries a status word (see common/Keccak1600_updstate.ec) and the
   contracts are stated with the streaming predicates of that file:
     init      ==> absorbing_spec r8 tb [] res
     absorb    absorbing_spec r8 tb l st ==> absorbing_spec r8 tb (l ++ input) res
     finish    absorbing_spec r8 tb l st ==> squeezing_spec r8 (ABSORB1600 tb r8 l) 0 res
     squeeze   squeezing_spec r8 st0 k st ==> output = sqstream r8 st0 k len
                                            /\ squeezing_spec r8 st0 (k+len) res
   The memory-buffer procedures are proved first, against Keccak1600_Jazz.M;
   the array-buffer ones in the abstract theory KeccakUpdstateRef (parameter
   _ASIZE), whose module MM copies the extracted code (checked at _ASIZE = 999
   by extracted/Keccak1600_updstate_ref_checkXtr.ec).
   The proofs hold for every permutation choice: the permutation is called
   through the dispatcher `_keccakf1600`, whose contract `keccakf1600_h`
   covers all its branches.  The add/dump procedures keep the `HAS_AVX2`
   dispatch symbolic (both branches are proved), as in
   Keccak1600_fixedsizes_ref.ec.  `_finish_updstate` and `ststatus_updstate`
   are proved in common/Keccak1600_updstate_finish.ec.
******************************************************************************)

require import AllCore List Int IntDiv StdOrder.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray208.
from JazzEC require import Array3 Array25 Array26.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

require import Keccak1600_ref Keccakf1600.
require import Keccak1600_statebytes Keccak1600_subreadwrite Keccak1600_updstate.
require import Keccak1600_updstate_finish.

import IntOrder.


(* ========================================================================= *)
(* Init (finish and the status export: Keccak1600_updstate_finish.ec)        *)
(* ========================================================================= *)

lemma init_updstate_ll: islossless M._init_updstate.
proof. by proc; wp; call state_init_ll; auto. qed.

hoare init_updstate_h _r64 _tb:
 M._init_updstate
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec (8 * _r64) _tb [] res.
proof.
proc; wp; ecall (state_init_h (8 * _r64)); auto => &hr [#] -> -> H0 H1 /=.
split; first smt().
move=> _ kst Hk.
rewrite /absorbing_spec /=.
split.
+ have -> : Array25.init (fun i => ((Array26.init (fun i => if 0 <= i < 25 then kst.[i] else st{hr}.[i])).[25 <- (zeroextu64 _tb `<<` W8.of_int 8) + zeroextu64 (W8.of_int ((_r64 - 1) %% 256)) `<<` W8.of_int 8]).[i]) = kst.
  + by apply Array25.tP => i Hi; rewrite Array25.initiE //= Array26.get_setE 1:/# ifF 1:/# Array26.initiE 1:/# /= ifT /#.
  by rewrite -pabsorb_spec_refE.
rewrite (: (_r64 - 1) %% 256 = _r64 - 1) 1:/# init_status 1:/#.
by apply encode_ststatusE.
qed.

phoare init_updstate_ph _r64 _tb:
 [ M._init_updstate
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec (8 * _r64) _tb [] res
 ] = 1%r.
proof. by conseq init_updstate_ll (init_updstate_h _r64 _tb). qed.


(* ========================================================================= *)
(* Memory-buffer absorb and squeeze                                          *)
(* ========================================================================= *)

lemma add_m_updstate_ll: islossless M._add_m_updstate.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
if.
+ seq 2: true => //; first by while true (upto + 32 - newat) => [z|]; auto => /#.
  by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_m_updstate_h _mem _st _at _buf _upto:
 M._add_m_updstate
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf = _buf /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ res = (addstate_at _st _at (memread _mem _buf (_upto - _at)), _upto, _buf + (_upto - _at)).
proof.
proc => /=; pose L := memread _mem _buf (_upto - _at).
seq 1 : #pre; first by inline *; auto.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2; rewrite (W64.to_uint_and_mod 3) // W64.of_uintK; smt(modz_small pow2_64).
seq 1 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 Hk; split; first smt().
    by exists _at; split => //; apply addstate_spec_init => //; smt(size_memread).
  wp; ecall (m_rlen_read_upto8_h buf len); wp; skip => /> &hr H0 H1 H2 Hk Hnz.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
  move=> _ [buf2 t] /= Hs Hbuf2.
  rewrite W64.shl_shlw 1:/# set64_addstate_at 1:/#.
  pose base := 8 * (_at %/ 8).
  have Hb : _at - base = _at %% 8 by smt().
  have M := msubread_rlen _mem t base _at _buf (_upto - _at) _ _ Hs; 1,2: smt().
  rewrite Hb in M.
  have S0 : addstate_spec _st _at L 0 base _buf _buf _st _at (_upto - _at) 0.
  + by apply addstate_spec_init => //; smt(size_memread).
  have S1 := addstate_msubread_u64 _mem (t `<<<` 8 * (_at %% 8)) base _st _at _buf (_upto - _at) 0 _st _at _buf (_upto - _at) 0 (base + 8) _ _ _ _ _ _ _ _ _ S0 M; 1..5: smt().
  split => Hc.
  + have Emin : min (_upto - _at) (base + 8 - _at) = base + 8 - _at by smt().
    move: S1; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: _upto - _at - (base + 8 - _at) = _upto - (base + 8)) 1:/# => S1.
    do split; 1..3: smt().
    exists (base + 8); split; first smt().
    by rewrite (: _buf + 8 - _at %% 8 = _buf + (base + 8 - _at)) 1:/#.
  have Emin : min (_upto - _at) (base + 8 - _at) = _upto - _at by smt().
  move: S1; rewrite Emin (: _at + (_upto - _at) = _upto) 1:/# (: _upto - _at - (_upto - _at) = 0) 1:/# => S1.
  exists (base + 8); split; first smt().
  by rewrite Hbuf2 (: min 8 (max 0 (_upto - _at)) = _upto - _at) 1:/#.
seq 2 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8
         /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0).
+ sp; if.
  seq 2 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 32 /\ newat = at + 32 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0).
  + while (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 32 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0); last by auto => /#.
    auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
    rewrite xorwC set256_addstate_at 1:/#.
    have Hal : at{hr} %% 8 = 0 by smt().
    do 3!(split; first smt()).
    exists (sz + 32); split; first smt().
    have Hs : size (u256bytes (loadW256 _mem buf{hr})) = 32 by rewrite /u256bytes size_to_list.
    apply (addstate_spec_fullword L (u256bytes (loadW256 _mem buf{hr})) sz _st _at 0 st{hr} _buf buf{hr} at{hr} (_upto - at{hr}) 0 (sz + 32) (buf{hr} + 32) (at{hr} + 32) (_upto - (at{hr} + 32))) => //; rewrite ?Hs; 1,2: smt().
    by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) 1:/#; apply loadW256_memread; smt().
  seq 2 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 16 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0).
  + seq 1 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 32 /\ newat = at + 16 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0); first by auto => /#.
    if; last by auto => /#.
    auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt -> [sz [Hsz IH]] Hc /=.
    rewrite xorwC set128_addstate_at 1:/#.
    have Hal : at{hr} %% 8 = 0 by smt().
    do 4!(split; first smt()).
    exists (sz + 16); split; first smt().
    have Hs : size (u128bytes (loadW128 _mem buf{hr})) = 16 by rewrite /u128bytes size_to_list.
    apply (addstate_spec_fullword L (u128bytes (loadW128 _mem buf{hr})) sz _st _at 0 st{hr} _buf buf{hr} at{hr} (_upto - at{hr}) 0 (sz + 16) (buf{hr} + 16) (at{hr} + 16) (_upto - (at{hr} + 16))) => //; rewrite ?Hs; 1,2: smt().
    by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) 1:/#; apply loadW128_memread; smt().
  seq 2 : (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 16 /\ newat = at + 8 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0); first by auto => /#.
  if; last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt -> [sz [Hsz IH]] Hc /=.
  rewrite set64_addstate_at 1:/#.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 4!(split; first smt()).
  exists (sz + 8); split; first smt().
  have Hs : size (u64bytes (loadW64 _mem buf{hr})) = 8 by rewrite /u64bytes size_to_list.
  apply (addstate_spec_fullword L (u64bytes (loadW64 _mem buf{hr})) sz _st _at 0 st{hr} _buf buf{hr} at{hr} (_upto - at{hr}) 0 (sz + 8) (buf{hr} + 8) (at{hr} + 8) (_upto - (at{hr} + 8))) => //; rewrite ?Hs; 1,2: smt().
  by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) 1:/#; apply loadW64_memread; smt().
while (Glob.mem = _mem /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 8 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _buf buf st at (_upto - at) 0); last by auto => /#.
auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
rewrite set64_addstate_at 1:/#.
have Hal : at{hr} %% 8 = 0 by smt().
do 3!(split; first smt()).
exists (sz + 8); split; first smt().
have Hs : size (u64bytes (loadW64 _mem buf{hr})) = 8 by rewrite /u64bytes size_to_list.
apply (addstate_spec_fullword L (u64bytes (loadW64 _mem buf{hr})) sz _st _at 0 st{hr} _buf buf{hr} at{hr} (_upto - at{hr}) 0 (sz + 8) (buf{hr} + 8) (at{hr} + 8) (_upto - (at{hr} + 8))) => //; rewrite ?Hs; 1,2: smt().
by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) 1:/#; apply loadW64_memread; smt().
if; last first.
+ auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  have [-> [_ ->]] := addstate_spec_done L (_upto - _at) sz _st _at 0 st{hr} _buf buf{hr} _upto 0 _ _ _ _ IH; 1..4: smt(size_memread).
  by rewrite cats0.
wp; ecall (m_rlen_read_upto8_h buf (W64.to_uint upto8)); wp; skip => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu; split; first smt().
move=> _ [b t] /= [Hs Hb].
rewrite set64_addstate_at 1:/#.
have M := msubread_rlen _mem t at{hr} at{hr} buf{hr} (_upto - at{hr}) _ _ Hs; 1,2: smt().
move: M; rewrite /= u64_shl0 /msubread => [#] Hsr _ _ _ _.
have Hs8 : size (u64bytes t) = 8 by rewrite /u64bytes size_to_list.
have [F1 [_ F3]] := addstate_spec_finish L (u64bytes t) (_upto - _at) sz _st _at 0 st{hr} _buf buf{hr} at{hr} (_upto - at{hr}) 0 (srat 8 at{hr} at{hr} (_upto - at{hr}) 0) (buf{hr} + srincr 8 at{hr} at{hr} (_upto - at{hr})) _ _ _ _ _ _ _ _ _ IH _; 1..9: smt(size_memread).
+ by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) 1:/#.
move: F1 F3; rewrite /= cats0 => -> F3.
by rewrite Hb -F3 /srincr /=; smt().
qed.

phoare add_m_updstate_ph _mem _st _at _buf _upto:
 [ M._add_m_updstate
 : Glob.mem = _mem /\ st = _st /\ at = _at /\ buf = _buf /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = _mem
   /\ res = (addstate_at _st _at (memread _mem _buf (_upto - _at)), _upto, _buf + (_upto - _at))
 ] = 1%r.
proof. by conseq add_m_updstate_ll (add_m_updstate_h _mem _st _at _buf _upto). qed.

lemma dump_m_updstate_ll: islossless M._dump_m_updstate.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
if.
+ seq 2: true => //; first by while true (upto + 32 - newat) => [z|]; auto => /#.
  by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare dump_m_updstate_h _mem _st _at _buf _upto:
 M._dump_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) _at (_upto - _at))
   /\ res = (_buf + (_upto - _at), _upto).
proof.
proc => /=; pose S := stbytes _st.
seq 1 : #pre; first by inline *; auto.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2; rewrite and7_mod8 /#.
seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)).
+ if; last first.
  + auto => /> H0 H1 H2 Hk; split; first smt().
    by exists 0; rewrite sub200_nil nseq0 /= store0 /#.
  wp; ecall (m_rlen_write_upto8_h Glob.mem buf t64 len); wp; skip => /> &hr H0 H1 H2 Hk Hnz.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#.
  pose base := 8 * (_at %/ 8).
  have Hb : base + _at %% 8 = _at by smt().
  rewrite (u64bytes_get64_shr (stbytes _st) base (_at %% 8)) 1:/# Hb -/S.
  split; first smt().
  move=> _; split => Hc.
  + do 3!(split; first smt()).
    exists (min (_upto - _at - (8 - _at %% 8)) (_at %% 8)); split; first smt(). split; first smt().
    rewrite take_cat size_sub 1:/# ifF 1:/#.
    by rewrite (: base + 8 - _at = 8 - _at %% 8) 1:/# take_nseq.
  split; first smt().
  exists 0; rewrite nseq0 cats0 /=.
  by rewrite take_cat size_sub 1:/# ifT 1:/# take_sub200 /#.
seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ _upto < at + 8 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)).
+ sp; if.
  + seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ _upto < at + 32 /\ newat = at + 32 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)).
    + while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 32 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)); last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 -> [z [Hz [Hzl ->]]] Hc /=.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 4!(split; first smt()).
      exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
      rewrite storeW256E -/(u256bytes (get256_direct (stbytes _st) at{hr})) u256bytes_get256 -/S.
      have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
      have := stores_overwrite _mem _buf (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 32) _.
      + by rewrite size_nseq size_sub /#.
      rewrite Hsz => ->.
      by rewrite (: at{hr} + 32 - _at = (at{hr} - _at) + 32) 1:/# (sub_cat S _at (at{hr} - _at) 32) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
    seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ _upto < at + 32 /\ newat = at + 16 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)); first by auto => /#.
    seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ _upto < at + 16 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)).
    + if; last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 -> Hlt -> [z [Hz [Hzl ->]]] Hc /=.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 5!(split; first smt()).
      exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
      rewrite storeW128E -/(u128bytes (get128_direct (stbytes _st) at{hr})) u128bytes_get128 -/S.
      have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
      have := stores_overwrite _mem _buf (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 16) _.
      + by rewrite size_nseq size_sub /#.
      rewrite Hsz => ->.
      by rewrite (: at{hr} + 16 - _at = (at{hr} - _at) + 16) 1:/# (sub_cat S _at (at{hr} - _at) 16) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
    seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ _upto < at + 16 /\ newat = at + 8 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)); first by auto => /#.
    if; last by auto => /#.
    auto => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 -> Hlt -> [z [Hz [Hzl ->]]] Hc /=.
    have Hal : at{hr} %% 8 = 0 by smt().
    do 5!(split; first smt()).
    exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
    rewrite storeW64E -/(u64bytes (get64_direct (stbytes _st) at{hr})) u64bytes_get64 -/S.
    have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
    have := stores_overwrite _mem _buf (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 8) _.
    + by rewrite size_nseq size_sub /#.
    rewrite Hsz => ->.
    by rewrite (: at{hr} + 8 - _at = (at{hr} - _at) + 8) 1:/# (sub_cat S _at (at{hr} - _at) 8) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
  while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ newat = at + 8 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ buf = _buf + (at - _at) /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ Glob.mem = stores _mem _buf (sub S _at (at - _at) ++ u8zeros z)); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 -> Ha0 Ha1 Ha8 -> [z [Hz [Hzl ->]]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 4!(split; first smt()).
  exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
  rewrite storeW64E -/(u64bytes (get64_direct (stbytes _st) at{hr})) u64bytes_get64 -/S.
  have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
  have := stores_overwrite _mem _buf (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 8) _.
  + by rewrite size_nseq size_sub /#.
  rewrite Hsz => ->.
  by rewrite (: at{hr} + 8 - _at = (at{hr} - _at) + 8) 1:/# (sub_cat S _at (at{hr} - _at) 8) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
if; last first.
+ auto => &hr [#] _ -> H0 H1 H2 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl ->]]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  have Ez : z = 0 by smt().
  by rewrite Ea Ez nseq0 cats0.
wp; ecall (m_rlen_write_upto8_h Glob.mem buf t64 (W64.to_uint upto8)); wp; skip => &hr [#] -> -> H0 H1 H2 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl ->]]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu; split; first smt().
move=> _ b m [-> ->].
rewrite u64bytes_get64 -/S take_sub200 1:/#.
have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
have := stores_overwrite _mem _buf (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} (_upto - at{hr})) _.
+ by rewrite size_nseq size_sub /#.
rewrite Hsz => ->; split; last by smt().
by rewrite (: _upto - _at = (at{hr} - _at) + (_upto - at{hr})) 1:/# (sub_cat S _at (at{hr} - _at) (_upto - at{hr})) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
qed.

phoare dump_m_updstate_ph _mem _st _at _buf _upto:
 [ M._dump_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) _at (_upto - _at))
   /\ res = (_buf + (_upto - _at), _upto)
 ] = 1%r.
proof. by conseq dump_m_updstate_ll (dump_m_updstate_h _mem _st _at _buf _upto). qed.

lemma absorb_m_updstate_ll: islossless M._absorb_m_updstate.
proof.
proc; seq 5: (8 <= r8).
+ by wp; ecall (ststatus_data_bnd_h); auto => /#.
+ by wp; call ststatus_data_bnd_ph; auto => /#.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_ll; call add_m_updstate_ll; auto => /#.
  by wp; call add_m_updstate_ll; auto.
+ by hoare; wp; ecall (ststatus_data_bnd_h); auto => /#.
by [].
qed.

hoare absorb_m_updstate_h _mem _r8 _tb _l _buf _len:
 M._absorb_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len
 ==> Glob.mem = _mem /\ absorbing_spec _r8 _tb (_l ++ memread _mem _buf _len) res.
proof.
proc => /=; exlim st => _st.
pose M := memread _mem _buf _len.
seq 5 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len
         /\ r8 = _r8 /\ buf = _buf /\ stk = ust_state _st /\ at = size _l %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_h st.[25]); auto => &hr [#] -> -> -> -> Habs H0 r ->.
  rewrite ststatus_data_specE /=.
  by have := Habs; rewrite /absorbing_spec /status_spec => /> *.
seq 1 : (Glob.mem = _mem /\ st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf <= buf <= _buf + _len /\ at = (size _l + (buf - _buf)) %% _r8
         /\ len = _len - (buf - _buf) + at /\ len < r8
         /\ pabsorb_spec _r8 (_l ++ take (buf - _buf) M) stk).
+ while (Glob.mem = _mem /\ st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len /\ r8 = _r8
         /\ _buf <= buf <= _buf + _len /\ at = (size _l + (buf - _buf)) %% _r8
         /\ len = _len - (buf - _buf) + at
         /\ pabsorb_spec _r8 (_l ++ take (buf - _buf) M) stk).
  + wp; ecall (keccakf1600_h stk); ecall (add_m_updstate_h Glob.mem stk at buf r8).
    auto => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> Hp Hc.
    have [Hr8 _] := Hp.
    pose k := buf{hr} - _buf.
    pose a := (size _l + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ r -> _ -> /=.
    have Es : take (_r8 - a) (drop k M) = memread _mem buf{hr} (_r8 - a).
    + by rewrite /M slice_memread 1..3:/#; congr; smt().
    have Hfill := pabsorb_fill_at _r8 _l M k stk{hr} a _ _ _ Hp; 1..3: smt(size_memread).
    move: Hfill; rewrite Es (: k + (_r8 - a) = buf{hr} + (_r8 - a) - _buf) 1:/# => Hfill.
    have Hblk := absorb_block_arith (size _l) k _r8 a _ _; 1,2: smt().
    do 2!(split; first done); split; first smt().
    split; first by rewrite (: buf{hr} + (_r8 - a) - _buf = k + (_r8 - a)) 1:/# Hblk.
    by split; [smt() | exact Hfill].
  auto => &hr [#] -> -> Habs H0 -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by rewrite take0 cats0; exact Hp.
wp; ecall (add_m_updstate_h Glob.mem stk at buf len); wp; skip => &hr [#] -> -> Habs H0 -> Hb0 Hb1 -> -> Hc Hp /=.
split; first smt().
move=> _ r Er.
change (absorbing_spec _r8 _tb (_l ++ memread _mem _buf _len) (st26_store r.`1 _st r.`2)).
have [Hr8 _] := Hp.
pose k := buf{hr} - _buf.
pose a := (size _l + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Ed : drop k M = memread _mem buf{hr} (_len - k) by rewrite /M (drop_memread_cur _mem _buf _len buf{hr}) 1:/#.
have Hlast := pabsorb_last_at _r8 _l M k stk{hr} a _ _ _ Hp; 1..3: smt(size_memread).
move: Hlast; rewrite Ed => Hlast.
have [Hat2 [Hr2 Htb2]] := st26_store_status r.`1 _st r.`2 _; first by rewrite Er /=; smt().
have [_ [Hr0 [Htb0 Hat0]]] := Habs.
rewrite /absorbing_spec st26_store_lanes Er /=; split.
+ by rewrite (: _len - k + a - a = _len - k) 1:/#.
move: Hat2 Hr2 Htb2; rewrite Er /= => Hat2 Hr2 Htb2.
have Hl := absorb_last_arith (size _l) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat size_memread 1:/#.
rewrite (: size _l + _len = size _l + (k + (_len - k))) 1:/# Hl.
smt().
qed.

phoare absorb_m_updstate_ph _mem _r8 _tb _l _buf _len:
 [ M._absorb_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len
 ==> Glob.mem = _mem /\ absorbing_spec _r8 _tb (_l ++ memread _mem _buf _len) res
 ] = 1%r.
proof. by conseq absorb_m_updstate_ll (absorb_m_updstate_h _mem _r8 _tb _l _buf _len). qed.

lemma squeeze_m_updstate_ll: islossless M._squeeze_m_updstate.
proof.
proc; seq 4: (8 <= r8).
+ by wp; ecall (ststatus_data_bnd_h); auto => /#.
+ by wp; call ststatus_data_bnd_ph; auto => /#.
+ seq 2: (8 <= r8) => //.
  + by wp; if; [wp; call keccakf1600_ll; auto | auto].
  + seq 1: true => //.
    + while (8 <= r8) len => [z|]; last by auto => /#.
      by wp; call keccakf1600_ll; call dump_m_updstate_ll; auto => /#.
    by wp; call dump_m_updstate_ll; auto.
  by hoare; wp; if; [wp; ecall (keccakf1600_h stk); auto | auto].
+ by hoare; wp; ecall (ststatus_data_bnd_h); auto => /#.
by [].
qed.

hoare squeeze_m_updstate_h _mem _r8 _st0 _k _buf _len:
 M._squeeze_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len
 ==> Glob.mem = stores _mem _buf (sqstream _r8 _st0 _k _len)
   /\ squeezing_spec _r8 _st0 (_k + _len) res.
proof.
proc => /=; exlim st => _st.
seq 4 : (Glob.mem = _mem /\ buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ stk = st_i _st0 ((_k - 1) %/ _r8 + 1)).
+ wp; ecall (ststatus_data_h st.[25]); auto => &hr [#] -> -> -> -> Hsq H0 r ->.
  rewrite ststatus_data_specE /=.
  by have := Hsq; rewrite /squeezing_spec => /> *.
seq 2 : (Glob.mem = _mem /\ buf = _buf /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ len = _len + at /\ stk = st_i _st0 (_k %/ _r8 + 1)).
+ wp; if.
  + wp; ecall (keccakf1600_h stk); auto => &hr [#] -> -> -> Hsq H0 -> -> Hat -> Hz.
    have [Hr [Hk _]] := Hsq.
    move=> r ->; do 6!(split; first done); split; first smt().
    split; first done.
    rewrite -(squeeze_entry0 _r8 _k) 1,2:/# /st_i (iterS ((_k - 1) %/ _r8 + 1)) //.
    by apply (squeeze_entry_ge0 _r8 _k) => /#.
  auto => &hr [#] -> -> -> Hsq H0 -> -> Hat -> Hz.
  have [Hr [Hk _]] := Hsq.
  by rewrite (squeeze_entry1 _r8 _k) 1,2:/#.
seq 1 : (Glob.mem = stores _mem _buf (sqstream _r8 _st0 _k (buf - _buf))
         /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len /\ st = _st /\ r8 = _r8
         /\ stk = st_i _st0 ((_k + (buf - _buf)) %/ _r8 + 1) /\ at = (_k + (buf - _buf)) %% _r8
         /\ len = at + (_len - (buf - _buf)) /\ 0 <= buf - _buf < _len /\ len <= r8).
+ while (Glob.mem = stores _mem _buf (sqstream _r8 _st0 _k (buf - _buf))
         /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len /\ st = _st /\ r8 = _r8
         /\ stk = st_i _st0 ((_k + (buf - _buf)) %/ _r8 + 1) /\ at = (_k + (buf - _buf)) %% _r8
         /\ len = at + (_len - (buf - _buf)) /\ 0 <= buf - _buf < _len).
  + wp; ecall (keccakf1600_h stk); ecall (dump_m_updstate_h Glob.mem stk at buf r8).
    auto => &hr [#] -> Hsq H0 -> -> -> -> -> Hw0 Hw1 Hc.
    have [Hr [Hk _]] := Hsq.
    pose w := buf{hr} - _buf; pose p := _k + w; pose a := p %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ r m [-> ->] r0 -> /=.
    have [Hp0 Hp1] := squeeze_pos_arith _r8 p a _ _; 1,2: smt().
    rewrite (: buf{hr} + (_r8 - a) - _buf = w + (_r8 - a)) 1:/#.
    split.
    + rewrite (sqstream_cat _r8 _st0 _k w (_r8 - a)) 1..4:/# stores_cat size_sqstream 1..3:/#.
      by rewrite (: _buf + w = buf{hr}) 1:/# (sqstream_block _r8 _st0 p (_r8 - a)) 1..4:/#.
    split; first exact Hsq. split; first exact H0.
    split.
    + rewrite /st_i -iterS; first smt(divz_ge0).
      by rewrite (: _k + (w + (_r8 - a)) = p + (_r8 - a)) 1:/# Hp1.
    split; first by rewrite (: _k + (w + (_r8 - a)) = p + (_r8 - a)) 1:/# Hp0.
    smt().
  auto => &hr [#] -> -> Hsq H0 -> -> -> -> -> /=.
  have [Hr [Hk _]] := Hsq.
  split; last by smt().
  have -> : sqstream _r8 _st0 _k 0 = [] by rewrite -size_eq0 size_sqstream.
  by rewrite store0 /#.
wp; ecall (dump_m_updstate_h Glob.mem stk at buf len); wp; skip => &hr [#] -> Hsq H0 -> -> -> -> -> Hw0 Hw1 Hle /=.
have [Hr [Hk _]] := Hsq.
pose w := buf{hr} - _buf; pose p := _k + w; pose a := p %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
split; first smt().
move=> _ r m [-> ->] /=.
rewrite (: a + (_len - w) - a = _len - w) 1:/#.
split.
+ have -> : sqstream _r8 _st0 _k _len = sqstream _r8 _st0 _k w ++ sqstream _r8 _st0 (_k + w) (_len - w).
  + by rewrite -(sqstream_cat _r8 _st0 _k w (_len - w)) 1..4:/#; congr; ring.
  rewrite stores_cat size_sqstream 1..3:/#.
  by rewrite (: _buf + w = buf{hr}) 1:/# (sqstream_block _r8 _st0 p (_len - w)) 1..4:/#.
change (squeezing_spec _r8 _st0 (_k + _len) (st26_store (st_i _st0 (p %/ _r8 + 1)) _st (a + (_len - w)))).
have [Fq Fm] := squeeze_fin_arith _r8 p a (_len - w) _ _ _ _; 1..4: smt().
have [Hat2 [Hr2 _]] := st26_store_status (st_i _st0 (p %/ _r8 + 1)) _st (a + (_len - w)) _; first smt().
have [_ [_ [_ [Hr0 _]]]] := Hsq.
rewrite /squeezing_spec st26_store_lanes /ststatus_at_norm Hr2 Hr0 Hat2.
rewrite (: _k + _len - 1 = p + (_len - w) - 1) 1:/# Fq (: _k + _len = p + (_len - w)) 1:/# Fm.
smt().
qed.

phoare squeeze_m_updstate_ph _mem _r8 _st0 _k _buf _len:
 [ M._squeeze_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len
 ==> Glob.mem = stores _mem _buf (sqstream _r8 _st0 _k _len)
   /\ squeezing_spec _r8 _st0 (_k + _len) res
 ] = 1%r.
proof. by conseq squeeze_m_updstate_ll (squeeze_m_updstate_h _mem _r8 _st0 _k _buf _len). qed.


(* ------------------------------------------------------------------------- *)
(* The exported wrappers                                                     *)
(* ------------------------------------------------------------------------- *)

lemma init_updstate_export_ll: islossless M.init_updstate.
proof. by proc; call init_updstate_ll; auto. qed.

hoare init_updstate_export_h _r64 _tb:
 M.init_updstate
 : r64 = _r64 /\ trailb = _tb /\ 0 < _r64 <= 25
 ==> absorbing_spec (8 * _r64) _tb [] res.
proof. by proc; ecall (init_updstate_h _r64 _tb); auto. qed.

lemma finish_updstate_export_ll: islossless M.finish_updstate.
proof. by proc; call finish_updstate_ll; auto. qed.

hoare finish_updstate_export_h _r8 _tb _l:
 M.finish_updstate
 : absorbing_spec _r8 _tb _l st
 ==> squeezing_spec _r8 (ABSORB1600 _tb _r8 _l) 0 res.
proof. by proc; ecall (finish_updstate_h _r8 _tb _l); auto. qed.

lemma absorb_m_updstate_export_ll: islossless M.absorb_m_updstate.
proof. by proc; call absorb_m_updstate_ll; auto. qed.

hoare absorb_m_updstate_export_h _mem _r8 _tb _l _buf _len:
 M.absorb_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len
 ==> Glob.mem = _mem /\ absorbing_spec _r8 _tb (_l ++ memread _mem _buf _len) res.
proof. by proc; ecall (absorb_m_updstate_h _mem _r8 _tb _l _buf _len); auto. qed.

lemma squeeze_m_updstate_export_ll: islossless M.squeeze_m_updstate.
proof. by proc; call squeeze_m_updstate_ll; auto. qed.

hoare squeeze_m_updstate_export_h _mem _r8 _st0 _k _buf _len:
 M.squeeze_m_updstate
 : Glob.mem = _mem /\ buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len
 ==> Glob.mem = stores _mem _buf (sqstream _r8 _st0 _k _len)
   /\ squeezing_spec _r8 _st0 (_k + _len) res.
proof. by proc; ecall (squeeze_m_updstate_h _mem _r8 _st0 _k _buf _len); auto. qed.

(* ========================================================================= *)
(* Array-buffer absorb and squeeze                                           *)
(* ========================================================================= *)

abstract theory KeccakUpdstateRef.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

clone import ReadWriteArray as RW
 with op _ASIZE <- _ASIZE,
      theory A <- A,
      theory WA <- WA
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

(* The extracted array procedures (Keccak1600_Jazz_ASIZE at _ASIZE = 999),
   with Array999/WArray999 replaced by A/WA and the size-independent callees
   taken from Keccak1600_Jazz.M (checked by Keccak1600_updstate_ref_checkXtr). *)
module MM = {
  proc _add_updstate (st:W64.t Array25.t, at:int, buf:W8.t A.t,
                      off:int, upto:int) : W64.t Array25.t * int * int = {
    var hAS_AVX2:bool;
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t256:W256.t;
    var t128:W128.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, ((1 + 2) + 4));
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (off2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, len);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    if (hAS_AVX2) {
      newat <- (newat + 32);
      while ((newat <= upto)) {
        t256 <- (get256_direct (WA.init8 (fun i => buf.[i])) off);
        off <- (off + 32);
        t256 <-
        (t256 `^` (get256_direct (WArray200.init64 (fun i => st.[i])) at));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) 
        at t256)));
        at <- newat;
        newat <- (newat + 32);
      }
      newat <- (newat - 16);
      if ((newat <= upto)) {
        t128 <- (get128_direct (WA.init8 (fun i => buf.[i])) off);
        off <- (off + 16);
        t128 <-
        (t128 `^` (get128_direct (WArray200.init64 (fun i => st.[i])) at));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set128_direct (WArray200.init64 (fun i => st.[i])) 
        at t128)));
        at <- newat;
      } else {
        
      }
      newat <- at;
      newat <- (newat + 8);
      if ((newat <= upto)) {
        t64 <- (get64_direct (WA.init8 (fun i => buf.[i])) off);
        off <- (off + 8);
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) 
        at ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64)))
        );
        at <- newat;
      } else {
        
      }
    } else {
      newat <- (newat + 8);
      while ((newat <= upto)) {
        t64 <- (get64_direct (WA.init8 (fun i => buf.[i])) off);
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) 
        at ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64)))
        );
        at <- newat;
        off <- (off + 8);
        newat <- (newat + 8);
      }
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
    } else {
      
    }
    at <- upto;
    return (st, at, off);
  }

  proc _absorb_updstate (st:W64.t Array26.t, buf:W8.t A.t, len:int) : 
  W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ M._ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (stk, at, off) <@ _add_updstate (stk, at, buf, off, r8);
      (* Erased call to spill *)
      stk <@ M._keccakf1600 (stk);
      (* Erased call to unspill *)
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
    (stk, at,  _1) <@ _add_updstate (stk, at, buf, off, len);
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }

  proc _dump_updstate (buf:W8.t A.t, off:int, st:W64.t Array25.t,
                       at:int, upto:int) : W8.t A.t * int * int = {
    var hAS_AVX2:bool;
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t256:W256.t;
    var t128:W128.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, ((1 + 2) + 4));
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf, off2) <@ RW.MM.__a_rlen_write_upto8 (buf, off, t64, len);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    if (hAS_AVX2) {
      newat <- (newat + 32);
      while ((newat <= upto)) {
        t256 <- (get256_direct (WArray200.init64 (fun i => st.[i])) at);
        buf <-
        (A.init
        (WA.get8
        (WA.set256_direct (WA.init8 (fun i => buf.[i])) 
        off t256)));
        off <- (off + 32);
        at <- newat;
        newat <- (newat + 32);
      }
      newat <- (newat - 16);
      if ((newat <= upto)) {
        t128 <- (get128_direct (WArray200.init64 (fun i => st.[i])) at);
        buf <-
        (A.init
        (WA.get8
        (WA.set128_direct (WA.init8 (fun i => buf.[i])) 
        off t128)));
        at <- newat;
        off <- (off + 16);
      } else {
        
      }
      newat <- at;
      newat <- (newat + 8);
      if ((newat <= upto)) {
        t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i => buf.[i])) off t64)
        ));
        off <- (off + 8);
        at <- newat;
      } else {
        
      }
    } else {
      newat <- (newat + 8);
      while ((newat <= upto)) {
        t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i => buf.[i])) off t64)
        ));
        at <- newat;
        off <- (off + 8);
        newat <- (newat + 8);
      }
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      (buf, off) <@ RW.MM.__a_rlen_write_upto8 (buf, off, t64,
      (W64.to_uint upto8));
    } else {
      
    }
    at <- upto;
    return (buf, off, at);
  }

  proc _squeeze_updstate (st:W64.t Array26.t, buf:W8.t A.t, len:int) : 
  W64.t Array26.t * W8.t A.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ M._ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    if ((at = 0)) {
      (* Erased call to spill *)
      stk <@ M._keccakf1600 (stk);
      (* Erased call to unspill *)
      at <- 0;
    } else {
      
    }
    off <- 0;
    len <- (len + at);
    while ((r8 < len)) {
      (buf, off, at) <@ _dump_updstate (buf, off, stk, at, r8);
      (* Erased call to spill *)
      stk <@ M._keccakf1600 (stk);
      (* Erased call to unspill *)
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (buf,  _1, at) <@ _dump_updstate (buf, off, stk, at, len);
    (* Erased call to unspill *)
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return (st, buf);
  }

  proc absorb_updstate (st:W64.t Array26.t, buf:W8.t A.t, len:int) : 
  W64.t Array26.t = {
    
    st <- st;
    buf <- buf;
    len <- len;
    st <@ _absorb_updstate (st, buf, len);
    return st;
  }

  proc squeeze_updstate (st:W64.t Array26.t, buf:W8.t A.t, len:int) : 
  W64.t Array26.t * W8.t A.t = {
    
    st <- st;
    buf <- buf;
    len <- len;
    (st, buf) <@ _squeeze_updstate (st, buf, len);
    return (st, buf);
  }
}.

lemma add_updstate_ll: islossless MM._add_updstate.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
if.
+ seq 2: true => //; first by while true (upto + 32 - newat) => [z|]; auto => /#.
  by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare add_updstate_h _st _at _buf _off _upto:
 MM._add_updstate
 : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res = (addstate_at _st _at (sub _buf _off (_upto - _at)), _upto, _off + (_upto - _at)).
proof.
proc => /=; pose L := sub _buf _off (_upto - _at).
seq 1 : #pre; first by inline *; auto.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 H3 H4; rewrite and7_mod8 /#.
seq 1 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto)
         /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0).
+ if; last first.
  + auto => /> H0 H1 H2 H3 H4 Hk; split; first smt().
    by exists _at; split => //; apply addstate_spec_init => //; smt(A.size_sub).
  wp; ecall (a_rlen_read_upto8_h buf off len); wp; skip => /> &hr H0 H1 H2 H3 H4 Hk Hnz.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#; split; first smt().
  move=> _ [off2 t] /= Hs Hoff2.
  rewrite W64.shl_shlw 1:/# set64_addstate_at 1:/#.
  pose base := 8 * (_at %/ 8).
  have Hb : _at - base = _at %% 8 by smt().
  have M := asubread_rlen _buf t base _at _off 0 (_upto - _at) _ _ _; 1,2: smt().
  + by move=> _; rewrite addz0.
  rewrite Hb in M.
  have S0 : addstate_spec _st _at L 0 base _off (_off + 0) _st _at (_upto - _at) 0.
  + by apply addstate_spec_init => //; smt(A.size_sub).
  have S1 := addstate_asubread_u64 _buf (t `<<<` 8 * (_at %% 8)) base _st _at _off (_upto - _at) 0 _st _at 0 (_upto - _at) 0 (base + 8) _ _ _ _ _ _ _ _ _ _ _ S0 M; 1..7: smt().
  split => Hc.
  + have Emin : min (_upto - _at) (base + 8 - _at) = base + 8 - _at by smt().
    move: S1; rewrite Emin (: _at + (base + 8 - _at) = base + 8) 1:/# (: _upto - _at - (base + 8 - _at) = _upto - (base + 8)) 1:/# => S1.
    do split; 1..3: smt().
    exists (base + 8); split; first smt().
    by rewrite (: _off + 8 - _at %% 8 = _off + (0 + (base + 8 - _at))) 1:/#.
  have Emin : min (_upto - _at) (base + 8 - _at) = _upto - _at by smt().
  move: S1; rewrite Emin (: _at + (_upto - _at) = _upto) 1:/# (: _upto - _at - (_upto - _at) = 0) 1:/# => S1.
  exists (base + 8); split; first smt().
  by rewrite Hoff2 (: _off + min 8 (max 0 (_upto - _at)) = _off + (0 + (_upto - _at))) 1:/#.
seq 2 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 8 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0).
+ sp; if.
  + seq 2 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 32 /\ newat = at + 32 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0).
    + while (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ newat = at + 32 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0); last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 H3 H4 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
      rewrite xorwC set256_addstate_at 1:/#.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 5!(split; first smt()).
      exists (sz + 32); split; first smt().
      have Hs : size (u256bytes (get256_direct (WA.init8 ("_.[_]" _buf)) off{hr})) = 32 by rewrite /u256bytes size_to_list.
      apply (addstate_spec_fullword L (u256bytes (get256_direct (WA.init8 ("_.[_]" _buf)) off{hr})) sz _st _at 0 st{hr} _off off{hr} at{hr} (_upto - at{hr}) 0 (sz + 32) (off{hr} + 32) (at{hr} + 32) (_upto - (at{hr} + 32))) => //; rewrite ?Hs; 1,2: smt().
      have [E [Ec1 Ec2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ H3 _ H4 IH; first smt().
      by rewrite E; apply getW256_bytearray; smt().
    seq 1 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 32 /\ newat = at + 16 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0); first by auto => /#.
    seq 1 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 16 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0).
    + if; last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt -> [sz [Hsz IH]] Hc /=.
      rewrite xorwC set128_addstate_at 1:/#.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 6!(split; first smt()).
      exists (sz + 16); split; first smt().
      have Hs : size (u128bytes (get128_direct (WA.init8 ("_.[_]" _buf)) off{hr})) = 16 by rewrite /u128bytes size_to_list.
      apply (addstate_spec_fullword L (u128bytes (get128_direct (WA.init8 ("_.[_]" _buf)) off{hr})) sz _st _at 0 st{hr} _off off{hr} at{hr} (_upto - at{hr}) 0 (sz + 16) (off{hr} + 16) (at{hr} + 16) (_upto - (at{hr} + 16))) => //; rewrite ?Hs; 1,2: smt().
      have [E [Ec1 Ec2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ H3 _ H4 IH; first smt().
      by rewrite E; apply getW128_bytearray; smt().
    seq 2 : (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ _upto < at + 16 /\ newat = at + 8 /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0); first by auto => /#.
    if; last by auto => /#.
    auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt -> [sz [Hsz IH]] Hc /=.
    rewrite set64_addstate_at 1:/#.
    have Hal : at{hr} %% 8 = 0 by smt().
    do 6!(split; first smt()).
    exists (sz + 8); split; first smt().
    have Hs : size (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) off{hr})) = 8 by rewrite /u64bytes size_to_list.
    apply (addstate_spec_fullword L (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) off{hr})) sz _st _at 0 st{hr} _off off{hr} at{hr} (_upto - at{hr}) 0 (sz + 8) (off{hr} + 8) (at{hr} + 8) (_upto - (at{hr} + 8))) => //; rewrite ?Hs; 1,2: smt().
    have [E [Ec1 Ec2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ H3 _ H4 IH; first smt().
    by rewrite E; apply getW64_bytearray; smt().
  while (upto = _upto /\ buf = _buf /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ newat = at + 8 /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ exists sz, _at <= sz /\ addstate_spec _st _at L 0 sz _off off st at (_upto - at) 0); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 H3 H4 -> Ha0 Ha1 Ha8 [sz [Hsz IH]] Hc /=.
  rewrite set64_addstate_at 1:/#.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 5!(split; first smt()).
  exists (sz + 8); split; first smt().
  have Hs : size (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) off{hr})) = 8 by rewrite /u64bytes size_to_list.
  apply (addstate_spec_fullword L (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) off{hr})) sz _st _at 0 st{hr} _off off{hr} at{hr} (_upto - at{hr}) 0 (sz + 8) (off{hr} + 8) (at{hr} + 8) (_upto - (at{hr} + 8))) => //; rewrite ?Hs; 1,2: smt().
  have [E [Ec1 Ec2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ H3 _ H4 IH; first smt().
  by rewrite E; apply getW64_bytearray; smt().
if; last first.
+ auto => &hr [#] -> _ H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  move: IH; rewrite Ea /= => IH.
  have [-> [_ ->]] := addstate_spec_done L (_upto - _at) sz _st _at 0 st{hr} _off off{hr} _upto 0 _ _ _ _ IH; 1..4: smt(A.size_sub).
  by rewrite cats0.
wp; ecall (a_rlen_read_upto8_h buf off (W64.to_uint upto8)); wp; skip => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 Hlt [sz [Hsz IH]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
have [E [Ec1 Ec2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ H3 _ H4 IH; first smt().
rewrite Eu; split; first smt().
move=> _ [o t] /= [Hs Ho].
rewrite set64_addstate_at 1:/#.
have Hsr : srspec (u64bytes t) at{hr} at{hr} (sub _buf off{hr} (_upto - at{hr})) (_upto - at{hr}) 0.
+ have := srspec_u64 t at{hr} at{hr} (sub _buf off{hr} (_upto - at{hr})) (_upto - at{hr}) _ _; 1: smt().
  + by apply (srspec_rlen_u8prefAt _ _ (_upto - at{hr})); [rewrite A.size_sub /# | exact Hs].
  by rewrite /= u64_shl0.
have Hs8 : size (u64bytes t) = 8 by rewrite /u64bytes size_to_list.
have [F1 [_ F3]] := addstate_spec_finish L (u64bytes t) (_upto - _at) sz _st _at 0 st{hr} _off off{hr} at{hr} (_upto - at{hr}) 0 (srat 8 at{hr} at{hr} (_upto - at{hr}) 0) (off{hr} + srincr 8 at{hr} at{hr} (_upto - at{hr})) _ _ _ _ _ _ _ _ _ IH _; 1..9: smt(A.size_sub).
+ by rewrite E.
move: F1 F3; rewrite /= cats0 => -> F3.
by rewrite Ho -F3 /srincr /=; smt().
qed.

phoare add_updstate_ph _st _at _buf _off _upto:
 [ MM._add_updstate
 : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res = (addstate_at _st _at (sub _buf _off (_upto - _at)), _upto, _off + (_upto - _at))
 ] = 1%r.
proof. by conseq add_updstate_ll (add_updstate_h _st _at _buf _off _upto). qed.

lemma dump_updstate_ll: islossless MM._dump_updstate.
proof.
proc; seq 5: true => //; first by islossless.
seq 1: true => //; last by islossless.
if.
+ seq 2: true => //; first by while true (upto + 32 - newat) => [z|]; auto => /#.
  by islossless.
by while true (upto + 8 - newat) => [z|]; auto => /#.
qed.

hoare dump_updstate_h _buf _off _st _at _upto:
 MM._dump_updstate
 : buf = _buf /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res = (A.fill (fun i => (sub (stbytes _st) _at (_upto - _at)).[i - _off]) _off (_upto - _at) _buf,
            _off + (_upto - _at), _upto).
proof.
proc => /=; pose S := stbytes _st.
seq 1 : #pre; first by inline *; auto.
seq 2 : (#pre /\ W64.to_uint at8 = _at %% 8).
+ by auto => /> H0 H1 H2 H3 H4; rewrite and7_mod8 /#.
seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
         /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at)
         /\ exists z, 0 <= z <= 7 /\ z <= _upto - at
            /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)).
+ if; last first.
  + auto => /> H0 H1 H2 H3 H4 Hk; split; first smt().
    by exists 0; rewrite sub200_nil nseq0 /= afill_nil /#.
  wp; ecall (a_rlen_write_upto8_h buf off t64 len); wp; skip => /> &hr H0 H1 H2 H3 H4 Hk Hnz.
  have Ea8 : at8{hr} = W64.of_int (_at %% 8) by rewrite -Hk W64.to_uintK.
  have Hk0 : _at %% 8 <> 0 by move: Hnz; rewrite Ea8; apply contra => ->.
  rewrite Hk shr3_shl3 Ea8 trunc_shl3_and63 1:/#.
  pose base := 8 * (_at %/ 8).
  have Hb : base + _at %% 8 = _at by smt().
  split; first smt().
  move=> _; rewrite afill_rlen 1:/# (u64bytes_get64_shr (stbytes _st) base (_at %% 8)) 1:/# Hb -/S.
  move=> [b o] /= -> Ho; split => Hc.
  + do 3!(split; first smt()).
    exists (min (_upto - _at - (8 - _at %% 8)) (_at %% 8)); split; first smt(). split; first smt().
    rewrite take_cat size_sub 1:/# ifF 1:/#.
    by rewrite (: base + 8 - _at = 8 - _at %% 8) 1:/# take_nseq.
  split; first smt().
  exists 0; rewrite nseq0 cats0 /=.
  by rewrite take_cat size_sub 1:/# ifT 1:/# take_sub200 /#.
seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 8 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)).
+ sp; if.
  + seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 32 /\ newat = at + 32 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)).
    + while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ newat = at + 32 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)); last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> -> [z [Hz [Hzl ->]]] Hc /=.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 6!(split; first smt()).
      exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
      rewrite a_set256_afill u256bytes_get256 -/S.
      have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
      have := afill_overwrite _buf _off (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 32) _.
      + by rewrite size_nseq size_sub /#.
      rewrite Hsz => ->.
      by rewrite (: at{hr} + 32 - _at = (at{hr} - _at) + 32) 1:/# (sub_cat S _at (at{hr} - _at) 32) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
    seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 32 /\ newat = at + 16 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)); first by auto => /#.
    seq 1 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 16 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)).
    + if; last by auto => /#.
      auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt -> [z [Hz [Hzl ->]]] Hc /=.
      have Hal : at{hr} %% 8 = 0 by smt().
      do 7!(split; first smt()).
      exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
      rewrite a_set128_afill u128bytes_get128 -/S.
      have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
      have := afill_overwrite _buf _off (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 16) _.
      + by rewrite size_nseq size_sub /#.
      rewrite Hsz => ->.
      by rewrite (: at{hr} + 16 - _at = (at{hr} - _at) + 16) 1:/# (sub_cat S _at (at{hr} - _at) 16) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
    seq 2 : (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ _upto < at + 16 /\ newat = at + 8 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)); first by auto => /#.
    if; last by auto => /#.
    auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt -> [z [Hz [Hzl ->]]] Hc /=.
    have Hal : at{hr} %% 8 = 0 by smt().
    do 7!(split; first smt()).
    exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
    rewrite a_set64_afill u64bytes_get64 -/S.
    have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
    have := afill_overwrite _buf _off (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 8) _.
    + by rewrite size_nseq size_sub /#.
    rewrite Hsz => ->.
    by rewrite (: at{hr} + 8 - _at = (at{hr} - _at) + 8) 1:/# (sub_cat S _at (at{hr} - _at) 8) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
  while (st = _st /\ upto = _upto /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE /\ _at <= at <= _upto /\ (at %% 8 = 0 \/ at = _upto) /\ off = _off + (at - _at) /\ newat = at + 8 /\ exists z, 0 <= z <= 7 /\ z <= _upto - at /\ buf = afill _buf _off (sub S _at (at - _at) ++ u8zeros z)); last by auto => /#.
  auto => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> -> [z [Hz [Hzl ->]]] Hc /=.
  have Hal : at{hr} %% 8 = 0 by smt().
  do 6!(split; first smt()).
  exists 0; rewrite nseq0 cats0; do 2!(split; first smt()).
  rewrite a_set64_afill u64bytes_get64 -/S.
  have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
  have := afill_overwrite _buf _off (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} 8) _.
  + by rewrite size_nseq size_sub /#.
  rewrite Hsz => ->.
  by rewrite (: at{hr} + 8 - _at = (at{hr} - _at) + 8) 1:/# (sub_cat S _at (at{hr} - _at) 8) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
if; last first.
+ auto => &hr [#] _ -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl ->]]] Hc /=.
  have Ea : at{hr} = _upto by smt().
  have Ez : z = 0 by smt().
  by rewrite Ea Ez nseq0 cats0 /afill size_sub /#.
wp; ecall (a_rlen_write_upto8_h buf off t64 (W64.to_uint upto8)); wp; skip => &hr [#] -> -> H0 H1 H2 H3 H4 Ha0 Ha1 Ha8 -> Hlt [z [Hz [Hzl ->]]] Hc /=.
have Hal : at{hr} %% 8 = 0 by smt().
have Eu : W64.to_uint (W64.of_int _upto `&` W64.of_int 7) = _upto - at{hr} by rewrite and7_mod8; smt().
rewrite Eu; split; first smt().
move=> _ [b o] /= [-> ->].
rewrite afill_rlen 1:/# u64bytes_get64 -/S take_sub200 1:/#.
have Hsz : size (sub S _at (at{hr} - _at)) = at{hr} - _at by rewrite size_sub /#.
have := afill_overwrite _buf _off (sub S _at (at{hr} - _at)) (u8zeros z) (sub S at{hr} (_upto - at{hr})) _.
+ by rewrite size_nseq size_sub /#.
rewrite Hsz => ->.
have Ecat : sub S _at (at{hr} - _at) ++ sub S at{hr} (_upto - at{hr}) = sub S _at (_upto - _at).
+ by rewrite (: _upto - _at = (at{hr} - _at) + (_upto - at{hr})) 1:/# (sub_cat S _at (at{hr} - _at) (_upto - at{hr})) 1,2:/# (: _at + (at{hr} - _at) = at{hr}) 1:/#.
rewrite Ecat /afill size_sub 1:/#; smt().
qed.

phoare dump_updstate_ph _buf _off _st _at _upto:
 [ MM._dump_updstate
 : buf = _buf /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
   /\ 0 <= _at <= _upto <= 200 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res = (A.fill (fun i => (sub (stbytes _st) _at (_upto - _at)).[i - _off]) _off (_upto - _at) _buf,
            _off + (_upto - _at), _upto)
 ] = 1%r.
proof. by conseq dump_updstate_ll (dump_updstate_h _buf _off _st _at _upto). qed.

lemma absorb_updstate_ll: islossless MM._absorb_updstate.
proof.
proc; seq 6: (8 <= r8).
+ by wp; ecall (ststatus_data_bnd_h); auto => /#.
+ by wp; call ststatus_data_bnd_ph; auto => /#.
+ seq 1: true => //.
  + while (8 <= r8) len => [z|]; last by auto => /#.
    by wp; call keccakf1600_ll; call add_updstate_ll; auto => /#.
  by wp; call add_updstate_ll; auto.
+ by hoare; wp; ecall (ststatus_data_bnd_h); auto => /#.
by [].
qed.

hoare absorb_updstate_h _r8 _tb _l _buf _len:
 MM._absorb_updstate
 : buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec _r8 _tb (_l ++ sub _buf 0 _len) res.
proof.
proc => /=; exlim st => _st.
pose M := sub _buf 0 _len.
seq 6 : (st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len <= _ASIZE
         /\ r8 = _r8 /\ buf = _buf /\ off = 0 /\ stk = ust_state _st /\ at = size _l %% _r8 /\ len = _len + at).
+ wp; ecall (ststatus_data_h st.[25]); auto => &hr [#] -> -> -> Habs H0 H1 r ->.
  rewrite ststatus_data_specE /=.
  by have := Habs; rewrite /absorbing_spec /status_spec => /> *.
seq 1 : (st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8 /\ buf = _buf
         /\ 0 <= off <= _len /\ at = (size _l + off) %% _r8
         /\ len = _len - off + at /\ len < r8
         /\ pabsorb_spec _r8 (_l ++ take off M) stk).
+ while (st = _st /\ absorbing_spec _r8 _tb _l _st /\ 0 <= _len <= _ASIZE /\ r8 = _r8 /\ buf = _buf
         /\ 0 <= off <= _len /\ at = (size _l + off) %% _r8
         /\ len = _len - off + at
         /\ pabsorb_spec _r8 (_l ++ take off M) stk).
  + wp; ecall (keccakf1600_h stk); ecall (add_updstate_h stk at buf off r8).
    auto => &hr [#] -> Habs H0 H1 -> -> Hb0 Hb1 -> -> Hp Hc.
    have [Hr8 _] := Hp.
    pose k := off{hr}.
    pose a := (size _l + k) %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ r -> _ -> /=.
    have Es : take (_r8 - a) (drop k M) = sub _buf k (_r8 - a).
    + by rewrite /M drop_sub take_sub; congr; smt().
    have Hfill := pabsorb_fill_at _r8 _l M k stk{hr} a _ _ _ Hp; 1..3: smt(A.size_sub).
    move: Hfill; rewrite Es => Hfill.
    have Hblk := absorb_block_arith (size _l) k _r8 a _ _; 1,2: smt().
    do 2!(split; first done); split; first smt().
    split; first by rewrite Hblk.
    by split; [smt() | exact Hfill].
  auto => &hr [#] -> Habs H0 H1 -> -> -> -> -> -> /=.
  have [Hp _] := Habs.
  split; last by smt().
  do 3!(split; first smt()).
  by rewrite take0 cats0; exact Hp.
wp; ecall (add_updstate_h stk at buf off len); wp; skip => &hr [#] -> Habs H0 H1 -> -> Hb0 Hb1 -> -> Hc Hp /=.
split; first smt().
move=> _ r Er.
change (absorbing_spec _r8 _tb (_l ++ sub _buf 0 _len) (st26_store r.`1 _st r.`2)).
have [Hr8 _] := Hp.
pose k := off{hr}.
pose a := (size _l + k) %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
have Ed : drop k M = sub _buf k (_len - k) by rewrite /M drop_sub; congr; smt().
have Hlast := pabsorb_last_at _r8 _l M k stk{hr} a _ _ _ Hp; 1..3: smt(A.size_sub).
move: Hlast; rewrite Ed => Hlast.
have [Hat2 [Hr2 Htb2]] := st26_store_status r.`1 _st r.`2 _; first by rewrite Er /=; smt().
have [_ [Hr0 [Htb0 Hat0]]] := Habs.
rewrite /absorbing_spec st26_store_lanes Er /=; split.
+ by rewrite (: _len - k + a - a = _len - k) 1:/#.
move: Hat2 Hr2 Htb2; rewrite Er /= => Hat2 Hr2 Htb2.
have Hl := absorb_last_arith (size _l) k _r8 a (_len - k) _ _ _ _; 1..4: smt().
rewrite /status_spec /ststatus_at_norm Hr2 Hr0 Htb2 Htb0 Hat2 /= size_cat A.size_sub 1:/#.
rewrite (: size _l + _len = size _l + (k + (_len - k))) 1:/# Hl.
smt().
qed.

phoare absorb_updstate_ph _r8 _tb _l _buf _len:
 [ MM._absorb_updstate
 : buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec _r8 _tb (_l ++ sub _buf 0 _len) res
 ] = 1%r.
proof. by conseq absorb_updstate_ll (absorb_updstate_h _r8 _tb _l _buf _len). qed.

lemma squeeze_updstate_ll: islossless MM._squeeze_updstate.
proof.
proc; seq 4: (8 <= r8).
+ by wp; ecall (ststatus_data_bnd_h); auto => /#.
+ by wp; call ststatus_data_bnd_ph; auto => /#.
+ seq 3: (8 <= r8) => //.
  + by wp; if; [wp; call keccakf1600_ll; auto | auto].
  + seq 1: true => //.
    + while (8 <= r8) len => [z|]; last by auto => /#.
      by wp; call keccakf1600_ll; call dump_updstate_ll; auto => /#.
    by wp; call dump_updstate_ll; auto.
  by hoare; wp; if; [wp; ecall (keccakf1600_h stk); auto | auto].
+ by hoare; wp; ecall (ststatus_data_bnd_h); auto => /#.
by [].
qed.

hoare squeeze_updstate_h _r8 _st0 _k _buf _len:
 MM._squeeze_updstate
 : buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 _st0 _k _len).[i]) 0 _len _buf
   /\ squeezing_spec _r8 _st0 (_k + _len) res.`1.
proof.
proc => /=; exlim st => _st.
seq 4 : (buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len <= _ASIZE
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ stk = st_i _st0 ((_k - 1) %/ _r8 + 1)).
+ wp; ecall (ststatus_data_h st.[25]); auto => &hr [#] -> -> -> Hsq H0 H1 r ->.
  rewrite ststatus_data_specE /=.
  by have := Hsq; rewrite /squeezing_spec => /> *.
seq 3 : (buf = _buf /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len <= _ASIZE
         /\ st = _st /\ r8 = _r8 /\ at = _k %% _r8 /\ off = 0 /\ len = _len + at /\ stk = st_i _st0 (_k %/ _r8 + 1)).
+ wp; if.
  + wp; ecall (keccakf1600_h stk); auto => &hr [#] -> -> Hsq H0 H1 -> -> Hat -> Hz.
    have [Hr [Hk _]] := Hsq.
    move=> r ->; do !(split; first smt()).
    rewrite -(squeeze_entry0 _r8 _k) 1,2:/# /st_i (iterS ((_k - 1) %/ _r8 + 1)) //.
    by apply (squeeze_entry_ge0 _r8 _k) => /#.
  auto => &hr [#] -> -> Hsq H0 H1 -> -> Hat -> Hz.
  have [Hr [Hk _]] := Hsq.
  by rewrite (squeeze_entry1 _r8 _k) 1,2:/#.
seq 1 : (buf = afill _buf 0 (sqstream _r8 _st0 _k off)
         /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len <= _ASIZE /\ st = _st /\ r8 = _r8
         /\ stk = st_i _st0 ((_k + off) %/ _r8 + 1) /\ at = (_k + off) %% _r8
         /\ len = at + (_len - off) /\ 0 <= off < _len /\ len <= r8).
+ while (buf = afill _buf 0 (sqstream _r8 _st0 _k off)
         /\ squeezing_spec _r8 _st0 _k _st /\ 0 < _len <= _ASIZE /\ st = _st /\ r8 = _r8
         /\ stk = st_i _st0 ((_k + off) %/ _r8 + 1) /\ at = (_k + off) %% _r8
         /\ len = at + (_len - off) /\ 0 <= off < _len).
  + wp; ecall (keccakf1600_h stk); ecall (dump_updstate_h buf off stk at r8).
    auto => &hr [#] -> Hsq H0 H1 -> -> -> -> -> Hw0 Hw1 Hc.
    have [Hr [Hk _]] := Hsq.
    pose w := off{hr}; pose p := _k + w; pose a := p %% _r8.
    have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
    split; first smt().
    move=> _ r -> r0 -> /=.
    have [Hp0 Hp1] := squeeze_pos_arith _r8 p a _ _; 1,2: smt().
    split.
    + rewrite -(sqstream_block _r8 _st0 p (_r8 - a)) 1..4:/# (sqstream_cat _r8 _st0 _k w (_r8 - a)) 1..4:/#.
      have E := afill_overwrite _buf 0 (sqstream _r8 _st0 _k w) [] (sqstream _r8 _st0 p (_r8 - a)) _; first by rewrite size_ge0.
      move: E; rewrite cats0 size_sqstream 1..3:/# /= => <-.
      by rewrite /afill size_sqstream 1..3:/# (size_sqstream _r8 _st0 p (_r8 - a)) 1..3:/#.
    split; first exact Hsq. split; first smt().
    split.
    + rewrite /st_i -iterS; first smt(divz_ge0).
      by rewrite (: _k + (w + (_r8 - a)) = p + (_r8 - a)) 1:/# Hp1.
    split; first by rewrite (: _k + (w + (_r8 - a)) = p + (_r8 - a)) 1:/# Hp0.
    smt().
  auto => &hr [#] -> Hsq H0 H1 -> -> -> -> -> -> /=.
  have [Hr [Hk _]] := Hsq.
  split; last by smt().
  have -> : sqstream _r8 _st0 _k 0 = [] by rewrite -size_eq0 size_sqstream.
  by rewrite afill_nil /#.
wp; ecall (dump_updstate_h buf off stk at len); wp; skip => &hr [#] -> Hsq H0 H1 -> -> -> -> -> Hw0 Hw1 Hle /=.
have [Hr [Hk _]] := Hsq.
pose w := off{hr}; pose p := _k + w; pose a := p %% _r8.
have Ha : 0 <= a < _r8 by smt(modz_ge0 ltz_pmod).
split; first smt().
move=> _ r -> /=.
rewrite (: a + (_len - w) - a = _len - w) 1:/#.
split.
+ have Ecat : sqstream _r8 _st0 _k _len = sqstream _r8 _st0 _k w ++ sqstream _r8 _st0 p (_len - w).
  + by rewrite -(sqstream_cat _r8 _st0 _k w (_len - w)) 1..4:/#; congr; ring.
  have E := afill_overwrite _buf 0 (sqstream _r8 _st0 _k w) [] (sqstream _r8 _st0 p (_len - w)) _; first by rewrite size_ge0.
  move: E; rewrite cats0 (size_sqstream _r8 _st0 _k w) 1..3:/# /= => E.
  rewrite -(sqstream_block _r8 _st0 p (_len - w)) 1..4:/#.
  have F : A.fill (fun (i : int) => (sqstream _r8 _st0 p (_len - w)).[i - w]) w (_len - w) (afill _buf 0 (sqstream _r8 _st0 _k w)) = afill (afill _buf 0 (sqstream _r8 _st0 _k w)) w (sqstream _r8 _st0 p (_len - w)).
  + by rewrite {2}/afill (size_sqstream _r8 _st0 p (_len - w)) 1..3:/#.
  rewrite F E -Ecat /afill (size_sqstream _r8 _st0 _k _len) 1..3:/#.
  by congr; apply fun_ext => i /=.
change (squeezing_spec _r8 _st0 (_k + _len) (st26_store (st_i _st0 (p %/ _r8 + 1)) _st (a + (_len - w)))).
have [Fq Fm] := squeeze_fin_arith _r8 p a (_len - w) _ _ _ _; 1..4: smt().
have [Hat2 [Hr2 _]] := st26_store_status (st_i _st0 (p %/ _r8 + 1)) _st (a + (_len - w)) _; first smt().
have [_ [_ [_ [Hr0 _]]]] := Hsq.
rewrite /squeezing_spec st26_store_lanes /ststatus_at_norm Hr2 Hr0 Hat2.
rewrite (: _k + _len - 1 = p + (_len - w) - 1) 1:/# Fq (: _k + _len = p + (_len - w)) 1:/# Fm.
smt().
qed.

phoare squeeze_updstate_ph _r8 _st0 _k _buf _len:
 [ MM._squeeze_updstate
 : buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 _st0 _k _len).[i]) 0 _len _buf
   /\ squeezing_spec _r8 _st0 (_k + _len) res.`1
 ] = 1%r.
proof. by conseq squeeze_updstate_ll (squeeze_updstate_h _r8 _st0 _k _buf _len). qed.

(* the exported wrappers *)
lemma absorb_updstate_export_ll: islossless MM.absorb_updstate.
proof. by proc; call absorb_updstate_ll; auto. qed.

hoare absorb_updstate_export_h _r8 _tb _l _buf _len:
 MM.absorb_updstate
 : buf = _buf /\ len = _len /\ absorbing_spec _r8 _tb _l st /\ 0 <= _len <= _ASIZE
 ==> absorbing_spec _r8 _tb (_l ++ sub _buf 0 _len) res.
proof. by proc; ecall (absorb_updstate_h _r8 _tb _l _buf _len); auto. qed.

lemma squeeze_updstate_export_ll: islossless MM.squeeze_updstate.
proof. by proc; call squeeze_updstate_ll; auto. qed.

hoare squeeze_updstate_export_h _r8 _st0 _k _buf _len:
 MM.squeeze_updstate
 : buf = _buf /\ len = _len /\ squeezing_spec _r8 _st0 _k st /\ 0 < _len <= _ASIZE
 ==> res.`2 = A.fill (fun i => (sqstream _r8 _st0 _k _len).[i]) 0 _len _buf
   /\ squeezing_spec _r8 _st0 (_k + _len) res.`1.
proof. by proc; ecall (squeeze_updstate_h _r8 _st0 _k _buf _len); auto. qed.


end KeccakUpdstateRef.
