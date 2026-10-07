require import AllCore IntDiv List StdOrder.

require import BitEncoding.
import BS2Int.
import IntOrder.

from Jasmin require import JModel_x86.
from CryptoSpecs require import Keccak1600_Spec FIPS202_SHA3_Spec.
from JazzEC require import Keccak1600_Jazz.

require import Keccak_bindings.
require import Keccak1600_statebytes.

import SLH64.
import IntOrder.

(* MOVE TO SOMEWHERE ELSE? *)


(* get rid of unnecessary hypothesis *)
lemma size_drop' ['a] n (s: 'a list):
 size (drop n s) = max 0 (size s - max 0 n).
proof.
case: (0 <= n) => H.
 rewrite size_drop //; congr; congr.
 by rewrite ler_maxr.
rewrite (ler_maxl 0 n) 1:/# /=.
rewrite drop_le0 1:/#.
smt(size_ge0).
qed.

lemma size_memread':
  forall (mem : global_mem_t) (a : address) (sz : int),
    size (memread mem a sz) = max 0 sz.
proof.
move=> m a sz; case: (0<=sz) => H.
 by rewrite size_memread /#.
by rewrite /memread mkseq0_le /#.
qed.

lemma memread0' mem buf len:
 len <= 0 =>
 memread mem buf len = [].
proof. by move=> ?; rewrite /memread mkseq0_le. qed.


lemma u64bytes_or w1 w2 i:
(u64bytes (w1 `|` w2)).[i] = (u64bytes w1).[i] `|` (u64bytes w2).[i].
proof. by rewrite !nth_to_list orb8E. qed.

op u32bytes w = W4u8.to_list w.
lemma get_u32bytes i w:
 (u32bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 4) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.


op u16bytes w = W2u8.to_list w.
lemma get_u16bytes i w:
 (u16bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 2) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.


lemma bits8_u64_shl8 (w: W64.t) k i:
 0 <= i < 8 =>
 w `<<<` 8*k \bits8 i
 = if i < k then W8.zero else w \bits8 (i-k).
proof.
move=> ?.
apply W8.ext_eq => j Hj.
rewrite bits8iE //=.
rewrite (:0 <= i * 8 + j < 64) 1:/# /=.
case: (i<k) => C.
 by rewrite zerowE get_out /#.
by rewrite bits8iE 1:/# /#.
qed.

lemma bits8_u128_shl8 (w: W128.t) k i:
 0 <= i < 16 =>
 w `<<<` 8*k \bits8 i
 = if i < k then W8.zero else w \bits8 (i-k).
proof.
move=> ?.
apply W8.ext_eq => j Hj.
rewrite bits8iE //=.
rewrite (:0 <= i * 8 + j < 128) 1:/# /=.
case: (i<k) => C.
 by rewrite zerowE get_out /#.
by rewrite bits8iE 1:/# /#.
qed.

lemma bits8_zeroextu64_32 (w: W32.t) i:
 zeroextu64 w \bits8 i = if 0 <= i < 4 then w \bits8 i else W8.zero.
proof.
rewrite bits8E; apply W8.ext_eq => k Hk.
case: (0 <= i < 8) => Hi.
 rewrite initiE //= zeroextu64E pack2E initiE 1:/# /= initiE 1:/# /=.
 case: (0 <= i < 4) => C.
  by rewrite ifT 1:/# bits8E initiE /#.
 by rewrite ifF 1:/# zerowE zerowE.
by rewrite get_out 1:/# initiE //= get_out 1:/#.
qed.

lemma bits8_zeroextu64_16 (w: W16.t) i:
 zeroextu64 w \bits8 i = if 0 <= i < 2 then w \bits8 i else W8.zero.
proof.
rewrite bits8E; apply W8.ext_eq => k Hk.
case: (0 <= i < 8) => Hi.
 rewrite initiE //= zeroextu64E pack4E initiE 1:/# /= initiE 1:/# /=.
 case: (0 <= i < 2) => C.
  by rewrite ifT 1:/# bits8E initiE /#.
 by rewrite ifF 1:/# zerowE zerowE.
by rewrite get_out 1:/# initiE //= get_out 1:/#.
qed.

lemma bits8_zeroextu64_8 (w: W8.t) i:
 zeroextu64 w \bits8 i = if i=0 then w else W8.zero.
proof.
rewrite bits8E; apply W8.ext_eq => k Hk.
case: (0 <= i < 8) => Hi.
 rewrite initiE //= zeroextu64E pack8E initiE 1:/# /= initiE 1:/# /=.
 case: (i=0) => C.
  by rewrite ifT /#.
 by rewrite ifF /#.
by rewrite initiE //= ifF 1:/# get_out 1:/#.
qed.

lemma u64bytes_cat (w0 w1: W64.t):
 u64bytes w0 ++ u64bytes w1
 = u128bytes (VPINSR_2u64 (VMOV_64 w0) w1 W8.one).
proof.
by rewrite /VPINSR_2u64 to_uint1 /= /u64bytes /u128bytes /=.
qed.

lemma u64bytes_cat0w (w: W64.t):
 u64bytes zero ++ u64bytes w
 = u128bytes (VPINSR_2u64 zero w W8.one).
proof.
by rewrite /VPINSR_2u64 to_uint1 /= /u64bytes /u128bytes /=.
qed.

lemma u128bytes_cat (w0 w1: W128.t):
 u128bytes w0 ++ u128bytes w1
 = u256bytes (VINSERTI128 (zeroextu256 w0) w1 W8.one).
proof.
by rewrite /VINSERTI128 to_uint1 /= /u128bytes /u256bytes /= zeroextu256E.
qed.

lemma u128bytes_cat0w (w: W128.t):
 u128bytes zero ++ u128bytes w
 = u256bytes (VINSERTI128 zero w W8.one).
proof.
by rewrite /VINSERTI128 to_uint1 /= /u128bytes /u256bytes /=.
qed.

lemma zeroextu128_zero:
 zeroextu128 W64.zero = W128.zero
by circuit.

lemma zeroextu256_zero:
 zeroextu256 W128.zero = W256.zero
by circuit.

(******************************************************************************
 *                        SHIFT operations                                    *
 ******************************************************************************)

lemma u64_shl0 (w: W64.t): w `<<<` 0 = w.
proof. by apply W64.wordP => i Hi; rewrite shlwE Hi /=. qed.

lemma SHLQ_ll: islossless M.__SHLQ
by islossless.

hoare SHLQ_h _w _sh:
 M.__SHLQ
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 8
 ==> res = _w `<<<` (8*_sh).
proof.
proc; simplify.
if => //.
 auto => /> *.
 by rewrite /W64.(`<<`) of_uintK modz_small /#.
by auto => /> *; rewrite u64_shl0.
qed.

phoare SHLQ_ph _w _sh:
 [ M.__SHLQ
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 8
 ==> res = _w `<<<` (8*_sh)
 ] = 1%r.
proof. by conseq SHLQ_ll (SHLQ_h _w _sh). qed.

lemma SHLDQ_ll: islossless M.__SHLDQ
by islossless.

hoare SHLDQ_h _w _sh:
 M.__SHLDQ
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 16
 ==> res = _w `<<<` (8*_sh).
proof.
proc; simplify.
if => //.
 auto => /> *.
 by rewrite /VPSLLDQ_128 of_uintK modz_small /#.
auto => /> *; apply W128.wordP => i Hi.
by rewrite shlwE Hi /=.
qed.

phoare SHLDQ_ph _w _sh:
 [ M.__SHLDQ
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 16
 ==> res = _w `<<<` (8*_sh)
 ] = 1%r.
proof. by conseq SHLDQ_ll (SHLDQ_h _w _sh). qed.

lemma SHLQ_256_ll: islossless M.__SHLQ_256
by islossless.

hoare SHLQ_256_h _w _sh:
 M.__SHLQ_256
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 16
 ==> res = W4u64.pack4 [ (_w \bits64 0) `<<<` (8*_sh)
                       ; (_w \bits64 1) `<<<` (8*_sh)
                       ; (_w \bits64 2) `<<<` (8*_sh)
                       ; (_w \bits64 3) `<<<` (8*_sh)
                       ].
proof.
proc; simplify.
if => //.
 auto => /> *.
 by rewrite /VPSLL_4u64 /= !of_uintK !modz_small /#.
by auto => /> *; rewrite !u64_shl0 pack4E /= -all_eqP /all_eq /=.
qed.

phoare SHLQ_256_ph _w _sh:
 [ M.__SHLQ_256
 : x = _w /\ shbytes = _sh /\ 0 <= _sh < 16
 ==> res = W4u64.pack4 [ (_w \bits64 0) `<<<` (8*_sh)
                       ; (_w \bits64 1) `<<<` (8*_sh)
                       ; (_w \bits64 2) `<<<` (8*_sh)
                       ; (_w \bits64 3) `<<<` (8*_sh)
                       ]
 ] = 1%r.
proof. by conseq SHLQ_256_ll (SHLQ_256_h _w _sh). qed.


(******************************************************************************
 *                        SUBREAD operations                                  *
 ******************************************************************************)

(**
  Abstract specification of SUBREAD acting on lists of bytes.

 remark: these specifications shall later be instantiated into memory and array
 read/writes.
*)

op u8prefAt (lw: bytes) off (l: bytes) =
 forall i,
  lw.[i] = if (max 0 off) <= i < size lw
           then l.[i-max 0 off]
           else W8.zero.

lemma u8prefAt0 lw cur at l n:
 u8prefAt lw (at - cur) l =>
 cur + size lw <= at \/ l = u8zeros n =>
 lw = u8zeros (size lw).
proof.
move => H [H1|Hl]; apply (eq_from_nth W8.zero);
 1,3:(by rewrite size_nseq; smt(size_ge0));
 move => i Hi; rewrite H nth_u8zeros;
 case: (max 0 (at-cur) <= i) => C //=; rewrite ifT 1:/#.
 by rewrite nth_out ?size_rcons //; smt(size_ge0). 
by rewrite Hl nth_u8zeros.
qed.

lemma nth_u64bytes_shl l w k i:
 0 <= k =>
 u8prefAt (u64bytes w) 0 l =>
 (u64bytes (w `<<<` 8 * k)).[i]
 = if k <= i < 8 then l.[i - k] else W8.zero.
proof.
move=> Hk H.
case: (0 <= i < 8) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
rewrite nth_to_list bits8_u64_shl8 // -nth_to_list H ler_maxr //=.
by rewrite size_to_list; smt(nth_out).
qed.

lemma nth_u128bytes_shl l w k i:
 0 <= k =>
 u8prefAt (u128bytes w) 0 l =>
 (u128bytes (w `<<<` 8 * k)).[i]
 = if k <= i < 16 then l.[i - k] else W8.zero.
proof.
move=> Hk H.
case: (0 <= i < 16) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
rewrite nth_to_list bits8_u128_shl8 // -nth_to_list H ler_maxr //=.
by rewrite size_to_list; smt(nth_out).
qed.

abbrev u8prefAbsorb (lw: bytes) off (l: bytes) tb =
 u8prefAt lw off (rcons l (of_int tb)).

lemma u8prefAbsorbP lw off l tb:
 u8prefAbsorb lw off l tb <=>
 forall i,
  lw.[i] = if (max 0 off) <= i < size lw
           then if i-max 0 off = size l
                then W8.of_int tb
                else l.[i-max 0 off]
           else W8.zero.
proof. smt(nth_rcons nth_out). qed.

lemma u8prefAbsorb0 lw cur at l tb:
 u8prefAbsorb lw (at - cur) l tb =>
 cur + size lw <= at \/ l=[] /\ tb=0 =>
 lw = u8zeros (size lw).
proof.
move=> /u8prefAt0 H [H1|[E1 E2]]; apply (H 1); first smt().
by right; rewrite -cats1 E1 E2 /= nseq1.
qed.

lemma u8prefAbsorbW lw at l tb:
 size lw <= size l =>
 u8prefAt lw at l =>
 u8prefAbsorb lw at l tb.
proof.
move=> Hl H; apply u8prefAbsorbP => i.
rewrite H; case: (max 0 at <= i < size lw) => ?//.
by rewrite ifF 1:/#.
qed.

op srincr sz (cur at len:int) =
 if 0 <= at-cur < sz
 then min (max 0 len) (cur+sz-at)
 else 0.

lemma srincr_out sz cur at l:
 ! 0 <= at-cur < sz => srincr sz cur at l = 0
by smt().

op srfnsh sz (cur at len tb:int) =
 if 0 <= at-cur < sz
 then 0 <= len /\ at+len < cur+sz /\ tb<>0
 else false.

abbrev srat sz cur at len tb =
 at + srincr sz cur at len + b2i (srfnsh sz cur at len tb).
abbrev srtb sz cur at len tb =
 if srfnsh sz cur at len tb then 0 else tb.
abbrev srl sz cur at (l:W8.t list) =
 drop (srincr sz cur at (size l)) l.
abbrev srlen sz cur at len =
 len-(srincr sz cur at len).

lemma srincr0 sz cur at:
 srincr sz cur at 0 = 0
by smt().
lemma srtb0 sz cur at:
 srtb sz cur at 0 0 = 0
by smt().
lemma srl0 sz cur at:
 srl sz cur at [] = []
by smt().
lemma srat0 sz cur at:
 srat sz cur at 0 0 = at
by smt().

lemma srincr_add tb sz1 sz2 cur at len:
 0 <= sz1 => 0 <= sz2 =>
 srincr (sz1+sz2) cur at len
 = srincr sz1 cur at len
   + srincr sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len)
by smt().

lemma srfnsh_add sz1 sz2 cur at len tb:
 0 <= sz1 => 0 <= sz2 =>
 srfnsh (sz1+sz2) cur at len tb
 = (srfnsh sz1 cur at len tb
    \/ srfnsh sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len) (srtb sz1 cur at len tb))
by smt().

lemma srat_add sz1 sz2 cur at len tb:
 0 <= sz1 => 0 <= sz2 =>
 srat (sz1+sz2) cur at len tb
 = srat sz1 cur at len tb
   + srincr sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len)
   + b2i (srfnsh sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len) (srtb sz1 cur at len tb))
by smt().

lemma srlen_add tb sz1 sz2 cur at len:
 0 <= sz1 => 0 <= sz2 => 0 <= len =>
 srlen (sz1+sz2) cur at len
 = srlen sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len)
by smt().

lemma srtb_add sz1 sz2 cur at len tb:
 0 <= sz1 => 0 <= sz2 =>
 srtb (sz1+sz2) cur at len tb
 = if srfnsh sz1 cur at len tb
   then 0
   else srtb sz2 (cur+sz1) (srat sz1 cur at len tb) (srlen sz1 cur at len) (srtb sz1 cur at len tb)
by smt().

lemma srl_add tb sz1 sz2 cur at l:
 0 <= sz1 => 0 <= sz2 =>
 srl (sz1+sz2) cur at l
 = srl sz2 (cur+sz1) (srat sz1 cur at (size l) tb) (srl sz1 cur at l).
proof. 
move=> ??.
by rewrite (srincr_add tb) // addzC -drop_drop; smt(size_drop size_ge0).
qed.


op srpre (cur at:int) (l: bytes) (len tb:int) =
 0 <= cur /\ 0 <= at /\ 0 <= tb < 256 /\
 len = size l /\
(*
 at + size l + b2i (tb<>0) <= 200 /\
*)
 (cur <= at \/ l=[] /\ tb=0).

lemma srpre_next sz (cur at:int) (l: bytes) (len tb:int):
 0 <= sz =>
 srpre cur at l len tb =>
 srpre (cur+sz) (srat sz cur at len tb) (srl sz cur at l) (srlen sz cur at len) (srtb sz cur at len tb).
proof.
move => /> Hsz Hcur Hat Htb0 Htb1 (*H200*) [H|] />;
smt(size_drop size_ge0).
qed.

op srspec lw (cur at:int) (l:W8.t list) (len tb:int) =
 srpre cur at l len tb =>
 srpre (cur+size lw)
       (srat (size lw) cur at len tb)
       (srl (size lw) cur at l)
       (srlen (size lw) cur at len)
       (srtb (size lw) cur at len tb)
 /\ u8prefAbsorb lw (at-cur) l tb.

lemma srpreP cur at l len tb:
 srpre cur at l len tb => cur <= at \/ l=[] /\ tb=0
by smt().

lemma srspec_cat lw1 lw2 cur at l len tb:
 srspec lw1 cur at l len tb =>
 srspec lw2 (cur+size lw1) (srat (size lw1) cur at len tb) (srl (size lw1) cur at l) (srlen (size lw1) cur at len) (srtb (size lw1) cur at len tb) =>
 srspec (lw1++lw2) cur at l len tb.
proof.
have Hsz1:= (size_ge0 lw1).
have Hsz2:= (size_ge0 lw2).
have Hszl:= (size_ge0 l).
case: (srpre cur at l len tb) => Hpre; last smt().
move=> H1 H2 _; move: (H1 Hpre) => {H1} [Hpre1 /u8prefAbsorbP H1].
move: (H2 Hpre1) => {H2} [Hpre2 /u8prefAbsorbP H2].
rewrite !size_cat srat_add 1..2:/# (srl_add tb) 1..2:/# (srlen_add tb) 1..3:/# srtb_add 1..2:/#.
split; first smt().
move: Hpre H1 H2 => /> ????(*?*) [Hat|[]->->]; last first.
 move=> /u8prefAbsorbP /u8prefAbsorb0 T1 /u8prefAbsorbP /u8prefAbsorb0; move: T1=> /= -> -> i.
 by rewrite cat_nseq 1..2:/# nth_u8zeros size_nseq /#.
move=> H1 H2 i.
rewrite nth_cat; case: (i<size lw1) => C1.
 case: (i < 0) => C2; first by rewrite nth_out 1:/# ifF 1:/#.
 case: (max 0 (at-cur) <= i) => C3 /=.
  by rewrite nth_rcons size_cat ifT 1:/# H1 ifT 1:/#; smt(nth_out).
 by rewrite H1 /= ifF 1:/#.
rewrite H2 size_cat.
case: (i < size lw1+size lw2) => C2/=; last first.
 by rewrite ifF /#.
case: (max 0 (at - cur) <= i) => C3; last by rewrite ifF 1:/#.
rewrite ifT 1:/# nth_rcons.
case: (i - max 0 (at - cur) = size l) => C4.
 rewrite ifT ?size_drop'; smt(nth_out nth_cat).
move: (srpreP _ _ _ _ _ Hpre1); case:( cur + size lw1 <= srat (size lw1) cur at (size l) tb) => C5/=; last first.
 by move => [] -> -> /=; smt(nth_out size_cat).
rewrite size_drop 1:/#.
case: (i = size lw1) => HHH.
 rewrite HHH /=.
 case: (srat (size lw1) cur at (size l) tb = cur + size lw1) => CC; last smt().
 rewrite CC /= ler_maxl 1:/# /=.
 case: (size l = srincr (size lw1) cur at (size l)) => CCC.
  by rewrite CCC /= ifT 1:/#; smt(nth_out nth_cat).
 by rewrite ifF 1:/# nth_drop; smt(nth_cat).
rewrite ifF.
 move: C5; case: (tb=0) => C6; first smt().
 rewrite /srfnsh C6 size_ge0 /=.
 case: ((0 <= at - cur < size lw1 && at + size l < cur + size lw1)) => C7/=; last smt().
 rewrite b2i1 /srincr. 
 have ?: size l < (cur + size lw1 - at) by smt().
 rewrite ler_minl 1:/# ifT 1:/# => ?.
 rewrite (ler_maxr _ (size l)); first smt(size_ge0).
 have ->: at + size l = cur + size lw1 - 1 by smt().
 by rewrite /= ler_maxr /#.
by rewrite nth_drop 1..2:/# /srfnsh /srincr; smt(nth_out nth_cat).
qed.

lemma srspec_ahead len1 tb1 lw cur at l len tb:
 size l = len =>
 0 <= len1 <= len =>
 0 <= tb1 < 256 =>
 0 <= at-cur < 8 =>
 cur + size lw <= at + len1 => 
 srspec lw cur at (take len1 l) len1 tb1 =>
 srspec lw cur at l len tb.
proof.
move => Elen Elen1 Htb Hat Hlen H Hpre; split.
 by apply srpre_next; smt(size_ge0).
move: (H _).
 smt(size_take).
move => [_ HH] i.
rewrite HH ler_maxr 1:/#.
case: (at - cur <= i < size lw) => C//.
rewrite !nth_rcons size_take 1:/#.
have ?: 0 <= i-(at-cur) < len1 by smt().
by rewrite ifT 1:/# ifT 1:/# nth_take /#.
qed.

lemma srspec_tb w cur at l len tb:
 srspec (u64bytes w) cur at l len 0 =>
 cur <= at =>
 at + len < cur + 8 =>
 srspec (u64bytes (w `|` (W64.of_int (tb %% 256) `<<` W8.of_int (8 * (at + len - cur))))) cur at l len tb.
proof.
move => H Hcur Hl Hpre; rewrite size_to_list; split; first by rewrite srpre_next.
have HHpre: srpre cur at l len 0 by smt().
move: (H HHpre) => {H} [_ H].
move=> i; rewrite size_to_list nth_rcons u64bytes_or ler_maxr 1:/#.
case: (at - cur <= i < 8) => C; last first.
 rewrite H ler_maxr 1:/# size_to_list C /=.
 case: (i < 0 \/ 8 <= i) => C2.
  by rewrite nth_out // size_to_list /#.
 rewrite shl_shlw; first smt(size_ge0).
 rewrite (nth_u64bytes_shl [W8.of_int tb]).
   smt(size_ge0).
  move=> j; case: (j=0) => C4.
   rewrite size_to_list nth_to_list ifT 1:/# ifT 1:/#.
   by rewrite of_int_bits8_div 1:/# C4 /= /#.
  case: (0 <= j < 8) => C5 //.
   rewrite nth_to_list of_int_bits8_div // divz_small //. 
    split; first smt().
    move=> _; rewrite exprM. 
    apply (ltr_le_trans W8.modulus); first smt().
    by rewrite {1}(:W8.modulus=W8.modulus^1) 1:/#; smt(ler_eexpr).
   smt().
  by rewrite nth_out ?size_to_list // /#.
 by rewrite ifF; smt(size_ge0).
case: (i-(at-cur) < size l) => C2.
 rewrite shl_shlw 1:/# (nth_u64bytes_shl [W8.of_int tb]) 1:/#.
  move=> j; rewrite ler_maxr // size_to_list.
  case: (j<0 \/ 8 <= j) => ?.
   rewrite nth_out.
    by rewrite size_to_list /#.
   by rewrite ifF 1:/#.
  case: (j=0) => C3.
   rewrite ifT 1:/# C3 /= get_u64bytes /=.
   by rewrite of_int_bits8_div /#.
  rewrite /= C3 /= get_u64bytes.
  rewrite of_int_bits8_div 1:/# divz_small //.
  split; first smt().
  move=> _; rewrite exprM.
  by apply (ltr_le_trans W8.modulus); smt(ler_eexpr).
 by rewrite H nth_rcons size_to_list ifT 1:/# ifT 1:/# (nth_out _ [W8.of_int tb]) 1:/# orw0 /#.
rewrite H size_to_list nth_rcons.
case: (max 0 (at - cur) <= i < 8) => C3; last first.
 by rewrite or0w shl_shlw 1:/# (nth_u64bytes_shl [W8.of_int tb]) /#.
rewrite ifF 1:/# or0w shl_shlw. 
 smt(size_ge0).
rewrite (nth_u64bytes_shl [W8.of_int tb]); last smt().
 smt(size_ge0).
move=> j; case: (j=0) => C4.
 rewrite size_to_list nth_to_list ifT 1:/# ifT 1:/#.
 by rewrite of_int_bits8_div 1:/# C4 /= /#.
rewrite size_to_list ler_maxr 1:/# C4 /=.
case: (0 <= j < 8) => C5 //.
 rewrite nth_to_list of_int_bits8_div // divz_small //. 
 split; first smt().
 move=> _; rewrite exprM. 
 apply (ltr_le_trans W8.modulus); first smt().
 by rewrite {1}(:W8.modulus=W8.modulus^1) 1:/#; smt(ler_eexpr).
by rewrite nth_out //.
qed.


lemma u8prefAt_zeroext_u32 w l:
 size l = 4 =>
 u8prefAt (u32bytes w) 0 l => u8prefAt (u64bytes (zeroextu64 w)) 0 l.
proof.
move=> Hl H i; rewrite get_u64bytes bits8_zeroextu64_32 ler_maxr 1:// size_to_list.
case: (0 <= i < 4) => C.
 by rewrite ifT 1:/# -get_u32bytes H size_to_list ifT /#.
smt(nth_out).
qed.

lemma srspec_u32 (w: W32.t) cur at l:
 0 <= at-cur < 8 =>
 u8prefAt (u32bytes w) 0 l => (*(memread _m _buf 4)*)
 size l = 4 =>
 srspec (u64bytes ((zeroextu64 w) `<<<` 8*(at-cur))) cur at l 4 0.
proof.
move=> Hcur Hw Hl Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list ler_maxr 1:/#.
case: (0 <= i < 8) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
case: (at-cur <= i < 8) => C.
 rewrite (nth_u64bytes_shl l) 1:/#.
  by apply u8prefAt_zeroext_u32.
 rewrite C /= -cats1 nth_cat Hl.
 case: (i - (at - cur) < 4) => C2 //.
 smt(nth_out).
rewrite  (nth_u64bytes_shl l) // 1:/#.
 by apply u8prefAt_zeroext_u32.
smt(nth_out).
qed.

lemma srspec_u64 w cur at l len :
 0 <= at-cur < 8 =>
 u8prefAt (u64bytes w) 0 l =>
 srspec (u64bytes (w `<<<` 8*(at-cur))) cur at l len 0.
proof.
move=> Hcur Hw Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list.
case: (0 <= i < 8) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
rewrite ler_maxr 1:/# (nth_u64bytes_shl l) 1:/# //.
smt(nth_rcons nth_out).
qed.

lemma srspec_u128 w cur at l len :
 0 <= at-cur < 16 =>
 u8prefAt (u128bytes w) 0 l =>
 srspec (u128bytes (w `<<<` 8*(at-cur))) cur at l len 0.
proof.
move=> Hcur Hw Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list.
case: (0 <= i < 16) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
rewrite ler_maxr 1:/# (nth_u128bytes_shl l) 1:/# //.
smt(nth_rcons nth_out).
qed.

lemma srspec_u256 w cur l len :
 u8prefAt (u256bytes w) 0 l =>
 srspec (u256bytes w) cur cur l len 0.
proof.
move=> Hw Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list.
case: (0 <= i < 32) => Hi; last first.
 by rewrite nth_out ?size_to_list /#.
rewrite ler_maxr 1:/# /= Hi /= nth_rcons.
rewrite Hw size_to_list ler_maxr 1:/# Hi /=.
by case: (i < size l) => ? //; smt(nth_out).
qed.

lemma srspec_u64_shl tb w cur at l len:
 0 <= at-cur < 8 =>
 tb = 0 \/ 8 <= len =>
 u8prefAt (u64bytes w) 0 l =>
 srspec (u64bytes (w `<<<` 8*(at-cur))) cur at l len tb.
proof.
move=> Hcur H Hw Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list ler_maxr 1:/#.
case: (0 <= i < 8) => ?; last first.
 by rewrite nth_out ?size_to_list /#.
case: (at-cur <= i < 8) => C.
 rewrite (nth_u64bytes_shl l) 1:/# // C /= nth_rcons.
 case: (i - (at - cur) < size l) => ?//=.
 by elim: H; smt(nth_out).
by rewrite  (nth_u64bytes_shl l) 1:/# //; smt(nth_out).
qed.

lemma srspec_u128_shl tb w cur at l len:
 0 <= at-cur < 16 =>
 tb = 0 \/ 16 <= len =>
 u8prefAt (u128bytes w) 0 l =>
 srspec (u128bytes (w `<<<` 8*(at-cur))) cur at l len tb.
proof.
move=> Hcur H Hw Hpre.
split.
 by rewrite size_to_list srpre_next.
move=> i; rewrite size_to_list ler_maxr 1:/#.
case: (0 <= i < 16) => ?; last first.
 by rewrite nth_out ?size_to_list /#.
case: (at-cur <= i < 16) => C.
 rewrite (nth_u128bytes_shl l) 1:/# // C /= nth_rcons.
 case: (i - (at - cur) < size l) => ?//=.
 by elim: H; smt(nth_out).
by rewrite  (nth_u128bytes_shl l) 1:/# //; smt(nth_out).
qed.

lemma srspec_u64_u128 w cur at l len tb:
 0 <= at - cur < 16 =>
 cur + 8 <= at =>
 srspec (u64bytes w) (cur + 8) at l len tb =>
 srspec (u128bytes (VPINSR_2u64 zero w one)) cur at l len tb.
proof.
move=> Hat Hcur H Hpre; split; first by apply srpre_next; smt(W16u8.size_to_list).
have Hpre': srpre (cur+8) at l len tb by smt().
move: (H Hpre') => [_/u8prefAbsorbP {H} H].
rewrite -u64bytes_cat0w u8prefAbsorbP => i.
rewrite nth_cat size_cat !size_to_list /= u64bytes0 nth_u8zeros H.
case: (i<8) => ?; first by rewrite ifF /#.
rewrite size_to_list ler_maxr 1:/# ler_maxr 1:/#.
by case: (at - cur <= i < 16) => ? /#.
qed.

lemma srspec_u128_u256 w cur at l len tb:
 0 <= at - cur < 32 =>
 cur + 16 <= at =>
 srspec (u128bytes w) (cur + 16) at l len tb =>
 srspec (u256bytes (VINSERTI128 zero w one)) cur at l len tb.
proof.
move=> Hat Hcur H Hpre; split; first by apply srpre_next; smt(W32u8.size_to_list).
have Hpre': srpre (cur+16) at l len tb by smt().
move: (H Hpre') => [_/u8prefAbsorbP {H} H].
rewrite -u128bytes_cat0w u8prefAbsorbP => i.
rewrite nth_cat size_cat !size_to_list /= u128bytes0 nth_u8zeros H.
case: (i<16) => ?; first by rewrite ifF /#.
rewrite size_to_list ler_maxr 1:/# ler_maxr 1:/#.
by case: (at - cur <= i < 32) => ? /#.
qed.

lemma srspec_split l1 l2 w1 w2 cur at l len at1:
 0 <= at-cur < 8 =>
 l = l1++l2 =>
 at1 = at + size l1 =>
 at1 < cur + 8 =>
 u8prefAt (u64bytes w2) 0 l2 =>
 srspec (u64bytes w1) cur at l1 (len - size l2) 0 =>
 srspec (u64bytes (w1 `|` (w2 `<<<` 8*(at1-cur)))) cur at l len 0.
proof.
move=> Hcur -> -> Hat Hw2 H1 Hpre; split.
 by rewrite size_to_list; apply srpre_next.
move: (H1 _); first smt(size_ge0 size_cat).
move=> {H1} []_ Hw1 i.
rewrite size_to_list u64bytes_or Hw1 ler_maxr 1:/# size_to_list (nth_u64bytes_shl l2) //.
 smt(size_ge0).
case: (at - cur <= i < 8) => C1; last first.
 rewrite or0w; smt(nth_out size_ge0).
rewrite !nth_rcons nth_cat ?size_cat.
case: (i - (at - cur) = size l1) => C2.
 rewrite ifF 1:/# or0w; smt(nth_out).
case: (at + size l1 - cur <= i < 8) => C3.
 rewrite nth_out 1:/# or0w.
 smt(nth_out size_ge0).
smt(nth_out size_ge0).
qed.

lemma srspec_w4_w2 l l1 w1 w2 cur at at1 l2 len:
 len = size l =>
 l1 = take (len%/4*4) l =>
 l2 = take (len%/2*2) l =>
 0 <= at - cur < 8 =>
 0 <= len < 8 =>
 2 <= len%%4 =>
 at1 = at + len%/4*4 =>
 at1 < cur+8 =>
 u8prefAt (u16bytes w2) 0 (drop (len%/4*4) l) =>
 srspec (u64bytes w1) cur at l1 (len%/4*4) 0 =>
 srspec (u64bytes (w1 `|` ((zeroextu64 w2) `<<<` 8*(at1-cur)))) cur at l2 (len%/2*2) 0.
proof.
move => Hlen -> -> Hcur Hsz H2 Hat H Hpref H4.
apply (srspec_split (take (len%/4*4) l) (take 2 (drop (len%/4*4) l)) w1 (zeroextu64 w2) cur at (take (len%/2*2) l) (len%/2*2) at1) => //.
+ rewrite -(cat_take_drop (len%/4*4) (take _ _)) take_take ifT 1:/#; congr.
  by rewrite drop_take /#.
+ smt(size_take).
+ move => i; rewrite get_u64bytes bits8_zeroextu64_16 -get_u16bytes Hpref ler_maxr //= !size_to_list.
  case: (0 <= i < 2) => C.
   by rewrite ifT 1:/# nth_take 1..2:/# nth_drop 1..2:/#.
  case: (0 <= i < 8) => //?.
  by rewrite nth_out // size_take // size_drop /#.
smt(size_take size_drop).
qed.

lemma srspec_w2_w1 l l1 w1 w2 cur at at1 len:
 len = size l =>
 l1 = take (len%/2*2) l =>
 0 <= at - cur < 8 =>
 0 <= len < 8 =>
 1 <= len%%2 =>
 at1 = at + len%/2*2 =>
 at1 < cur+8 =>
 u8prefAt [w2] 0 (drop (len%/2*2) l) =>
 srspec (u64bytes w1) cur at l1 (len%/2*2) 0 =>
 srspec (u64bytes (w1 `|` ((zeroextu64 w2) `<<<` 8*(at1-cur)))) cur at l len 0.
proof.
move => Hlen -> Hcur Hsz H2 Hat H Hpref H4.
apply (srspec_split (take (len%/2*2) l) (drop (len%/2*2) l) w1 (zeroextu64 w2) cur at l len at1) => //.
+ by rewrite (cat_take_drop (len%/2*2)).
+ smt(size_take).
+ move => i; rewrite get_u64bytes bits8_zeroextu64_8.
  have ->:(if i=0 then w2 else W8.zero)=[w2].[i] by smt(nth_out).
  rewrite Hpref ler_maxr //= !size_to_list.
  case: (0 <= i < 1) => C.
   by rewrite ifT 1:/# nth_drop 1..2:/#.
  case: (0 <= i < 8) => //?.
  by rewrite nth_out // size_drop /#.
smt(size_take size_drop).
qed.


(***************************************
      MEMORY reads/writes
****************************************)



lemma drop_srl_memread (mem: global_mem_t) off len sz cur at:
 0 <= sz =>
 drop (srincr sz cur at len) (memread mem off len)
 = memread mem (off+srincr sz cur at len) (len-srincr sz cur at len).
proof.
move=> Hsz; apply (eq_from_nth W8.zero).
rewrite size_drop' /srincr !size_memread' 1:/#.
rewrite size_drop' size_memread' => i Hi.
rewrite nth_memread /srl' 1:/# nth_drop; 1..2: smt(size_ge0).
by rewrite nth_memread; smt(size_ge0).
qed.

op msubreadpre m (lw: W8.t list) (cur at off len tb:int) =
 srpre cur at (memread m off len) len tb.

op msubread (m : global_mem_t) lw (cur at off len tb:int) at2 off2 len2 tb2 =
 srspec lw cur at (memread m off len) len tb
 /\ at2 = srat (size lw) cur at len tb
 /\ off2 = off + srincr (size lw) cur at len
 /\ len2 = len - srincr (size lw) cur at len
 /\ tb2 = srtb (size lw) cur at len tb.

lemma msubread_nil (m: global_mem_t) (cur at off len tb: int):
 msubread m [] cur at off len tb at off len tb
by smt().

lemma msubread0 (m: global_mem_t) (lw:W8.t list) (cur at off len tb: int):
 lw=u8zeros (size lw) => (len < 0 \/ at<cur \/ cur+size lw <= at \/ len=0 /\ tb=0) => msubread m lw cur at off len tb at off len tb.
proof.
move=> -> [H|[H|[|[->->]]]]; rewrite /msubread size_nseq.
+ split; last smt().
  by apply absurd => _; rewrite /srpre size_memread' /#.
+ split; last smt().
  by move=> Hpre; rewrite size_nseq; smt(nth_u8zeros).
+ rewrite ler_maxr; first smt(size_ge0).
  move=> H; split; last smt().
  move=> Hpre; split.
   by rewrite srpre_next; smt(size_ge0).
  rewrite u8prefAbsorbP => i; rewrite size_nseq size_memread' nth_u8zeros.
  case: (0 <= i < size lw) => C; last smt().
  by rewrite nth_out /#.
split; last smt().
by move=> ?; rewrite memread0 size_nseq; smt(size_ge0 nth_u8zeros).
qed.

lemma msubread_cat m lw1 lw2 (cur at dlt len tb:int) at1 dlt1 len1 tb1 at2 dlt2 len2 tb2:
 msubread m lw1 cur at dlt len tb at1 dlt1 len1 tb1 =>
 msubread m lw2 (cur+size lw1) at1 dlt1 len1 tb1 at2 dlt2 len2 tb2 =>
 msubread m (lw1++lw2) cur at dlt len tb at2 dlt2 len2 tb2.
proof.
rewrite /msubread => /= [#]H1 Hat1 Hdlt1 Hlen1 Htb1.
move => /= [#]H2 Hat2 Hdlt2 Hlen2 Htb2.
split; last first.
 by rewrite size_cat srat_add; smt(size_ge0).
move => Hpre; move:(Hpre).
have Hl: memread m dlt1 len1 = srl (size lw1) cur at (memread m dlt len)
 by smt(size_ge0 drop_srl_memread).
by apply (srspec_cat lw1 lw2 cur at (memread m dlt len) len tb) => // /#.
qed.

lemma loadW32_memread m buf len:
 4 <= len =>
 u8prefAt (u32bytes (loadW32 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 4) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u32bytes loadW32_bits8 // ler_maxr // size_to_list C /=.
by rewrite /loadW8 nth_mkseq 1:/#.
qed.

lemma msubread_u32 _m _cur _at _buf:
 0 <= _at-_cur < 8 =>
 msubread _m (u64bytes (zeroextu64 (loadW32 _m _buf) `<<<` 8 * (_at - _cur))) _cur _at
            _buf 4 0 (_at + min (_cur + 8 - _at) 4) (_buf + min (_cur + 8 - _at) 4) (4 - min (_cur + 8 - _at) 4) 0.
proof.
move=> Hat; rewrite /msubread; split; last by rewrite size_to_list /#.
apply srspec_u32; first smt(). 
 by apply loadW32_memread; smt().
by rewrite size_memread.
qed.

lemma loadW64_memread m buf len:
 8 <= len =>
 u8prefAt (u64bytes (loadW64 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 8) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u64bytes loadW64_bits8 // ler_maxr // size_to_list C /=.
by rewrite /loadW8 nth_mkseq 1:/#.
qed.

lemma msubread_u64 _m _cur _at _buf _len _tb:
 8 <= _len =>
 0 <= _at-_cur < 8 =>
 msubread _m (u64bytes (loadW64 _m _buf `<<<` 8 * (_at - _cur))) _cur _at
            _buf _len _tb (_cur + 8) (_buf + (_cur + 8 - _at)) (_len - (_cur + 8 - _at)) _tb.
proof.
move=> Hlen Hat; rewrite /msubread; split; last first.
 by rewrite size_to_list; smt(size_memread).
apply srspec_u64_shl => //; first smt().
by apply loadW64_memread; smt().
qed.

lemma loadW128_memread m buf len:
 16 <= len =>
 u8prefAt (u128bytes (loadW128 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 16) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u128bytes loadW128_bits8 // ler_maxr // size_to_list C /=.
by rewrite /loadW8 nth_mkseq 1:/#.
qed.

lemma msubread_u128 _m _cur _at _buf _len _tb:
 16 <= _len =>
 0 <= _at-_cur < 16 =>
 msubread _m (u128bytes (loadW128 _m _buf `<<<` 8 * (_at - _cur))) _cur _at
            _buf _len _tb (_cur + 16) (_buf + (16-(_at-_cur))) (_len - (16-(_at-_cur))) _tb.
proof.
move=> Hlen Hat; rewrite /msubread; split; last first.
 by rewrite size_to_list; smt(size_memread).
apply srspec_u128_shl => //; first smt().
by apply loadW128_memread; smt().
qed.

lemma loadW256_bits8 m p i:
 0 <= i < 32 =>
 loadW256 m p \bits8 i = loadW8 m (p+i).
proof. by move=> Hi; rewrite /loadW256 pack32bE // initiE //. qed.

lemma loadW256_memread m buf len:
 32 <= len =>
 u8prefAt (u256bytes (loadW256 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 32) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u256bytes loadW256_bits8 // ler_maxr // size_to_list C /=.
by rewrite /loadW8 nth_mkseq 1:/#.
qed.

lemma msubread_u256 _m _cur _buf _len _tb:
 32 <= _len =>
 msubread _m (u256bytes (loadW256 _m _buf)) _cur _cur
            _buf _len _tb (_cur + 32) (_buf + 32) (_len - 32) _tb.
proof.
move=> Hlen; rewrite /msubread; split; last first.
 by rewrite size_to_list; smt(size_memread).
move=> Hpre /=; split.
 by apply srpre_next; smt(W32u8.size_to_list).
apply u8prefAbsorbW; first rewrite size_to_list size_memread /#.
by apply loadW256_memread.
qed.

lemma msubread_ahead m w1 cur at buf len at1 buf1 len1 len2 tb:
 0 <= at-cur < 8 =>
 0 <= len <= len2  =>
 at1 = cur+8 =>
 msubread m (u64bytes w1) cur at buf len 0
          at1 buf1 len1 0 =>
 msubread m (u64bytes w1) cur at buf len2 tb
          at1 buf1 (len2-(cur+8-at)) tb.
proof.
move=> Hcur Hlen Hat [H1 H].
pose L:= len2-len.
have {1}->: len2 = len + L by smt().
have ?: at1 = min (cur+8) (at+len). 
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= => _ /#.
split; last first.
 by rewrite /srfnsh /srincr size_to_list /#.
apply (srspec_ahead len 0); smt(take_memread size_memread W8u8.size_to_list).
qed.

lemma loadW16_memread m buf len:
 2 <= len =>
 u8prefAt (u16bytes (loadW16 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 2) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u16bytes ler_maxr // size_to_list C /=.
by rewrite /loadW16 W2u8.pack2bE // initiE // nth_mkseq /#. 
qed.

lemma msubread_w4_w2 m w1 cur at buf len at1 buf1 len1 dlt:
 0 <= at-cur < 8 =>
 0 <= len < 8 =>
 at1 < cur+8 =>
 2 <= len%%4 =>
 at + dlt = min (cur+8) (at+len%/4*4+2) =>
 msubread m (u64bytes w1) cur at buf (len%/4*4) 0
          at1 buf1 len1 0 =>
 msubread m
    (u64bytes (w1 `|` (zeroextu64 (loadW16 m buf1) `<<<` 8*(at1-cur))))
    cur at buf (len%/2*2) 0
    (at+dlt) (buf+dlt) (len%/2*2-dlt) 0.
proof.
move=> Hcur Hlen Hat Hl Hdlt [Hspec1 H]; split; last first.
 by rewrite /srfnsh /srincr size_to_list /= /#.
have />: at1 = at + len%/4*4.
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= /#.
move: H => />; rewrite /srfnsh b2i0 /= => /addzI <-.
apply (srspec_w4_w2 (memread m buf len) (memread m buf (len %/ 4 * 4))) => //.
+ smt(size_memread).
+ by rewrite take_memread /#.
+ by rewrite take_memread /#.
rewrite drop_memread 1:/#.
by apply loadW16_memread; smt().
qed.

lemma loadW8_memread m buf len:
 1 <= len =>
 u8prefAt [loadW8 m buf] 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 1) => C; last first.
 by rewrite ifF /#.
rewrite ifT 1:/# ler_maxr //= C /=.
by rewrite /loadW8 nth_mkseq /#. 
qed.

lemma msubread_w2_w1 m w1 cur at buf len at1 buf1 len1 dlt:
 0 <= at-cur < 8 =>
 0 <= len < 8 =>
 at1 < cur+8 =>
 1 <= len%%2 =>
 at + dlt = min (cur+8) (at+len%/2*2+1) =>
 msubread m (u64bytes w1) cur at buf (len%/2*2) 0
          at1 buf1 len1 0 =>
 msubread m
    (u64bytes (w1 `|` (zeroextu64 (loadW8 m buf1) `<<<` 8*(at1-cur))))
    cur at buf len 0
    (at+dlt) (buf+dlt) (len-dlt) 0.
proof.
move=> Hcur Hlen Hat Hl Hdlt [Hspec1 H]; split; last first.
 by rewrite /srfnsh /srincr size_to_list /= /#.
have />: at1 = at + len%/2*2.
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= /#.
move: H => />; rewrite /srfnsh b2i0 /= => /addzI <-.
apply (srspec_w2_w1 (memread m buf len) (memread m buf (len %/ 2 * 2))) => //.
+ smt(size_memread).
+ by rewrite take_memread /#.
rewrite drop_memread 1:/#.
by apply loadW8_memread; smt().
qed.

lemma msubread_tb m w cur at buf len at1 buf1 len1 tb:
 0 <= len =>
 0 <= at - cur < 8 =>
 at + len < cur + 8 =>
 msubread m (u64bytes w) cur at buf len 0 at1 buf1 len1 0 =>
 msubread m (u64bytes (w `|` (of_int (tb %% 256) `<<` of_int (8 * (at1 - cur)))))
            cur at buf len tb (at1+b2i (tb<>0)) buf1 len1 0.
proof.
move=> Hlen Hat Hcur []H [#]; rewrite size_to_list b2i0 => Eat Ebuf Elen _.
split; last by rewrite size_to_list /#.
have ->: at1=at + len by smt().
apply (srspec_tb _ _ _ _ _ _ H); smt().
qed.

lemma msubread_u64_u128 m w cur at buf len tb at1 buf1 len1 tb1:
 0 <= at-cur < 16 =>
 cur+8 <= at =>
 msubread m (u64bytes w) (cur+8) at buf len tb
          at1 buf1 len1 tb1 =>
 msubread m (u128bytes (VPINSR_2u64 zero w one)) cur at buf len tb
          at1 buf1 len1 tb1.
proof.
move=> Hat Hcur [Hspec H]; split; last first.
 by move: H => []; rewrite !size_to_list => /> /#.
by apply srspec_u64_u128.
qed.

lemma msubread_u128_u256 m w cur at buf len tb at1 buf1 len1 tb1:
 0 <= at-cur < 32 =>
 cur+16 <= at =>
 msubread m (u128bytes w) (cur+16) at buf len tb
          at1 buf1 len1 tb1 =>
 msubread m (u256bytes (VINSERTI128  zero w one)) cur at buf len tb
          at1 buf1 len1 tb1.
proof.
move=> Hat Hcur [Hspec H]; split; last first.
 by move: H => []; rewrite !size_to_list => /> /#.
by apply srspec_u128_u256.
qed.


op msubwrite (m m2: global_mem_t) lw (buf len:int) buf2 len2 =
 m2 = stores m buf (take len lw)
 /\ buf2 = buf + min (size lw) (max 0 len)
 /\ len2 = len - min (size lw) (max 0 len).


lemma msubwrite_cat m m1 m2 lw1 lw2 buf len buf1 len1 buf2 len2:
 msubwrite m m1 lw1 buf len buf1 len1 =>
 msubwrite m1 m2 lw2 buf1 len1 buf2 len2 =>
 msubwrite m m2 (lw1++lw2) buf len buf2 len2.
proof.
move=> />; split; last smt(size_ge0 size_cat).
rewrite take_cat; case: (len < size lw1) => C.
 by rewrite (take_le0 (len -_)) 1:/# store0.
rewrite stores_cat; congr.
  by rewrite take_oversize 1:/#.
 smt(size_ge0).
congr; smt(size_ge0).
qed.

(* byte view of the partial (4/2/1-byte) stores of [__*_ilen_write_upto8] *)
lemma u32bytes_trunc (w: W64.t): u32bytes (truncateu32 w) = take 4 (u64bytes w).
proof.
have H: forall k, 0 <= k < 4 =>
  truncateu32 w \bits8 k = (w `&` W64.of_int (2^32-1)) \bits8 k.
 by move=> k Hk; rewrite -W2u32.zeroext_truncateu32_and bits8_zeroextu64_32 Hk.
by rewrite /u32bytes /u64bytes /= !H //; do! split; circuit.
qed.

lemma u16bytes_trunc (w: W64.t): u16bytes (truncateu16 w) = take 2 (u64bytes w).
proof.
have H: forall k, 0 <= k < 2 =>
  truncateu16 w \bits8 k = (w `&` W64.of_int (2^16-1)) \bits8 k.
 by move=> k Hk; rewrite -W4u16.zeroext_truncateu16_and bits8_zeroextu64_16 Hk.
by rewrite /u16bytes /u64bytes /= !H //; do! split; circuit.
qed.

lemma u8bytes_trunc (w: W64.t): [truncateu8 w] = take 1 (u64bytes w).
proof.
have ->: truncateu8 w = (w `&` W64.of_int (2^8-1)) \bits8 0.
 by rewrite -W8u8.zeroext_truncateu8_and bits8_zeroextu64_8.
by rewrite /u64bytes /=; circuit.
qed.

lemma trunc_unpckh (w: W128.t): truncateu64 (VPUNPCKH_2u64 w w) = w \bits64 1.
proof.
have ->: forall (x: W128.t), truncateu64 x = x \bits64 0 by move=> x; circuit.
by rewrite /VPUNPCKH_2u64 /interleave_gen /get_hi_2u64 /=.
qed.

lemma u128bytes_split (w: W128.t):
 u128bytes w = u64bytes (truncateu64 w) ++ u64bytes (truncateu64 (VPUNPCKH_2u64 w w)).
proof. by rewrite trunc_unpckh /u128bytes /u64bytes /=; do! split; circuit. qed.

lemma take8_u128bytes (w: W128.t): take 8 (u128bytes w) = u64bytes (truncateu64 w).
proof. by rewrite u128bytes_split take_size_cat // /u64bytes size_to_list. qed.

lemma u256bytes_split (w: W256.t):
 u256bytes w = u128bytes (truncateu128 w) ++ u128bytes (VEXTRACTI128 w (W8.of_int 1)).
proof. by rewrite /u256bytes /u128bytes /=; do! split; circuit. qed.

lemma take16_u256bytes (w: W256.t): take 16 (u256bytes w) = u128bytes (truncateu128 w).
proof. by rewrite u256bytes_split take_size_cat // /u128bytes size_to_list. qed.

lemma bits8_u64_shr8 (w: W64.t) k i:
 0 <= k => 0 <= i < 8 =>
 w `>>>` 8*k \bits8 i
 = if i + k < 8 then w \bits8 (i+k) else W8.zero.
proof.
move=> ??.
apply W8.ext_eq => j Hj.
rewrite bits8iE //=.
rewrite (:0 <= i * 8 + j < 64) 1:/# /=.
case: (i + k < 8) => C.
 by rewrite bits8iE 1:/# /#.
by rewrite zerowE get_out /#.
qed.

lemma u64bytes_shr8 (w: W64.t) k:
 0 <= k <= 8 =>
 u64bytes (w `>>` W8.of_int (8*k)) = drop k (u64bytes w) ++ u8zeros k.
proof.
move=> Hk; apply (eq_from_nth W8.zero).
 by rewrite size_cat size_drop 1:/# size_nseq /u64bytes size_to_list /#.
rewrite /u64bytes size_to_list => i Hi.
rewrite nth_to_list // /W64.(`>>`) of_uintK modz_small 1:/# bits8_u64_shr8 1,2:/#.
rewrite nth_cat size_drop 1:/# size_to_list.
case: (i + k < 8) => C.
 by rewrite ifT 1:/# nth_drop 1..2:/# nth_to_list /#.
by rewrite ifF 1:/# nth_nseq /#.
qed.

(* one piece of [__*_ilen_write_upto8]: [w] holds the not-yet-written bytes
   of [B] shifted down by [n]; its first [k] bytes are the next [k] bytes of
   [B], and shifting it by [k] keeps that shape for [n+k] *)
lemma upto8_take (B: W8.t list) (w: W64.t) n k:
 size B = 8 => 0 <= n => 0 <= k => n + k <= 8 =>
 u64bytes w = drop n B ++ u8zeros n =>
 take k (u64bytes w) = take k (drop n B).
proof.
move=> HB Hn Hk Hnk ->.
rewrite take_cat size_drop // HB ler_maxr 1:/#; case: (k < 8 - n) => C //.
by rewrite take_le0 1:/# cats0 take_oversize // size_drop // /#.
qed.

lemma upto8_shr (B: W8.t list) (w: W64.t) n k s:
 s = 8*k => size B = 8 => 0 <= n => 0 <= k => n + k <= 8 =>
 u64bytes w = drop n B ++ u8zeros n =>
 u64bytes (w `>>` W8.of_int s) = drop (n+k) B ++ u8zeros (n+k).
proof.
move=> -> HB Hn Hk Hnk Hw; rewrite u64bytes_shr8 1:/# Hw.
rewrite drop_cat size_drop // HB ler_maxr 1:/#.
case: (k < 8 - n) => C.
 by rewrite drop_drop // -catA cat_nseq // addzC.
have ->: k - (8 - n) = 0 by smt().
by rewrite drop0 drop_oversize 1:/# /= cat_nseq.
qed.

lemma stores_piece m b (B: W8.t list) n k:
 0 <= n <= size B => 0 <= k =>
 stores (stores m b (take n B)) (b + n) (take k (drop n B))
 = stores m b (take (n+k) B).
proof.
by move=> Hn Hk; rewrite takeD 1..2:/# stores_cat size_take' 1:/# ifT /#.
qed.

lemma mwrite_upto8_step (m _m: global_mem_t) _buf (B: W8.t list) n k (w: W64.t) piece:
 size B = 8 => 0 <= n => 0 <= k => n + k <= 8 =>
 m = stores _m _buf (take n B) =>
 u64bytes w = drop n B ++ u8zeros n =>
 piece = take k (u64bytes w) =>
 stores m (_buf + n) piece = stores _m _buf (take (n+k) B).
proof.
move=> HB Hn Hk Hnk -> Hw ->.
by rewrite (upto8_take B w n k) // stores_piece /#.
qed.


(******************************************************************************
 *        Read/write steps of the shared absorb and dump layers               *
 *  (Keccak1600_statebytes.ec instantiated with srspec / msubread / msubwrite; *
 *   the array counterparts are inside ReadWriteArray below)                   *
 ******************************************************************************)

(* A word read by `srspec` at offset `cur` is the `size lw`-byte window of the
   padded stream `u8zeros at ++ l ++ [tb]` starting at `cur` (generic in the
   word size: reused for the u64/u128/u256 reads). *)
lemma srspec_window lw cur at l len tb:
 srpre cur at l len tb =>
 srspec lw cur at l len tb =>
 bytes2state (u8zeros cur ++ lw)
 = bytes2state (take (cur + size lw) (u8zeros at ++ l ++ [W8.of_int tb])).
proof.
move=> Hpre Hspec; have [_ /u8prefAbsorbP Hp] := Hspec Hpre.
move: Hpre; rewrite /srpre => |> Hcur Hat Htb0 Htb1 Hor.
apply bytes2state_nthE => i Hi.
rewrite nth_cat size_nseq ler_maxr // nth_nseq_if cats1.
case: (i < cur + size lw) => C.
 rewrite nth_take; 1,2: smt(size_ge0).
 rewrite nth_rcons size_cat size_nseq ler_maxr // nth_cat size_nseq ler_maxr // nth_nseq_if Hp.
 by case: Hor => [Hle|[-> ->]]; smt(nth_out size_ge0).
rewrite nth_out; first smt(size_take size_ge0).
rewrite nth_out; first smt(size_take size_ge0).
by case: (i < cur).
qed.

(* A full in-data word read at the aligned position (any trailing byte). *)
lemma srspec_full lw cur l len tb:
 size lw <= size l =>
 u8prefAt lw 0 l =>
 srspec lw cur cur l len tb.
proof.
move=> Hsz Hw Hpre; split; first by apply srpre_next => //; apply size_ge0.
by rewrite (_: cur - cur = 0) 1:// u8prefAbsorbW.
qed.

(* One read step of an arbitrary word `lw` (srspec at offset `cur`): `stc` is the
   state after the first `cur` bytes; the word is XORed into it at `cur`. *)
lemma addstate_spec_step (l lw: W8.t list) cur st at tb stc c0 c at0 len0 tb0 cur1 c1 at1 len1 tb1:
 0 <= at => 0 <= tb < 256 =>
 0 <= cur <= at0 < cur + size lw =>
 cur1 = cur + size lw =>
 at1 = srat (size lw) cur at0 len0 tb0 =>
 c1 = c + srincr (size lw) cur at0 len0 =>
 len1 = srlen (size lw) cur at0 len0 =>
 tb1 = srtb (size lw) cur at0 len0 tb0 =>
 addstate_spec st at l tb cur c0 c stc at0 len0 tb0 =>
 srspec lw cur at0 (drop (size l - len0) l) len0 tb0 =>
 addstate_spec st at l tb cur1 c0 c1 (addstate_at stc cur lw) at1 len1 tb1.
proof.
move => |> Hat Htb0 Htb1 Hcur Hat0_1 Hat0_2; rewrite /addstate_spec addstate_atE // Hat /= => [#].
move => Hst0 ->> ->> ->> ->> Hspec.
split.
 rewrite Hst0 -addstateA; congr.
 rewrite (srspec_window _ _ _ _ _ _ _ Hspec); first by rewrite /srpre size_drop; smt(size_ge0).
 pose S := u8zeros at ++ l ++ [W8.of_int tb].
 have Hsz: size (take cur S) = cur.
  by rewrite size_take // /S !size_cat size_nseq /=; move: Hat0_1; rewrite /b2i; smt(size_ge0).
 rewrite (takeD S cur (size lw)) 1:/# 1:size_ge0 bytes2state_cat Hsz; congr.
 apply bytes2state_nthE => i Hi.
 have nthT: forall (s: W8.t list) n j, 0 <= n => nth W8.zero (take n s) j = if j < n then nth W8.zero s j else W8.zero.
  move=> s n j Hn; case: (j < n) => C; first by rewrite nth_take.
  by rewrite nth_out //; smt(size_take size_ge0).
 have nthD: forall k j, 0 <= k => nth W8.zero (drop k l) j = if 0 <= j then nth W8.zero l (k + j) else W8.zero.
  move=> k j Hk; case: (0 <= j) => C; first by rewrite nth_drop.
  by rewrite nth_neg 1:/#.
 move: Hat0_1 Hat0_2; rewrite /b2i => Hat0_1 Hat0_2.
 rewrite nthT 1:/# (nth_cat _ (u8zeros cur)) size_nseq (_: max 0 cur = cur) 1:/# nth_nseq_if.
 case: (i < cur) => C1 /=.
  by rewrite ifT 1:/# -catA (nth_cat _ (u8zeros _)) size_nseq ifT 1:/# nth_nseq_if /#.
 rewrite nthT 1:size_ge0 nth_drop 1,2:/# /S (_: cur + (i - cur) = i) 1:/#.
 case: (i < cur + size lw) => C2; last by rewrite ifF 1:/#.
 rewrite (_: (i - cur < size lw) = true) 1:/# /=.
 have Hk: 0 <= size l - (if at < cur then max 0 (at + size l - cur) else size l) by smt(size_ge0).
 rewrite !cats1 !nth_rcons !size_cat !size_nseq !size_drop // !nth_cat !size_nseq !nth_nseq_if !nthD //.
 smt(nth_out size_ge0).
do 3! (split; first by rewrite /srincr /srfnsh /b2i /=; smt(size_ge0)).
by rewrite /srincr /srfnsh /b2i /=; smt(size_ge0).
qed.

(* One aligned, full in-data word (any size): the shared step of every plain load. *)
lemma addstate_spec_fullword (l lw: W8.t list) sz st at tb stc c0 c at0 len0 tb0 sz1 c1 at1 len1:
 0 <= at => 0 <= tb < 256 => at <= sz => 0 < size lw <= len0 =>
 sz1 = sz + size lw => c1 = c + size lw => at1 = at0 + size lw => len1 = len0 - size lw =>
 addstate_spec st at l tb sz c0 c stc at0 len0 tb0 =>
 u8prefAt lw 0 (drop (size l - len0) l) =>
 addstate_spec st at l tb sz1 c0 c1 (addstate_at stc at0 lw) at1 len1 tb0.
proof.
move=> Hat Htb Hsz Hlw -> -> -> -> H Hw.
have Ea: at0 = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ H); smt().
move: H; rewrite Ea => H.
have [Hl0 Hl1] := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H.
apply (addstate_spec_step l lw sz st at tb stc c0 c sz len0 tb0) => //.
+ smt().
+ by rewrite /srincr /srfnsh /b2i /=; smt().
+ by rewrite /srincr; smt().
+ by rewrite /srincr; smt().
+ by rewrite /srfnsh; smt().
by apply srspec_full => //; rewrite size_drop; smt().
qed.

(* Finishing with the last (aligned, partial) word read at at0. *)
lemma addstate_spec_finish (l lw: W8.t list) n sz st at tb stc c0 c at0 len0 tb0 at1 c1:
 size l = n => 0 <= at => 0 <= tb < 256 => at <= sz => size lw = 8 => len0 < 8 =>
 (0 < len0 \/ tb0 <> 0) =>
 at1 = srat 8 at0 at0 len0 tb0 => c1 = c + srincr 8 at0 at0 len0 =>
 addstate_spec st at l tb sz c0 c stc at0 len0 tb0 =>
 srspec lw at0 at0 (drop (size l - len0) l) len0 tb0 =>
 addstate_at stc at0 lw = addstate_at st at (l ++ if tb <> 0 then [W8.of_int tb] else [])
 /\ at1 = at + n + b2i (tb <> 0) /\ c1 = c0 + n.
proof.
move=> <- Hat Htb Hsz Hlw Hl Hg -> -> H Hsr.
have Ea: at0 = sz by apply (addstate_spec_sz _ _ _ _ _ _ _ _ _ _ _ Hsz _ H).
move: H; rewrite -Ea => H.
have [Hl0 _] := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H.
have H': addstate_spec st at l tb (at0 + 8) c0 (c + srincr 8 at0 at0 len0) (addstate_at stc at0 lw)
          (srat 8 at0 at0 len0 tb0) (srlen 8 at0 at0 len0) (srtb 8 at0 at0 len0 tb0).
 by apply (addstate_spec_step l lw at0 st at tb stc c0 c at0 len0 tb0) => //; rewrite ?Hlw //; smt().
have [Hf1 Hf2]: srlen 8 at0 at0 len0 = 0 /\ srtb 8 at0 at0 len0 tb0 = 0 by rewrite /srincr /srfnsh /=; smt().
have [Hst Hat1] := addstate_spec_finished _ _ _ _ _ _ _ _ _ _ _ Hf1 Hf2 H'.
have Hc := addstate_spec_cur _ _ _ _ _ _ _ _ _ _ _ H'.
by rewrite Hst addstate_at_trail // Hat1 Hc Hf1.
qed.

(* MEMORY instance: the remaining data of the input is the memread at the cursor. *)
lemma addstate_spec_drop_memread st at mem b len tb sz c st' at' len' tb':
 0 <= len =>
 addstate_spec st at (memread mem b len) tb sz b c st' at' len' tb' =>
 drop (size (memread mem b len) - len') (memread mem b len) = memread mem c len'.
proof.
move=> Hlen H.
have Hc := addstate_spec_cur _ _ _ _ _ _ _ _ _ _ _ H.
have [Hl0 Hl1] := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H.
move: Hc Hl1; rewrite size_memread // => Hc Hl1.
by rewrite drop_memread 1:/# Hc; congr; ring.
qed.

(* MEMORY instance of the absorb input: the memread at _buf, read through memread. *)
lemma take_memread' mem b len k:
 0 <= k <= len => take k (memread mem b len) = memread mem b k.
proof. by move=> Hk; rewrite take_memread 1:/#; congr; smt(). qed.

lemma slice_memread mem b len k n:
 0 <= k => 0 <= n => k + n <= len =>
 take n (drop k (memread mem b len)) = memread mem (b + k) n.
proof. by move=> Hk Hn Hkn; rewrite drop_memread 1:/# take_memread //; congr; smt(). qed.

lemma drop_memread_cur mem b len c:
 b <= c <= b + len =>
 drop (c - b) (memread mem b len) = memread mem c (len - (c - b)).
proof. by move=> Hc; rewrite drop_memread 1:/#; congr; ring. qed.

(* One u64 msubread step (prefix and last word of the memory absorb). *)
lemma addstate_msubread_u64 mem w cur st at buf len tb stc at0 buf0 len0 tb0 cur1 at1 buf1 len1 tb1:
 0 <= at => 0 <= len => 0 <= tb < 256 =>
 0 <= cur <= at0 < cur+8 =>
 cur1 = cur + 8 =>
 addstate_spec st at (memread mem buf len) tb cur buf buf0 stc at0 len0 tb0 =>
 msubread mem (u64bytes w) cur at0 buf0 len0 tb0 at1 buf1 len1 tb1 =>
 addstate_spec st at (memread mem buf len) tb cur1 buf buf1 (addstate_at stc cur (u64bytes w)) at1 len1 tb1.
proof.
have Hs: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
move=> Hat Hlen Htb Hc Hc1 Hspec; rewrite /msubread => [#] Hsr Eat Ebuf Elen Etb.
apply (addstate_spec_step (memread mem buf len) (u64bytes w) cur st at tb stc buf buf0 at0 len0 tb0 cur1 buf1 at1 len1 tb1); rewrite ?Hs //.
by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ Hlen Hspec).
qed.

(* The runtime-length (`rlen`) read as one msubread step: the word read at
   the cursor, shifted to the in-word position `at - cur` (updstate first
   word and last partial word). *)
lemma srspec_rlen_u8prefAt w (l: W8.t list) len:
 size l = len => srspec (u64bytes w) 0 0 l len 0 => u8prefAt (u64bytes w) 0 l.
proof.
move=> Hs H; have [_ /u8prefAbsorbP P] := H _; first by rewrite /srpre; smt(size_ge0).
move=> i; rewrite P /= (: max 0 0 = 0) 1:// /=.
case: (i = size l) => C //.
by rewrite C; smt(nth_out size_ge0).
qed.

lemma msubread_rlen m t cur at buf len:
 0 <= cur <= at < cur + 8 => 0 <= len =>
 srspec (u64bytes t) 0 0 (memread m buf len) len 0 =>
 msubread m (u64bytes (t `<<<` 8 * (at - cur))) cur at buf len 0
   (at + min len (cur + 8 - at)) (buf + min len (cur + 8 - at)) (len - min len (cur + 8 - at)) 0.
proof.
move=> Hc Hl H.
have Hs: size (u64bytes (t `<<<` 8 * (at - cur))) = 8 by rewrite /u64bytes size_to_list.
rewrite /msubread Hs; split.
+ apply srspec_u64; first smt().
  by apply (srspec_rlen_u8prefAt _ _ len) => //; rewrite size_memread.
by rewrite /srincr /srfnsh /=; smt().
qed.

(* A dump that writes junk bytes past its data, later overwritten. *)
lemma stores_overwrite (m: global_mem_t) b (L Z L2: W8.t list):
 size Z <= size L2 =>
 stores (stores m b (L ++ Z)) (b + size L) L2 = stores m b (L ++ L2).
proof.
move=> H; have H1 := size_ge0 L; have H2 := size_ge0 Z.
apply mem_eq_ext => j; rewrite !get_storesE !size_cat.
case: (b + size L <= j < b + size L + size L2) => C.
+ rewrite ifT 1:/# nth_cat ifF 1:/#.
  by congr; ring.
case: (b <= j < b + (size L + size Z)) => C2.
+ by rewrite ifT 1:/# !nth_cat; smt().
by rewrite ifF 1:/#.
qed.

(* memory adapters *)
lemma msubwrite_dump0 (S: WArray200.t) m b len:
 0 <= len => msubwrite m m (sub S 0 0) b len b len.
proof.
move=> H; have ->: sub S 0 0 = [] by rewrite -size_eq0 size_sub.
by rewrite /msubwrite /= store0 /#.
qed.

lemma msubwrite_stores m b lw len b2 len2:
 b2 = b + size lw => len2 = len - size lw => size lw <= len =>
 msubwrite m (stores m b lw) lw b len b2 len2.
proof.
move=> -> -> H; rewrite /msubwrite take_oversize //=.
by rewrite ler_maxr; smt(size_ge0).
qed.

lemma msubwrite_storeW256 m b w len b2 len2:
 b2 = b + 32 => len2 = len - 32 => 32 <= len =>
 msubwrite m (storeW256 m b w) (u256bytes w) b len b2 len2.
proof.
by move=> -> -> H; rewrite storeW256E; apply msubwrite_stores; rewrite /u256bytes size_to_list.
qed.

lemma msubwrite_storeW128 m b w len b2 len2:
 b2 = b + 16 => len2 = len - 16 => 16 <= len =>
 msubwrite m (storeW128 m b w) (u128bytes w) b len b2 len2.
proof.
by move=> -> -> H; rewrite storeW128E; apply msubwrite_stores; rewrite /u128bytes size_to_list.
qed.

lemma msubwrite_storeW64 m b w len b2 len2:
 b2 = b + 8 => len2 = len - 8 => 8 <= len =>
 msubwrite m (storeW64 m b w) (u64bytes w) b len b2 len2.
proof.
by move=> -> -> H; rewrite storeW64E; apply msubwrite_stores; rewrite /u64bytes size_to_list.
qed.

lemma msubwrite_dump_step (S: WArray200.t) m0 m1 m2 b len k n lw b1 b2 k1 l1 l2:
 0 <= k => 0 <= n => k + n <= len => k1 = k + n => l1 = len - k => l2 = len - k1 =>
 msubwrite m0 m1 (sub S 0 k) b len b1 l1 =>
 lw = sub S k n =>
 msubwrite m1 m2 lw b1 l1 b2 l2 =>
 msubwrite m0 m2 (sub S 0 k1) b len b2 l2.
proof.
move=> Hk Hn Hkn -> -> -> H1 -> H2.
by rewrite (sub_cat S 0 k n) //=; exact (msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H1 H2).
qed.

lemma msubwrite_dump_last (S: WArray200.t) m0 m1 m2 b len k n lw b1 b2 l1 l2:
 0 <= k <= len => len <= k + n => l1 = len - k =>
 msubwrite m0 m1 (sub S 0 k) b len b1 l1 =>
 lw = sub S k n =>
 msubwrite m1 m2 lw b1 l1 b2 l2 =>
 m2 = stores m0 b (sub S 0 len) /\ b2 = b + len.
proof.
move=> Hk Hkn -> H1 -> H2.
have := msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H1 H2.
rewrite (_: sub S 0 k ++ sub S k n = sub S 0 (k+n)) 1:(sub_cat S 0 k n) 1..2:/# //=.
rewrite /msubwrite take_sub200 1:/# size_sub 1:/# => /> *.
smt().
qed.

lemma msubwrite_dump_fin (S: WArray200.t) m0 m1 b len b1:
 0 <= len =>
 msubwrite m0 m1 (sub S 0 len) b len b1 0 =>
 m1 = stores m0 b (sub S 0 len) /\ b1 = b + len.
proof. by move=> H; rewrite /msubwrite take_sub200 1:/# size_sub /#. qed.

lemma msubwrite_app m0 m1 b len L lw b1 l1 b2 l2:
 size L + size lw <= len => b2 = b1 + size lw => l2 = l1 - size lw =>
 msubwrite m0 m1 L b len b1 l1 =>
 msubwrite m0 (stores m1 b1 lw) (L ++ lw) b len b2 l2.
proof.
move=> Hsz -> -> H1; apply (msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H1).
move: H1; rewrite /msubwrite => /> *.
by apply msubwrite_stores; smt(size_ge0).
qed.

lemma msubwrite_squeeze_last r8 st m0 m1 b len b1 l1:
 0 < r8 <= 200 => 0 <= len => 0 < len %% r8 =>
 msubwrite m0 m1 (squeezeblocks r8 st (len %/ r8)) b len b1 l1 =>
 stores m1 b1 (sub (stbytes (st_i st (len %/ r8 + 1))) 0 (len %% r8))
 = stores m0 b (SQUEEZE1600 r8 len st).
proof.
move=> Hr Hl C; rewrite /msubwrite (SQUEEZE1600_split r8 len st) // C /= => [[-> [-> _]]].
have Hsz: size (squeezeblocks r8 st (len %/ r8)) = r8 * (len %/ r8).
 by rewrite size_squeezeblocks //; smt(divz_ge0).
have Hle: r8 * (len %/ r8) <= len by apply mul_divz_le => /#.
by rewrite take_oversize 1:/# stores_cat; congr; smt().
qed.

lemma msubwrite_squeeze_fin r8 st m0 m1 b len b1 l1:
 0 < r8 <= 200 => 0 <= len => !(0 < len %% r8) =>
 msubwrite m0 m1 (squeezeblocks r8 st (len %/ r8)) b len b1 l1 =>
 m1 = stores m0 b (SQUEEZE1600 r8 len st).
proof.
move=> Hr Hl C; rewrite /msubwrite (SQUEEZE1600_split r8 len st) // ifF // cats0 => [[-> _]].
have Hsz: size (squeezeblocks r8 st (len %/ r8)) = r8 * (len %/ r8).
 by rewrite size_squeezeblocks //; smt(divz_ge0).
have Hle: r8 * (len %/ r8) <= len by apply mul_divz_le => /#.
by rewrite take_oversize /#.
qed.

(* budgeted sub-writes of a prefix [sub S 0 k]: one step, a skipped step
   (budget exhausted), and changing or truncating the budget *)
lemma msubwrite_sub_step (S: WArray200.t) m0 m1 m2 b len k n k1 lw b1 l1 b2 l2:
 0 <= k => 0 <= n => k1 = k + n =>
 msubwrite m0 m1 (sub S 0 k) b len b1 l1 =>
 lw = sub S k n =>
 msubwrite m1 m2 lw b1 l1 b2 l2 =>
 msubwrite m0 m2 (sub S 0 k1) b len b2 l2.
proof.
move=> Hk Hn -> H1 -> H2.
by rewrite (sub_cat S 0 k n) //=; exact (msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H1 H2).
qed.

lemma msubwrite_sub_skip (S: WArray200.t) m0 m1 b len k k' b1 l1:
 0 <= k <= k' => !(0 < l1) =>
 msubwrite m0 m1 (sub S 0 k) b len b1 l1 =>
 msubwrite m0 m1 (sub S 0 k') b len b1 l1.
proof.
move=> Hk Hl; rewrite /msubwrite !size_sub 1,2:/# => [[-> [-> El]]].
case: (len <= 0) => C; first by rewrite !take_le0 //; smt().
have Hlk: len <= k by smt().
by rewrite !take_sub200 1,2:/#; smt().
qed.

lemma msubwrite_take_budget m0 m1 (lw: W8.t list) n b len b1 l1:
 0 <= n => len <= n =>
 msubwrite m0 m1 lw b len b1 l1 =>
 msubwrite m0 m1 (take n lw) b len b1 l1.
proof.
move=> Hn Hl; rewrite /msubwrite => [[-> [-> ->]]].
rewrite take_take' size_take'; smt(size_ge0).
qed.

lemma msubwrite_untake m0 m1 (lw: W8.t list) n b len b1 l1:
 0 <= n => len <= n =>
 msubwrite m0 m1 (take n lw) b len b1 l1 =>
 msubwrite m0 m1 lw b len b1 l1.
proof.
move=> Hn Hl; rewrite /msubwrite => [[-> [-> ->]]].
rewrite take_take' size_take'; smt(size_ge0).
qed.

lemma msubwrite_rebudget m0 m1 (lw: W8.t list) b len len' b1 l1 l1':
 size lw <= len => size lw <= len' => l1' = len' - size lw =>
 msubwrite m0 m1 lw b len b1 l1 =>
 msubwrite m0 m1 lw b len' b1 l1'.
proof.
move=> H1 H2 -> ; rewrite /msubwrite => [[-> [-> _]]].
by rewrite !take_oversize //; smt(size_ge0).
qed.

lemma msubwrite_dump_take (S: WArray200.t) m0 m1 b len k b1 l1:
 0 <= len <= k =>
 msubwrite m0 m1 (sub S 0 k) b len b1 l1 =>
 m1 = stores m0 b (sub S 0 len) /\ b1 = b + len.
proof.
move=> Hl; rewrite /msubwrite size_sub 1:/# => [[-> [-> _]]].
by rewrite take_sub200 1:/#; smt().
qed.

(******************************************************************************
 *                        CORRECTNESS theorems                                *
 ******************************************************************************)


(* lossless assertions *)

lemma m_ilen_read_upto8_at_ll: islossless M.__m_ilen_read_upto8_at
by islossless.

hoare m_ilen_read_upto8_at_h _buf _len _tb _cur _at:
 M.__m_ilen_read_upto8_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> msubread Glob.mem (u64bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3.
proof.
proc; simplify.
if => //.
 by auto => |> &m [[H|H]|H]; apply msubread0; rewrite size_to_list ?u64bytes0 // /#.
sp; if => //.
 (* 8 <= lEN *)
 wp; ecall (SHLQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 by apply msubread_u64.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ buf=_buf /\ cUR=_cur /\ tRAIL=_tb
         /\ lEN=_len /\ aT=_at==> _).
 by move => /> /#.
pose n0 := min (_cur + 8 - _at) (_len %/ 4 * 4).
seq 1: ( #[:2,3,5:6]pre
       /\ msubread Glob.mem (u64bytes w) _cur _at _buf (_len %/ 4 * 4) 0 aT buf (_len %/ 4 * 4-n0) 0
       /\ buf = _buf+n0 /\ lEN = _len - n0 /\ aT=_at+n0).
 if => //.
  (* 4 <= lEN  *)
  wp; ecall (SHLQ_h w (aT-cUR)); auto => |> *.
  split; first smt().
  move=> ??.
  rewrite /n0.
  have ->: _len %/ 4 * 4 = 4 by smt().
  have ->: (_buf + if _cur + 8 <= _at + 4 then _cur + 8 - _at else 4)
          = _buf + min (_cur+8-_at) 4 by smt().
  have ->: (if _cur + 8 <= _at + 4 then _cur + 8 else _at + 4)
          = _at + min (_cur+8-_at) 4 by smt().
  split; last smt().
  by apply msubread_u32.
 auto => |> ???????; split; last smt().
 rewrite /n0.
 have ->: (_len %/ 4 * 4 - min (_cur + 8 - _at) (_len %/ 4 * 4)) = _len %/ 4 * 4 by smt().
 by apply msubread0; rewrite u64bytes0 size_nseq /#.
pose n1 := min (_cur+8-_at) (_len %/ 2 * 2).
exlim aT => at1; exlim lEN => len1; exlim buf => buf1.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ cUR=_cur /\ tRAIL=_tb /\ buf=buf1 /\ lEN=len1 /\ aT=at1
         /\ msubread Glob.mem (u64bytes w) _cur _at _buf (_len%/4*4) 0
                     at1 buf1 (_len %/ 4 * 4 - n0) 0
         /\ buf1=_buf+n0 /\ len1=_len-n0 /\ at1=_at+n0
         ==> _).
 by move => />.
seq 1: ( #[/:7]pre
      /\ msubread Glob.mem (u64bytes w) _cur _at _buf (_len %/ 2 * 2) 0
                  aT buf (_len%/2*2-n1) 0
      /\ buf=_buf+n1 /\ lEN=_len-n1 /\ aT=_at+n1).
 if => //.
  (* 2 <= lEN *)
  wp; ecall (SHLQ_h t16 (aT-cUR)); auto => |> &m ????? H1??.
  split; first smt().
  move=> ??; split; last smt().
  rewrite -!addzA.
  have ->: (n0 + if _cur + 8 <= _at + (n0 + 2) then _cur + (8 - (_at + n0)) else 2)=n1 by smt().
  have ->: (if _cur + 8 <= _at + (n0 + 2) then _cur + 8 else _at + (n0 + 2))=_at+n1 by smt().
  rewrite (addzA _at).
  by apply (msubread_w4_w2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
 auto => |> &m ?????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En0: n0 = _cur+8-_at by smt().
 have En1: n1 = n0 by smt().
 split; last smt().
 rewrite En1 {3}En0.
 by apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
pose n2 := min (_cur+8-_at) _len.
exlim aT => at2; exlim lEN => len2; exlim buf => buf2.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ cUR=_cur /\ tRAIL=_tb /\ buf=buf2 /\ lEN=len2 /\ aT=at2
         /\ msubread Glob.mem (u64bytes w) _cur _at _buf (_len%/2*2) 0
                     at2 buf2 (_len%/2*2 - n1) 0
         /\ buf2=_buf+n1 /\ len2=_len-n1 /\ at2=_at+n1
         ==> _).
 by move => />.
seq 1: ( #[/:7]pre
       /\ msubread Glob.mem (u64bytes w) _cur _at _buf _len 0
                   aT buf (_len-n2) 0
       /\ buf=_buf+n2 /\ lEN=_len-n2 /\ aT=_at+n2).
 if => //.
  (* 1 <= lEN *)
  wp; ecall (SHLQ_h t8 (aT-cUR)); auto => |> ?????? H1??.
  split; first smt(). 
  move=> ??; split; last smt().
  rewrite -!addzA.
  have ->: n1+1=n2 by smt().
  rewrite (addzA _at).
  by apply (msubread_w2_w1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
 auto => |> &m ?????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En1: n1 = _cur+8-_at by smt().
 have En2: n2 = n1 by smt().
 split; last smt().
 rewrite En2 {3}En1.
 by apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
if => //.
 auto => |> &m ?????H??.
 have ->: 1 = b2i (_tb<>0) by smt().
 by apply msubread_tb; smt().
auto => |> &m ?????H; rewrite negb_and => [[C|C]]; last smt().
have {3}->: n2 =  _cur + 8 - _at by smt().
apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
qed.

phoare m_ilen_read_upto8_at_ph _buf _len _tb _cur _at:
 [
 M.__m_ilen_read_upto8_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> msubread Glob.mem (u64bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3
 ] = 1%r. 
proof.
by conseq m_ilen_read_upto8_at_ll (m_ilen_read_upto8_at_h _buf _len _tb _cur _at).
qed.

lemma m_ilen_read_upto16_at_ll: islossless M.__m_ilen_read_upto16_at
by islossless.

lemma m_ilen_read_upto16_at_h _buf _len _tb _cur _at:
 hoare [
 M.__m_ilen_read_upto16_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> msubread Glob.mem (u128bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3
 ].
proof.
proc; simplify.
if => //.
 auto => |> &m H.
 apply msubread0.
  by rewrite size_to_list ?u128bytes0 // /#.
 by rewrite size_to_list /#.
(* 16 <= lEN *)
if => //.
 wp; ecall (SHLDQ_h w (aT-cUR)); auto => |> &m *.
 split; first smt().
 move=> ??.
 by apply msubread_u128.
(* lEN < 16 *)
if => //.
 (* CUR+8 <= AT *)
 wp; ecall(m_ilen_read_upto8_at_h buf lEN tRAIL (cUR+8) aT); auto => |>.
 rewrite !negb_or negb_and => |> &m ???????? [dlt0 len0 tb0 at0 w0] /= H.
 by apply msubread_u64_u128; smt().
wp; ecall(m_ilen_read_upto8_at_h buf lEN tRAIL (cUR+8) aT).
wp; ecall(m_ilen_read_upto8_at_h buf lEN tRAIL cUR aT).
auto => |>; rewrite !negb_or negb_and => |> &m?????????[]dlt0 len0 tb0 at0 w0 |> H0.
move=> []dlt1 len1 tb1 at1  w2 /= H1.
rewrite -u64bytes_cat.
by apply (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).
qed.

lemma m_ilen_read_upto16_at_ph _buf _len _tb _cur _at:
 phoare [
 M.__m_ilen_read_upto16_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
   /\ 0 <= _len
 ==> msubread Glob.mem (u128bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3
 ] = 1%r.
proof.
by conseq m_ilen_read_upto16_at_ll (m_ilen_read_upto16_at_h  _buf _len _tb _cur _at).
qed.

lemma m_ilen_read_upto32_at_ll: islossless M.__m_ilen_read_upto32_at
by islossless.

hoare m_ilen_read_upto32_at_h _buf _len _tb _cur _at:
 M.__m_ilen_read_upto32_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> msubread Glob.mem (u256bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3.
proof.
proc; simplify.
if => //.
 auto => |> &m H. 
 apply msubread0.
  by rewrite size_to_list ?u256bytes0 // /#.
 by rewrite size_to_list /#.
(* 32 <= lEN *)
sp; if => //.
 auto => |> &m ??.
 by apply msubread_u256.
(* lEN < 16 *)
if => //.
 (* CUR+16 <= AT *)
 wp; ecall(m_ilen_read_upto16_at_h buf lEN tRAIL (cUR+16) aT); auto => |>.
 rewrite !negb_or negb_and => |> ???????? [dlt0 len0 tb0 at0 w0] /= H.
 by apply msubread_u128_u256; smt().
wp; ecall(m_ilen_read_upto16_at_h buf lEN tRAIL (cUR+16) aT).
wp; ecall(m_ilen_read_upto16_at_h buf lEN tRAIL cUR aT).
auto => |> &m.
rewrite !negb_or negb_and => ???[]dlt0 len0 tb0 at0 w0 |> H0 []dlt1 len1 tb1 at1 w1 /= H1.
rewrite -u128bytes_cat.
by apply (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).
qed.

phoare m_ilen_read_upto32_at_ph _buf _len _tb _cur _at:
 [
 M.__m_ilen_read_upto32_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
   /\ 0 <= _len
 ==> msubread Glob.mem (u256bytes res.`5) _cur _at _buf _len _tb
              res.`4 res.`1 res.`2 res.`3
 ] = 1%r. 
proof.
by conseq m_ilen_read_upto32_at_ll (m_ilen_read_upto32_at_h  _buf _len _tb _cur _at).
qed.

lemma m_ilen_read_bcast_upto8_at_ll: islossless M.__m_ilen_read_bcast_upto8_at
by islossless.

(*
lemma trunc_zext_u64_u128 w:
 truncateu64 (W2u64.zeroextu128 w) = w.
proof. by circuit. qed.
*)

lemma trunc_VMOV_64 w:
 truncateu64 (VMOV_64 w) = w.
proof. by circuit. qed.

equiv m_ilen_read_bcast_upto8_at_eq:
 M.__m_ilen_read_bcast_upto8_at
 ~ M.__m_ilen_read_upto8_at
 : ={arg, Glob.mem}
 ==> (res.`1,res.`2,res.`3,res.`4,res.`5){1}
     = (res.`1,res.`2,res.`3,res.`4,VPBROADCAST_4u64 (truncateu64 (VMOV_64 res.`5))){2}.
proof.
proc; simplify.
if => //=.
 auto => />.
 by move=> *; clear; circuit.
sp; if => //=.
 inline*; auto => /> &m *; split.
  move=> *.
  rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
  by rewrite /W64.(`<<`) trunc_VMOV_64 of_uintK modz_small 1:/# of_uintK modz_small /#.
 move=> *.
 rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
 by rewrite /W64.(`<<`) trunc_VMOV_64 1:/# of_uintK modz_small /#.
inline *.
rcondf {1} 6; first by auto.
rcondf {1} 6; first by auto.
wp 10 4.
conseq (: ={Glob.mem,buf,aT,cUR,lEN,tRAIL} ==> ={w,aT,cUR,buf,lEN,tRAIL}) => //.
by sim.
qed.

(* reads leave the memory unchanged *)
hoare m_ilen_read_upto8_at_mem _m:
 M.__m_ilen_read_upto8_at : Glob.mem = _m ==> Glob.mem = _m.
proof. by proc; inline *; auto. qed.

hoare m_ilen_read_bcast_upto8_at_mem _m:
 M.__m_ilen_read_bcast_upto8_at : Glob.mem = _m ==> Glob.mem = _m.
proof. by proc; inline *; auto. qed.

(* the broadcast read: the same word on the four lanes *)
hoare m_ilen_read_bcast_upto8_at_h _buf _len _tb _cur _at:
 M.__m_ilen_read_bcast_upto8_at
 : buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> exists w, res.`5 = VPBROADCAST_4u64 w
     /\ msubread Glob.mem (u64bytes w) _cur _at _buf _len _tb res.`4 res.`1 res.`2 res.`3.
proof.
exlim Glob.mem => _m.
conseq (m_ilen_read_bcast_upto8_at_mem _m)
       (_: Glob.mem = _m /\ buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
           ==> exists w, res.`5 = VPBROADCAST_4u64 w
               /\ msubread _m (u64bytes w) _cur _at _buf _len _tb res.`4 res.`1 res.`2 res.`3) => //.
conseq m_ilen_read_bcast_upto8_at_eq
       (_: Glob.mem = _m /\ buf=_buf /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
           ==> msubread _m (u64bytes res.`5) _cur _at _buf _len _tb res.`4 res.`1 res.`2 res.`3).
+ by move=> &1 />; exists Glob.mem{1} arg{1}.
+ move=> &1 &2 /= [E1 [E2 [E3 [E4 E5]]]] H.
  by exists (truncateu64 (VMOV_64 res{2}.`5)); rewrite E1 E2 E3 E4 E5 trunc_VMOV_64.
by conseq (m_ilen_read_upto8_at_mem _m) (m_ilen_read_upto8_at_h _buf _len _tb _cur _at).
qed.

lemma m_rlen_read_upto8_ll: islossless M.__m_rlen_read_upto8
by islossless.

(* The runtime-length readers/writers (`__*_rlen_*`, used by the updstate code)
   are the inline-length ones with the length bits tested at runtime: their
   contracts follow from the `ilen` contracts through an `equiv`. *)

lemma shl8_mulE (w: W64.t) k:
 0 <= k < 64 => w `<<` W8.of_int k = w * W64.of_int (2^k).
proof.
move=> Hk.
by rewrite W64.shl_shlw 1:// -{1}(W64.to_uintK w) W64.shlMP 1:/# -W64.of_intM W64.to_uintK.
qed.

lemma test64_zf l b:
 0 <= l < 8 => b = 1 \/ b = 2 \/ b = 4 =>
 (TEST_64 (W64.of_int l) (W64.of_int b)).`5 = (l %/ b %% 2 = 0).
proof.
move=> Hl Hb; have : l \in iota_ 0 8 by rewrite mem_iota /#.
rewrite -iotaredE /= /TEST_64 /TEST_XX /rflags_of_bwop /ZF_of /=.
by case: Hb => [->|[->|->]]; do 7! (case => [-> /=|]; first by circuit); move=> -> /=; circuit.
qed.

equiv m_rlen_ilen_read_eq:
 M.__m_rlen_read_upto8 ~ M.__m_ilen_read_upto8_at
 : ={Glob.mem} /\ buf{1} = buf{2} /\ len{1} = lEN{2}
   /\ tRAIL{2} = 0 /\ cUR{2} = 0 /\ aT{2} = 0 /\ 0 <= len{1}
 ==> ={Glob.mem} /\ res.`1{1} = res.`1{2} /\ res.`2{1} = res.`5{2}.
proof.
proc; inline *; case: (8 <= len{1}).
+ rcondt{1} 1; first by auto.
  rcondf{2} 1; first by auto => /#.
  rcondt{2} 1; first by auto => /#.
  rcondf{2} 4; first by auto.
  by auto => />.
rcondf{1} 1; first by auto.
wp; skip => /> &2 H0 H1.
have T1 : (TEST_64 (W64.of_int lEN{2}) W64.one).`5 = (lEN{2} %/ 1 %% 2 = 0).
+ by rewrite -(test64_zf lEN{2} 1) /#.
rewrite T1 (test64_zf lEN{2} 4) 1,2:/# (test64_zf lEN{2} 2) 1,2:/#.
have : lEN{2} \in iota_ 0 8 by rewrite mem_iota /#.
rewrite -iotaredE /=.
case => [->|]; first by move=> /=; circuit.
move: (loadW32 Glob.mem{2} buf{2}) (loadW16 Glob.mem{2} buf{2}) (loadW16 Glob.mem{2} (buf{2} + 4))
      (loadW8 Glob.mem{2} buf{2}) (loadW8 Glob.mem{2} (buf{2} + 2)) (loadW8 Glob.mem{2} (buf{2} + 4))
      (loadW8 Glob.mem{2} (buf{2} + 6)) => a32 b0 b4 c0 c2 c4 c6.
have M16 : W8.of_int 16 `&` W8.of_int 63 = W8.of_int 16 by circuit.
have M32 : W8.of_int 32 `&` W8.of_int 63 = W8.of_int 32 by circuit.
have M48 : W8.of_int 48 `&` W8.of_int 63 = W8.of_int 48 by circuit.
rewrite M16 M32 M48; clear M16 M32 M48 T1 H0 H1.
rewrite !(shl8_mulE _ 16) // !(shl8_mulE _ 32) // !(shl8_mulE _ 48) // /=.
by do 6! (case => [->|] /=; first by circuit); move=> -> /=; circuit.
qed.

hoare m_rlen_read_upto8_h _buf _len:
 M.__m_rlen_read_upto8
 : buf=_buf /\ len=_len /\ 0 <= _len
 ==> srspec (u64bytes res.`2) 0 0 (memread Glob.mem _buf _len) _len 0
     /\ res.`1 = _buf + min 8 (max 0 _len).
proof.
conseq m_rlen_ilen_read_eq (m_ilen_read_upto8_at_h _buf _len 0 0 0).
+ by move=> &1 [#] <- <- H0; exists Glob.mem{1} (buf{1}, len{1}, 0, 0, 0).
move=> &1 &2 [#] -> -> ->; rewrite /msubread => [#] Hs _ -> _ _.
by split; [exact Hs | rewrite size_to_list /srincr /#].
qed.

phoare m_rlen_read_upto8_ph _buf _len:
 [ M.__m_rlen_read_upto8
 : buf=_buf /\ len=_len /\ 0 <= _len
 ==> srspec (u64bytes res.`2) 0 0 (memread Glob.mem _buf _len) _len 0
     /\ res.`1 = _buf + min 8 (max 0 _len)
 ] = 1%r.
proof. by conseq m_rlen_read_upto8_ll (m_rlen_read_upto8_h _buf _len). qed.

lemma m_ilen_write_upto8_ll: islossless M.__m_ilen_write_upto8
by islossless.

hoare m_ilen_write_upto8_h (_m: global_mem_t) _buf _len _w:
 M.__m_ilen_write_upto8
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u64bytes _w) _buf _len res.`1 res.`2.
proof.
proc => /=.
if => //=; last first.
 auto => /> Hlen; rewrite ler_maxl 1:/# ler_minr; first smt(size_ge0).
 by rewrite take_le0 1:/# store0.
if => //=.
 auto => /> Hlen0 Hlen1; rewrite take_oversize size_to_list 1:/#; split; last smt().
 by rewrite storeW64E.
(* 0 < lEN < 8: pieces of 4, 2 and 1 bytes; [_len - lEN] bytes written *)
seq 1: (0 <= lEN < 4 /\ lEN <= _len < 8 /\ buf = _buf + (_len - lEN)
        /\ Glob.mem = stores _m _buf (take (_len - lEN) (u64bytes _w))
        /\ u64bytes w = drop (_len - lEN) (u64bytes _w) ++ u8zeros (_len - lEN)).
 if => //.
  auto => /> Hlen0 Hlen1 Hlen4.
  rewrite storeW32E -/(u32bytes (truncateu32 _w)) u32bytes_trunc.
  rewrite (mwrite_upto8_step _m _m _buf (u64bytes _w) 0 4 _w) ?size_to_list ?take0 ?store0 ?drop0 ?nseq0 ?cats0 //=.
  rewrite (upto8_shr (u64bytes _w) _w 0 4 32) ?size_to_list ?drop0 ?nseq0 ?cats0 //=.
  smt().
 by auto => /> *; rewrite take0 store0 drop0 nseq0 cats0 /#.
seq 1: (0 <= lEN < 2 /\ lEN <= _len < 8 /\ buf = _buf + (_len - lEN)
        /\ Glob.mem = stores _m _buf (take (_len - lEN) (u64bytes _w))
        /\ u64bytes w = drop (_len - lEN) (u64bytes _w) ++ u8zeros (_len - lEN)).
 if => //.
  auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
  rewrite storeW16E -/(u16bytes (truncateu16 w{m})) u16bytes_trunc.
  rewrite (mwrite_upto8_step _ _m _buf (u64bytes _w) (_len - lEN{m}) 2 w{m}) ?size_to_list // 1..2:/#.
  rewrite (upto8_shr (u64bytes _w) w{m} (_len - lEN{m}) 2 16) ?size_to_list // 1..2:/#.
  smt().
 by auto => /> /#.
if => //.
 auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
 rewrite -stores_singl u8bytes_trunc.
 rewrite (mwrite_upto8_step _ _m _buf (u64bytes _w) (_len - lEN{m}) 1 w{m}) ?size_to_list // 1..2:/#.
 by rewrite (_: _len - lEN{m} + 1 = _len) 1:/# /#.
auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
have ->: lEN{m} = 0 by smt().
by rewrite size_to_list ler_maxr 1:/# ler_minr /#.
qed.

phoare m_ilen_write_upto8_ph (_m: global_mem_t) _buf _len _w:
 [ M.__m_ilen_write_upto8
 :  _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u64bytes _w) _buf _len res.`1 res.`2
 ] = 1%r.
proof. by conseq m_ilen_write_upto8_ll (m_ilen_write_upto8_h _m _buf _len _w). qed.

lemma m_ilen_write_upto16_ll: islossless M.__m_ilen_write_upto16
by islossless.

hoare m_ilen_write_upto16_h (_m: global_mem_t) _buf _len _w:
 M.__m_ilen_write_upto16
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u128bytes _w) _buf _len res.`1 res.`2.
proof.
proc => /=.
if => //=; last first.
 by auto => /> Hlen; rewrite /msubwrite take_le0 1:/# store0; smt(size_ge0).
if => //=.
 by auto => /> H0 H16; apply msubwrite_storeW128 => /#.
(* 0 < lEN < 16: an optional low u64, then the rest via __m_ilen_write_upto8 *)
seq 1: (0 < _len < 16
        /\ ((8 <= _len /\ msubwrite _m Glob.mem (take 8 (u128bytes _w)) _buf _len buf lEN
             /\ w = VPUNPCKH_2u64 _w _w)
         \/ (_len < 8 /\ Glob.mem = _m /\ buf = _buf /\ lEN = _len /\ w = _w))).
 if => //.
  auto => /> H0 H16 H8; split; first smt().
  have Hm: msubwrite _m (storeW64 _m _buf (MOVV_64 (truncateu64 _w))) (take 8 (u128bytes _w))
             _buf _len (_buf + 8) (_len - 8).
   by rewrite take8_u128bytes /MOVV_64; apply msubwrite_storeW64 => /#.
  by left.
 by auto => /> /#.
ecall (m_ilen_write_upto8_h Glob.mem buf lEN t64).
auto => |> &m H0 H16 Hc [b2 l2] m2 /= H2.
case: Hc => [[H8 [H Hw]]|[H8 [Hm [Hb [Hl Hw]]]]].
 move: H2; rewrite Hw /MOVV_64 => H2.
 have := msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H H2.
 by rewrite take8_u128bytes -u128bytes_split.
move: H2; rewrite Hm Hb Hl Hw /MOVV_64 -take8_u128bytes => H2.
by apply (msubwrite_untake _ _ _ 8 _ _ _ _ _ _ H2) => /#.
qed.

phoare m_ilen_write_upto16_ph (_m: global_mem_t) _buf _len _w:
 [ M.__m_ilen_write_upto16
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u128bytes _w) _buf _len res.`1 res.`2
 ] = 1%r.
proof. by conseq m_ilen_write_upto16_ll (m_ilen_write_upto16_h _m _buf _len _w). qed.

lemma m_ilen_write_upto32_ll: islossless M.__m_ilen_write_upto32
by islossless.

hoare m_ilen_write_upto32_h (_m: global_mem_t) _buf _len _w:
 M.__m_ilen_write_upto32
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u256bytes _w) _buf _len res.`1 res.`2.
proof.
proc => /=.
if => //=; last first.
 by auto => /> Hlen; rewrite /msubwrite take_le0 1:/# store0; smt(size_ge0).
if => //=.
 by auto => /> H0 H32; apply msubwrite_storeW256 => /#.
(* 0 < lEN < 32: an optional low u128, then the rest via __m_ilen_write_upto16 *)
seq 2: (0 < _len < 32
        /\ ((16 <= _len /\ msubwrite _m Glob.mem (take 16 (u256bytes _w)) _buf _len buf lEN
             /\ t128 = VEXTRACTI128 _w (W8.of_int 1))
         \/ (_len < 16 /\ Glob.mem = _m /\ buf = _buf /\ lEN = _len /\ t128 = truncateu128 _w))).
 seq 1: (#pre /\ t128 = truncateu128 w); first by auto.
 if => //.
  auto => /> H0 H32 H16; split; first smt().
  have Hm: msubwrite _m (storeW128 _m _buf (truncateu128 _w)) (take 16 (u256bytes _w))
             _buf _len (_buf + 16) (_len - 16).
   by rewrite take16_u256bytes; apply msubwrite_storeW128 => /#.
  by left.
 by auto => /> /#.
ecall (m_ilen_write_upto16_h Glob.mem buf lEN t128).
auto => |> &m H0 H32 Hc [b2 l2] m2 /= H2.
case: Hc => [[H16 [H Ht]]|[H16 [Hm [Hb [Hl Ht]]]]].
 move: H2; rewrite Ht => H2.
 have := msubwrite_cat _ _ _ _ _ _ _ _ _ _ _ H H2.
 by rewrite take16_u256bytes -u256bytes_split.
move: H2; rewrite Hm Hb Hl Ht -take16_u256bytes => H2.
by apply (msubwrite_untake _ _ _ 16 _ _ _ _ _ _ H2) => /#.
qed.

phoare m_ilen_write_upto32_ph (_m: global_mem_t) _buf _len _w:
 [ M.__m_ilen_write_upto32
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u256bytes _w) _buf _len res.`1 res.`2
 ] = 1%r.
proof. by conseq m_ilen_write_upto32_ll (m_ilen_write_upto32_h _m _buf _len _w). qed.

lemma m_rlen_write_upto8_ll: islossless M.__m_rlen_write_upto8
by islossless.

equiv m_rlen_ilen_write_eq:
 M.__m_rlen_write_upto8 ~ M.__m_ilen_write_upto8
 : ={Glob.mem} /\ buf{1} = buf{2} /\ len{1} = lEN{2} /\ data{1} = w{2} /\ 0 <= len{1}
 ==> ={Glob.mem} /\ res{1} = res{2}.`1.
proof.
proc; case: (8 <= len{1}).
+ by rcondt{1} 1; [auto | rcondt{2} 1; [auto => /# | rcondt{2} 1; [auto => /# | auto => />]]].
rcondf{1} 1; first by auto.
seq 1 0 : (={Glob.mem} /\ buf{1} = buf{2} /\ len{1} = lEN{2} /\ data{1} = w{2}
           /\ 0 <= len{1} < 8 /\ zf{1} = (len{1} %/ 4 %% 2 = 0)).
+ by auto => /> &2 H0 H1; rewrite (test64_zf lEN{2} 4) /#.
case: (len{1} = 0).
+ rcondf{2} 1; first by auto => /#.
  rcondf{1} 1; first by auto => /#.
  rcondf{1} 2; first by auto => /> &2 *; rewrite (test64_zf 0 2).
  rcondf{1} 3; first by auto => /> &2 *; have /= := test64_zf 0 1.
  by auto.
rcondt{2} 1; first by auto => /#.
rcondf{2} 1; first by auto => /#.
seq 1 1 : (={Glob.mem} /\ buf{1} = buf{2} /\ lEN{2} = len{1} %% 4
           /\ data{1} = w{2} /\ 0 < len{1} < 8).
+ by if; [move=> /> /# | auto => /> /# | auto => /> /#].
seq 2 1 : (={Glob.mem} /\ buf{1} = buf{2} /\ lEN{2} = len{1} %% 2
           /\ data{1} = w{2} /\ 0 < len{1} < 8).
+ seq 1 0 : (#pre /\ zf{1} = (len{1} %/ 2 %% 2 = 0)).
  + by auto => /> &1 &2 *; rewrite (test64_zf len{1} 2) /#.
  by if; [move=> /> /# | auto => /> /# | auto => /> /#].
seq 1 0 : (#pre /\ zf{1} = (len{1} %/ 1 %% 2 = 0)).
+ by auto => /> &1 &2 *; rewrite -(test64_zf len{1} 1) /#.
by if; [move=> /> /# | auto => /> /# | auto => /> /#].
qed.

hoare m_rlen_write_upto8_h _m _buf _w _len:
 M.__m_rlen_write_upto8
 : _m=Glob.mem /\ buf=_buf /\ len=_len /\ data = _w /\ 0 <= _len
 ==> Glob.mem = stores _m _buf (take _len (u64bytes _w))
     /\ res = _buf + min 8 (max 0 _len).
proof.
conseq m_rlen_ilen_write_eq (m_ilen_write_upto8_h _m _buf _len _w).
+ by move=> &1 [#] -> -> -> -> H; exists Glob.mem{1} (_buf, _len, _w).
by move=> &1 &2 [#] -> ->; rewrite /msubwrite size_to_list /= => [#] -> -> _.
qed.

phoare m_rlen_write_upto8_ph _m _buf _w _len:
 [ M.__m_rlen_write_upto8
 : _m=Glob.mem /\ buf=_buf /\ len=_len /\ data = _w /\ 0 <= _len
 ==> Glob.mem = stores _m _buf (take _len (u64bytes _w))
     /\ res = _buf + min 8 (max 0 _len)
 ] = 1%r.
proof. by conseq m_rlen_write_upto8_ll (m_rlen_write_upto8_h _m _buf _w _len). qed.


abstract theory ReadWriteArray.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

(* Some auxiliary lemmata for [sub] *)

lemma sub0 (buf: W8.t A.t) off:
 sub buf off 0 = [].
proof. by rewrite -size_eq0 size_sub /#. qed.

lemma sub0' (buf: W8.t A.t) off len:
 len <= 0 =>
 sub buf off len = [].
proof. by move=> ?; rewrite /sub mkseq0_le. qed.

lemma sub_split len' (buf: W8.t A.t) off len:
 0 <= len' <= len =>
 sub buf off len = sub buf off len' ++ sub buf (off+len') (len-len').
proof.
move=> Hlen.
rewrite (:len=len'+(len-len')) 1:/# /sub mkseq_add 1..2:/#; congr.
rewrite (:len' + (len - len') - len'=len-len') 1:/#.
by apply eq_mkseq => i /= /#.
qed.

lemma size_sub' ['a] (buf:'a A.t) k len:
 size (sub buf k len) = max 0 len.
proof.
case: (0<=len) => H.
 by rewrite size_sub /#.
by rewrite /sub mkseq0_le /#.
qed.

lemma take_sub n (a:W8.t A.t) k len:
 take n (sub a k len) = sub a k (min n len).
proof.
case: (n < 0) => ?.
 by rewrite take_le0 1:/# /sub mkseq0_le /#. 
case: (len < n) => ?.
 by rewrite take_oversize ?size_sub' /#.
by rewrite take_mkseq // /#.
qed.

lemma drop_sub n (buf: W8.t A.t) off len:
 drop n (sub buf off len)
 = sub buf (off+max 0 n) (len-max 0 n).
proof.
apply (eq_from_nth W8.zero).
rewrite size_drop' /srincr !size_sub' 1:/#.
rewrite size_drop' size_sub' => i Hi.
rewrite nth_sub 1:/#.
case: (n < 0) => ?.
 by rewrite drop_le0 1:/# nth_sub /#.
rewrite nth_drop; 1..2: smt(size_ge0).
by rewrite nth_sub; smt(size_ge0).
qed.


(***************************************
      ARRAY reads/writes
****************************************)


op asubread (buf:W8.t A.t) off lw (cur at dlt len tb at2 dlt2 len2 tb2: int) =
 (0<=off /\ 0<=dlt /\ off+dlt+len <= _ASIZE => srspec lw cur at (sub buf (off+dlt) len) len tb)
 /\ at2 = srat (size lw) cur at len tb
 /\ dlt2 = dlt + srincr (size lw) cur at len
 /\ len2 = len - srincr (size lw) cur at len
 /\ tb2 = srtb (size lw) cur at len tb.

lemma asubread0 (buf:W8.t A.t) off lw (cur at dlt len tb:int):
 lw = u8zeros (size lw) =>
 len < 0 \/ at < cur \/ cur + size lw <= at \/ len = 0 /\ tb = 0 =>
 asubread buf off lw cur at dlt len tb at dlt len tb.
proof.
move=> -> [H|[H|[|[->->]]]]; rewrite /asubread size_nseq.
+ split; last smt().
  by move=> ?; apply absurd => _; rewrite /srpre size_sub' /#.
+ split; last smt().
  by move=> Hppre Hpre; rewrite size_nseq; smt(nth_u8zeros).
+ rewrite ler_maxr; first smt(size_ge0).
  move=> H; split; last smt().
  move=> Hppre Hpre; split.
   by rewrite srpre_next; smt(size_ge0).
  rewrite u8prefAbsorbP => i; rewrite size_nseq size_sub' nth_u8zeros.
  case: (0 <= i < size lw) => C; last smt().
  by rewrite nth_out /#.
split; last smt().
by move=> ??; rewrite sub0 size_nseq; smt(size_ge0 nth_u8zeros).
qed.

lemma asubread_cat (buf:W8.t A.t) off lw1 lw2 (cur at dlt len tb:int) at1 dlt1 len1 tb1 at2 dlt2 len2 tb2:
 asubread buf off lw1 cur at dlt len tb at1 dlt1 len1 tb1 =>
 asubread buf off lw2 (cur+size lw1) at1 dlt1 len1 tb1 at2 dlt2 len2 tb2 =>
 asubread buf off (lw1++lw2) cur at dlt len tb at2 dlt2 len2 tb2.
proof.
rewrite /asubread => /= [#]H1 Hat1 Hdlt1 Hlen1 Htb1.
move => /= [#]H2 Hat2 Hdlt2 Hlen2 Htb2.
split; last first.
 by rewrite size_cat srat_add; smt(size_ge0).
move => Hppre Hpre; move:(Hpre).
have Hl: sub buf (off + dlt1) len1 = srl (size lw1) cur at (sub buf (off + dlt) len).
 smt(size_ge0 drop_sub). 
by apply (srspec_cat lw1 lw2 cur at (sub buf (off + dlt) len) len tb) => // /#.
qed.

lemma get32_bytes (buf: W8.t A.t) off k:
 0 <= off =>
 off + 4 <= _ASIZE =>
 get32_direct (WA.init8 ("_.[_]" buf)) off \bits8 k
 = (sub buf off 4).[k].
proof.
move=> Ho1 Ho2; rewrite get32E.
have->: W4u8.Pack.init (fun j => (WA.init8 ("_.[_]" buf)).[off+j])
        = W4u8.Pack.of_list (sub buf off 4).
 apply W4u8.Pack.ext_eq => i Hi.
 by rewrite initiE 1:/# /= initiE 1:/# get_of_list // nth_sub.
by rewrite get_pack4 1:size_sub // !nth_sub.
qed.

lemma getW32_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 4 <= _ASIZE =>
 4 <= len =>
 u8prefAt (u32bytes (get32_direct (WA.init8 ("_.[_]" buf)) off)) 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 4) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u32bytes get32_bytes 1..2:/# // ler_maxr // size_to_list C /=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_u32 (_buf:W8.t A.t) _off _cur _at _dlt:
 0 <= _at-_cur < 8 =>
 asubread _buf _off
   (u64bytes
     (zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)) `<<<`
      8 * (_at - _cur))) _cur _at _dlt 4 0 (_at + min (_cur + 8 - _at) 4)
   (_dlt + min (_cur + 8 - _at) 4) (4 - min (_cur + 8 - _at) 4) 0.
proof.
move=> Hat; rewrite /asubread; split; last first.
 by rewrite size_to_list; smt(size_sub).
move=> Hppre; apply srspec_u32 => //.
 by apply getW32_bytearray; smt().
by rewrite size_sub.
qed.

lemma get64_bytes (buf: W8.t A.t) off k:
 0 <= off =>
 off + 8 <= _ASIZE =>
 get64_direct (WA.init8 ("_.[_]" buf)) off \bits8 k
 = (sub buf off 8).[k].
proof.
move=> Ho1 Ho2; rewrite get64E.
have->: W8u8.Pack.init (fun j => (WA.init8 ("_.[_]" buf)).[off+j])
        = W8u8.Pack.of_list (sub buf off 8).
 apply W8u8.Pack.ext_eq => i Hi.
 by rewrite initiE 1:/# /= initiE 1:/# get_of_list // nth_sub.
by rewrite get_pack8 1:size_sub // !nth_sub.
qed.

lemma getW64_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 8 <= _ASIZE =>
 8 <= len =>
 u8prefAt (u64bytes (get64_direct (WA.init8 ("_.[_]" buf)) off)) 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 8) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u64bytes get64_bytes 1..2:/# // ler_maxr // size_to_list C /=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_u64 (_buf:W8.t A.t) _off _cur _at _dlt _len _tb:
 8 <= _len =>
 0 <= _at-_cur < 8 =>
 asubread _buf _off (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))) _cur _at
            _dlt _len _tb (_cur + 8) (_dlt + (_cur + 8 - _at)) (_len - (_cur + 8 - _at)) _tb.
proof.
move=> Hlen Hat; rewrite /asubread; split; last first.
 by rewrite size_to_list; smt(size_sub).
move=> Hppre; apply srspec_u64_shl => //; first smt().
by apply getW64_bytearray; smt(). 
qed.

lemma get128_bytes (buf: W8.t A.t) off k:
 0 <= off =>
 off + 16 <= _ASIZE =>
 get128_direct (WA.init8 ("_.[_]" buf)) off \bits8 k
 = (sub buf off 16).[k].
proof.
move=> Ho1 Ho2; rewrite get128E.
have->: W16u8.Pack.init (fun j => (WA.init8 ("_.[_]" buf)).[off+j])
        = W16u8.Pack.of_list (sub buf off 16).
 apply W16u8.Pack.ext_eq => i Hi.
 by rewrite initiE 1:/# /= initiE 1:/# get_of_list // nth_sub.
by rewrite get_pack16 1:size_sub // !nth_sub.
qed.

lemma getW128_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 16 <= _ASIZE =>
 16 <= len =>
 u8prefAt (u128bytes (get128_direct (WA.init8 ("_.[_]" buf)) off)) 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 16) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u128bytes get128_bytes 1..2:/# // ler_maxr // size_to_list C /=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_u128 (_buf:W8.t A.t) _off _cur _at _dlt _len _tb:
 16 <= _len =>
 0 <= _at-_cur < 16 =>
 asubread _buf _off (u128bytes (get128_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))) _cur _at
            _dlt _len _tb (_cur + 16) (_dlt + (16 - (_at - _cur))) (_len - (16 - (_at - _cur))) _tb.
proof.
move=> Hlen Hat; rewrite /asubread; split; last first.
 by rewrite size_to_list; smt(size_sub).
move=> Hppre; apply srspec_u128_shl => //; first smt().
by apply getW128_bytearray; smt(). 
qed.

lemma get256_bytes (buf: W8.t A.t) off k:
 0 <= off =>
 off + 32 <= _ASIZE =>
 get256_direct (WA.init8 ("_.[_]" buf)) off \bits8 k
 = (sub buf off 32).[k].
proof.
move=> Ho1 Ho2; rewrite get256E.
have->: W32u8.Pack.init (fun j => (WA.init8 ("_.[_]" buf)).[off+j])
        = W32u8.Pack.of_list (sub buf off 32).
 apply W32u8.Pack.ext_eq => i Hi.
 by rewrite initiE 1:/# /= initiE 1:/# get_of_list // nth_sub.
by rewrite get_pack32 1:size_sub // !nth_sub.
qed.

lemma getW256_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 32 <= _ASIZE =>
 32 <= len =>
 u8prefAt (u256bytes (get256_direct (WA.init8 ("_.[_]" buf)) off)) 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 32) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u256bytes get256_bytes 1..2:/# // ler_maxr // size_to_list C /=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_u256 (_buf:W8.t A.t) _off _cur _dlt _len _tb:
 32 <= _len =>
 asubread _buf _off (u256bytes (get256_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt))) _cur _cur _dlt _len _tb
          (_cur + 32) (_dlt + 32) (_len - 32) _tb.
proof.
move=> Hlen; rewrite /asubread; split; last first.
 by rewrite size_to_list; smt(size_sub).
move=> Hppre Hpre /=; split.
 by apply srpre_next; smt(W32u8.size_to_list).
apply u8prefAbsorbW; first rewrite size_to_list size_sub /#.
by apply getW256_bytearray; smt().
qed.

lemma asubread_ahead buf off w1 cur at dlt len at1 dlt1 len1 len2 tb:
 0 <= at-cur < 8 =>
 0 <= len <= len2  =>
 at1 = cur+8 =>
 asubread buf off (u64bytes w1) cur at dlt len 0
          at1 dlt1 len1 0 =>
 asubread buf off (u64bytes w1) cur at dlt len2 tb
          at1 dlt1 (len2-(cur+8-at)) tb.
proof.
move=> Hcur Hlen Hat [H1 H].
pose L:= len2-len.
have {1}->: len2 = len + L by smt().
have ?: at1 = min (cur+8) (at+len). 
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= => _ /#.
split; last first.
 by rewrite /srfnsh /srincr size_to_list /#.
move=> Hppre.
apply (srspec_ahead len 0) => //; smt(size_sub' W8u8.size_to_list take_sub).
qed.

lemma get16_bytes (buf: W8.t A.t) off k:
 0 <= off =>
 off + 2 <= _ASIZE =>
 get16_direct (WA.init8 ("_.[_]" buf)) off \bits8 k
 = (sub buf off 2).[k].
proof.
move=> Ho1 Ho2; rewrite get16E.
have->: W2u8.Pack.init (fun j => (WA.init8 ("_.[_]" buf)).[off+j])
        = W2u8.Pack.of_list (sub buf off 2).
 apply W2u8.Pack.ext_eq => i Hi.
 by rewrite initiE 1:/# /= initiE 1:/# get_of_list // nth_sub.
by rewrite get_pack2 1:size_sub // !nth_sub.
qed.

lemma getW16_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 2 <= _ASIZE =>
 2 <= len =>
 u8prefAt (u16bytes (get16_direct (WA.init8 ("_.[_]" buf)) off)) 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 2) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u16bytes get16_bytes 1..2:/# // ler_maxr // size_to_list C /=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_w4_w2 buf off w1 cur at dlt len at1 dlt1 len1 n0:
 0 <= at-cur < 8 =>
 0 <= len < 8 =>
 at1 < cur+8 =>
 2 <= len%%4 =>
 n0 = min (cur+8-at) (len%/4*4+2) =>
 asubread buf off (u64bytes w1) cur at dlt (len%/4*4) 0
          at1 dlt1 len1 0 =>
 asubread buf off
    (u64bytes (w1 `|` (zeroextu64 (get16_direct (WA.init8 ("_.[_]" buf)) (off + dlt1)) `<<<` 8*(at1-cur))))
    cur at dlt (len%/2*2) 0
    (at+n0) (dlt+n0) (len%/2*2-n0) 0.
proof.
move=> Hcur Hlen Hat Hl Hdlt [Hspec1 H]; split; last first.
 by rewrite /srfnsh /srincr size_to_list /= /#.
move=> Hppre; have />: at1 = at + len%/4*4.
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= /#.
move: H => />; rewrite /srfnsh b2i0 /= => /addzI E.
apply (srspec_w4_w2 (sub buf (off+dlt) len) (sub buf (off+dlt) (len %/ 4 * 4))) => //.
+ smt(size_sub').
+ by rewrite take_sub /#.
+ by rewrite take_sub /#.
+ rewrite drop_sub ler_maxr 1:/# -E addzA.
  by apply getW16_bytearray; smt().
by apply Hspec1; smt().
qed.

lemma get8_bytes (buf: W8.t A.t) off:
 0 <= off =>
 off + 1 <= _ASIZE =>
 get8_direct (WA.init8 ("_.[_]" buf)) off
 = buf.[off].
proof. by move=> Ho1 Ho2; rewrite /get8 initiE /#. qed.

lemma getW8_bytearray (buf: W8.t A.t) off len:
 0 <= off =>
 off + 1 <= _ASIZE =>
 1 <= len =>
 u8prefAt [get8_direct (WA.init8 ("_.[_]" buf)) off] 0 (sub buf off len).
proof.
move=> Hoff0 Hoff1 Hlen i; case: (0 <= i < 1) => C; last smt().
rewrite ifT 1:/# /get8 initiE 1:/# ifT 1:/# ler_maxr //=.
by rewrite !nth_mkseq /#.
qed.

lemma asubread_w2_w1 buf off w1 cur at dlt len at1 dlt1 len1 n0:
 0 <= at-cur < 8 =>
 0 <= len < 8 =>
 at1 < cur+8 =>
 1 <= len%%2 =>
 at + n0 = min (cur+8) (at+len%/2*2+1) =>
 asubread buf off (u64bytes w1) cur at dlt (len%/2*2) 0
          at1 dlt1 len1 0 =>
 asubread buf off
    (u64bytes (w1 `|` (zeroextu64 (get8 (WA.init8 ("_.[_]" buf)) (off + dlt1)) `<<<`
       8 * (at1 - cur))))
    cur at dlt len 0
    (at+n0) (dlt+n0) (len-n0) 0.
proof.
move=> Hcur Hlen Hat Hl Hdlt [Hspec1 H]; split; last first.
 by rewrite /srfnsh /srincr size_to_list /= /#.
move=> Hppre; have />: at1 = at + len%/2*2.
 by move: H Hat => />; rewrite /srfnsh /srincr size_to_list !ifT 1..2:/# b2i0 /= /#.
move: H => />; rewrite /srfnsh b2i0 /= => /addzI E.
apply (srspec_w2_w1 (sub buf (off+dlt) len) (sub buf (off+dlt) (len %/ 2 * 2))) => //.
+ smt(size_sub').
+ by rewrite take_sub /#.
+ rewrite drop_sub ler_maxr 1:/# -E addzA.
  by apply getW8_bytearray; smt().
by apply Hspec1; smt().
qed.

lemma asubread_tb buf off w cur at dlt len at1 dlt1 len1 tb:
 0 <= len =>
 0 <= at - cur < 8 =>
 at + len < cur + 8 =>
 asubread buf off (u64bytes w) cur at dlt len 0 at1 dlt1 len1 0 =>
 asubread buf off
  (u64bytes
     (w `|` (of_int (tb %% 256) `<<` of_int (8 * (at1 - cur)))))
  cur at dlt len tb (at1 + b2i (tb <> 0)) (dlt1) (len1) 0.
proof.
move=> Hlen Hat Hcur []H [#]; rewrite size_to_list b2i0 => Eat Ebuf Elen _.
split; last by rewrite size_to_list /#.
move => Hppre; have ->: at1=at + len by smt().
move: (H _); first smt().
by move=> HH; apply (srspec_tb _ _ _ _ _ _ HH); smt().
qed.

lemma asubread_u64_u128 buf off w cur at dlt len tb at1 dlt1 len1 tb1:
 0 <= at-cur < 16 =>
 cur+8 <= at =>
 asubread buf off (u64bytes w) (cur+8) at dlt len tb
          at1 dlt1 len1 tb1 =>
 asubread buf off (u128bytes (VPINSR_2u64 zero w one)) cur at dlt len tb
          at1 dlt1 len1 tb1.
proof.
move=> Hat Hcur [Hspec H]; split; last first.
 by move: H => []; rewrite !size_to_list => /> /#.
move=> Hppre; move: (Hspec Hppre).
by apply srspec_u64_u128.
qed.

lemma asubread_u128_u256 buf off w cur at dlt len tb at1 dlt1 len1 tb1:
 0 <= at-cur < 32 =>
 cur+16 <= at =>
 asubread buf off (u128bytes w) (cur+16) at dlt len tb
          at1 dlt1 len1 tb1 =>
 asubread buf off (u256bytes (VINSERTI128  zero w one)) cur at dlt len tb
          at1 dlt1 len1 tb1.
proof.
move=> Hat Hcur [Hspec H]; split; last first.
 by move: H => []; rewrite !size_to_list => /> /#.
move=> Hppre; move: (Hspec Hppre).
by apply srspec_u128_u256.
qed.

op asubwrite (a a2: W8.t A.t) off lw (dlt len:int) dlt2 len2 =
 a2 = A.fill (fun i => lw.[i-(off+dlt)]) (off+dlt) (min (size lw) (max 0 len)) a
 /\ dlt2 = dlt + min (size lw) (max 0 len)
 /\ len2 = len - min (size lw) (max 0 len).

lemma asubwrite_cat a a1 a2 off lw1 lw2 dlt len dlt1 len1 dlt2 len2:
 asubwrite a a1 off lw1 dlt len dlt1 len1 =>
 asubwrite a1 a2 off lw2 dlt1 len1 dlt2 len2 =>
 asubwrite a a2 off (lw1++lw2) dlt len dlt2 len2.
proof.
rewrite /asubwrite => /> ; split; last smt(size_ge0 size_cat).
rewrite tP => i Hi; rewrite !filliE //= size_cat nth_cat.
smt(size_ge0).
qed.

(* array writes of a word, as a [fill] with its bytes *)
lemma a_set8_fill (buf: W8.t A.t) q (x: W8.t):
 A.init (WA.get8 (WA.set8_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => [x].[i-q]) q 1 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 get_set_if initiE //=.
by case: (i = q) => C; smt().
qed.

lemma a_set16_fill (buf: W8.t A.t) q (x: W16.t):
 A.init (WA.get8 (WA.set16_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => (u16bytes x).[i-q]) q 2 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 set16E initiE //=.
case: (q <= i < q + 2) => C //; last by rewrite initiE.
by rewrite /u16bytes nth_to_list /#.
qed.

lemma a_set32_fill (buf: W8.t A.t) q (x: W32.t):
 A.init (WA.get8 (WA.set32_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => (u32bytes x).[i-q]) q 4 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 set32E initiE //=.
case: (q <= i < q + 4) => C //; last by rewrite initiE.
by rewrite /u32bytes nth_to_list /#.
qed.

lemma a_set64_fill (buf: W8.t A.t) q (x: W64.t):
 A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => (u64bytes x).[i-q]) q 8 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 set64E initiE //=.
case: (q <= i < q + 8) => C //; last by rewrite initiE.
by rewrite /u64bytes nth_to_list /#.
qed.

lemma a_set128_fill (buf: W8.t A.t) q (x: W128.t):
 A.init (WA.get8 (WA.set128_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => (u128bytes x).[i-q]) q 16 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 set128E initiE //=.
case: (q <= i < q + 16) => C //; last by rewrite initiE.
by rewrite /u128bytes nth_to_list /#.
qed.

lemma a_set256_fill (buf: W8.t A.t) q (x: W256.t):
 A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" buf)) q x))
 = A.fill (fun i => (u256bytes x).[i-q]) q 32 buf.
proof.
rewrite tP => i Hi; rewrite filliE // initiE //= /get8 set256E initiE //=.
case: (q <= i < q + 32) => C //; last by rewrite initiE.
by rewrite /u256bytes nth_to_list /#.
qed.

(* extending a [fill] of a prefix of [B] by its next [k] bytes *)
lemma fill_piece (a: W8.t A.t) p (B: W8.t list) n k:
 0 <= n => 0 <= k =>
 A.fill (fun i => (take k (drop n B)).[i-(p+n)]) (p+n) k
   (A.fill (fun i => B.[i-p]) p n a)
 = A.fill (fun i => B.[i-p]) p (n+k) a.
proof.
move=> Hn Hk; rewrite tP => i Hi; rewrite !filliE //.
case: (p + n <= i < p + n + k) => C.
 by rewrite ifT 1:/# nth_take 1..2:/# nth_drop /#.
by case: (p <= i < p + n) => C' /#.
qed.

lemma awrite_upto8_step (a _a: W8.t A.t) p (B: W8.t list) n k (w: W64.t) piece:
 size B = 8 => 0 <= n => 0 <= k => n + k <= 8 =>
 a = A.fill (fun i => B.[i-p]) p n _a =>
 u64bytes w = drop n B ++ u8zeros n =>
 piece = take k (u64bytes w) =>
 A.fill (fun i => piece.[i-(p+n)]) (p+n) k a = A.fill (fun i => B.[i-p]) p (n+k) _a.
proof.
move=> HB Hn Hk Hnk -> Hw ->.
by rewrite (upto8_take B w n k) // fill_piece.
qed.


(* ---- array instances of the shared absorb and dump layers ---- *)

(* ARRAY instance: the remaining data of the input is the sub-array at the cursor
   (with the bounds the array loads need). *)
lemma addstate_spec_sub_rem st at (buf: W8.t A.t) off len tb sz c st' at' len' tb':
 0 <= off => 0 <= len => off + len <= _ASIZE =>
 addstate_spec st at (sub buf off len) tb sz off c st' at' len' tb' =>
 drop (size (sub buf off len) - len') (sub buf off len) = sub buf c len'
 /\ off <= c /\ c + len' = off + len.
proof.
move=> Hoff Hlen Hsz H.
have Hc := addstate_spec_cur _ _ _ _ _ _ _ _ _ _ _ H.
have [Hl0 Hl1] := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H.
move: Hc Hl1; rewrite size_sub // => Hc Hl1.
split; last smt().
by rewrite drop_sub; congr; smt().
qed.

(* One u64 asubread step (prefix and last word of the array absorb). *)
lemma addstate_asubread_u64 (buf: W8.t A.t) w cur st at off len tb stc at0 dlt len0 tb0 cur1 at1 dlt1 len1 tb1:
 0 <= at => 0 <= len => 0 <= tb < 256 => 0 <= off => off + len <= _ASIZE =>
 0 <= cur <= at0 < cur+8 =>
 cur1 = cur + 8 =>
 addstate_spec st at (sub buf off len) tb cur off (off + dlt) stc at0 len0 tb0 =>
 asubread buf off (u64bytes w) cur at0 dlt len0 tb0 at1 dlt1 len1 tb1 =>
 addstate_spec st at (sub buf off len) tb cur1 off (off + dlt1) (addstate_at stc cur (u64bytes w)) at1 len1 tb1.
proof.
have Hs: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
move=> Hat Hlen Htb Hoff Hsz Hc Hc1 Hspec; rewrite /asubread => [#] Hsr Eat Edlt Elen Etb.
have [Erem [Hc0 Hc2]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hsz Hspec.
apply (addstate_spec_step (sub buf off len) (u64bytes w) cur st at tb stc off (off + dlt) at0 len0 tb0 cur1 (off + dlt1) at1 len1 tb1); rewrite ?Hs //.
+ smt().
by rewrite Erem; apply Hsr; smt().
qed.

(* array twins of msubread_rlen / stores_overwrite (updstate add and dump) *)
lemma asubread_rlen (b: W8.t A.t) t cur at off dlt len:
 0 <= cur <= at < cur + 8 => 0 <= len =>
 (0 <= off /\ 0 <= dlt /\ off + dlt + len <= _ASIZE =>
  srspec (u64bytes t) 0 0 (sub b (off + dlt) len) len 0) =>
 asubread b off (u64bytes (t `<<<` 8 * (at - cur))) cur at dlt len 0
   (at + min len (cur + 8 - at)) (dlt + min len (cur + 8 - at)) (len - min len (cur + 8 - at)) 0.
proof.
move=> Hc Hl H.
have Hs: size (u64bytes (t `<<<` 8 * (at - cur))) = 8 by rewrite /u64bytes size_to_list.
rewrite /asubread Hs; split.
+ move=> Hb; apply srspec_u64; first smt().
  by apply (srspec_rlen_u8prefAt _ _ len); [rewrite size_sub | apply H].
by rewrite /srincr /srfnsh /=; smt().
qed.

lemma fill_overwrite (a: W8.t A.t) p (L Z L2: W8.t list):
 size Z <= size L2 =>
 A.fill (fun i => L2.[i - (p + size L)]) (p + size L) (size L2)
   (A.fill (fun i => (L ++ Z).[i - p]) p (size L + size Z) a)
 = A.fill (fun i => (L ++ L2).[i - p]) p (size L + size L2) a.
proof.
move=> H; have H1 := size_ge0 L; have H2 := size_ge0 Z.
apply A.tP => i Hi; rewrite !A.filliE //.
case: (p + size L <= i < p + size L + size L2) => C.
+ by rewrite ifT 1:/# nth_cat ifF 1:/#; congr; ring.
case: (p <= i < p + (size L + size Z)) => C2.
+ by rewrite ifT 1:/# !nth_cat; smt().
by rewrite ifF 1:/#.
qed.

lemma fill_take (a: W8.t A.t) p (L: W8.t list) n:
 A.fill (fun i => L.[i - p]) p n a = A.fill (fun i => (take n L).[i - p]) p n a.
proof.
apply A.tP => i Hi; rewrite !A.filliE //.
by case: (p <= i < p + n) => C //; rewrite nth_take 1,2:/#.
qed.

(* `afill a p L`: the list L written into the array at offset p (the array
   twin of `stores m p L`, used by the updstate dumps). *)
op afill (a: W8.t A.t) (p: int) (L: W8.t list) : W8.t A.t =
 A.fill (fun i => L.[i - p]) p (size L) a.

lemma afill_nil (a: W8.t A.t) p: afill a p [] = a.
proof. by apply A.tP => i Hi; rewrite /afill A.filliE // /#. qed.

lemma afill_overwrite (a: W8.t A.t) p (L Z L2: W8.t list):
 size Z <= size L2 =>
 afill (afill a p (L ++ Z)) (p + size L) L2 = afill a p (L ++ L2).
proof. by move=> H; rewrite /afill !size_cat fill_overwrite. qed.

lemma a_set64_afill (buf: W8.t A.t) q (x: W64.t):
 A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" buf)) q x)) = afill buf q (u64bytes x).
proof. by rewrite a_set64_fill /afill /u64bytes size_to_list. qed.

lemma a_set256_afill (buf: W8.t A.t) q (x: W256.t):
 A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" buf)) q x)) = afill buf q (u256bytes x).
proof. by rewrite a_set256_fill /afill /u256bytes size_to_list. qed.

lemma a_set128_afill (buf: W8.t A.t) q (x: W128.t):
 A.init (WA.get8 (WA.set128_direct (WA.init8 ("_.[_]" buf)) q x)) = afill buf q (u128bytes x).
proof. by rewrite a_set128_fill /afill /u128bytes size_to_list. qed.

lemma afill_rlen (a: W8.t A.t) p (w: W64.t) n:
 0 <= n =>
 A.fill (fun i => (u64bytes w).[i - p]) p (min 8 (max 0 n)) a = afill a p (take n (u64bytes w)).
proof.
move=> Hn; apply A.tP => i Hi; rewrite /afill !A.filliE // size_take // /u64bytes size_to_list.
case: (p <= i < p + min 8 (max 0 n)) => C.
+ by rewrite ifT 1:/# nth_take 1,2:/#.
by rewrite ifF 1:/#.
qed.

(* ARRAY instance of the absorb input: the whole array, read through sub. *)
lemma to_list_sub (buf: W8.t A.t): to_list buf = sub buf 0 _ASIZE.
proof. by rewrite /to_list /sub; apply eq_mkseq => i /=. qed.

lemma take_to_list (buf: W8.t A.t) k:
 0 <= k <= _ASIZE => take k (to_list buf) = sub buf 0 k.
proof. by move=> Hk; rewrite to_list_sub take_sub /#. qed.

lemma slice_to_list (buf: W8.t A.t) k n:
 0 <= k => 0 <= n => k + n <= _ASIZE =>
 take n (drop k (to_list buf)) = sub buf k n.
proof. by move=> Hk Hn Hkn; rewrite to_list_sub drop_sub take_sub; congr; smt(). qed.

lemma drop_to_list (buf: W8.t A.t) k:
 0 <= k <= _ASIZE => drop k (to_list buf) = sub buf k (_ASIZE - k).
proof. by move=> Hk; rewrite to_list_sub drop_sub; congr; smt(). qed.

(* array adapters of the shared dump/squeeze layer *)
lemma asubwrite_dump0 (S: WArray200.t) a off len:
 0 <= len => asubwrite a a off (sub S 0 0) 0 len 0 len.
proof.
move=> H; have ->: sub S 0 0 = [] by rewrite -size_eq0 size_sub.
rewrite /asubwrite /=; split; last smt().
by rewrite tP => i Hi; rewrite filliE // /#.
qed.

lemma asubwrite_fill a off lw dlt len p n dlt2 len2:
 p = off + dlt => n = size lw => dlt2 = dlt + n => len2 = len - n => n <= len =>
 asubwrite a (A.fill (fun i => lw.[i - p]) p n a) off lw dlt len dlt2 len2.
proof.
move=> -> -> -> -> H; rewrite /asubwrite ler_maxr; first smt(size_ge0).
by rewrite ler_minl.
qed.

lemma asubwrite_set256 a off w dlt len p dlt2 len2:
 p = off + dlt => dlt2 = dlt + 32 => len2 = len - 32 => 32 <= len =>
 asubwrite a (A.init (WA.get8 (WA.set256_direct (WA.init8 ("_.[_]" a)) p w)))
           off (u256bytes w) dlt len dlt2 len2.
proof.
by move=> *; rewrite a_set256_fill; apply asubwrite_fill => //; rewrite /u256bytes size_to_list.
qed.

lemma asubwrite_set128 a off w dlt len p dlt2 len2:
 p = off + dlt => dlt2 = dlt + 16 => len2 = len - 16 => 16 <= len =>
 asubwrite a (A.init (WA.get8 (WA.set128_direct (WA.init8 ("_.[_]" a)) p w)))
           off (u128bytes w) dlt len dlt2 len2.
proof.
by move=> *; rewrite a_set128_fill; apply asubwrite_fill => //; rewrite /u128bytes size_to_list.
qed.

lemma asubwrite_set64 a off w dlt len p dlt2 len2:
 p = off + dlt => dlt2 = dlt + 8 => len2 = len - 8 => 8 <= len =>
 asubwrite a (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" a)) p w)))
           off (u64bytes w) dlt len dlt2 len2.
proof.
by move=> *; rewrite a_set64_fill; apply asubwrite_fill => //; rewrite /u64bytes size_to_list.
qed.

lemma asubwrite_rebase a a2 off off' lw dlt len dlt2 len2:
 asubwrite a a2 off lw dlt len dlt2 len2 =>
 asubwrite a a2 off' lw (dlt + (off - off')) len (dlt2 + (off - off')) len2.
proof.
rewrite /asubwrite => [[-> [-> ->]]].
by rewrite (_: off' + (dlt + (off - off')) = off + dlt) 1:/#; smt().
qed.

lemma asubwrite_dump_step (S: WArray200.t) a0 a1 a2 off len k n lw d1 d2 k1 l1 l2:
 0 <= k => 0 <= n => k + n <= len => k1 = k + n => l1 = len - k => l2 = len - k1 =>
 asubwrite a0 a1 off (sub S 0 k) 0 len d1 l1 =>
 lw = sub S k n =>
 asubwrite a1 a2 off lw d1 l1 d2 l2 =>
 asubwrite a0 a2 off (sub S 0 k1) 0 len d2 l2.
proof.
move=> Hk Hn Hkn -> -> -> H1 -> H2.
by rewrite (sub_cat S 0 k n) //=; exact (asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H1 H2).
qed.

lemma fill_stbytes_sub (S: WArray200.t) (a: W8.t A.t) p n len:
 0 <= n <= len =>
 A.fill (fun i => (sub S 0 len).[i - p]) p n a = A.fill (fun i => S.[i - p]) p n a.
proof.
move=> Hn; rewrite tP => i Hi; rewrite !filliE //=.
by case: (p <= i < p + n) => C //; rewrite nth_sub /#.
qed.

lemma asubwrite_dump_last (S: WArray200.t) a0 a1 a2 off len k n lw d1 d2 l1 l2:
 0 <= k <= len => len <= k + n => l1 = len - k =>
 asubwrite a0 a1 off (sub S 0 k) 0 len d1 l1 =>
 lw = sub S k n =>
 asubwrite a1 a2 off lw d1 l1 d2 l2 =>
 a2 = A.fill (fun i => S.[i - off]) off len a0 /\ d2 = len.
proof.
move=> Hk Hkn -> H1 -> H2.
have := asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H1 H2.
rewrite (_: sub S 0 k ++ sub S k n = sub S 0 (k+n)) 1:(sub_cat S 0 k n) 1..2:/# //=.
rewrite /asubwrite size_sub 1:/# => [[-> [-> _]]].
by rewrite (_: min (k + n) (max 0 len) = len) 1:/# fill_stbytes_sub /#.
qed.

lemma asubwrite_dump_fin (S: WArray200.t) a0 a1 off len d1:
 0 <= len =>
 asubwrite a0 a1 off (sub S 0 len) 0 len d1 0 =>
 a1 = A.fill (fun i => S.[i - off]) off len a0 /\ d1 = len.
proof.
move=> H; rewrite /asubwrite size_sub 1:/# => [[-> [-> _]]].
by rewrite (_: min len (max 0 len) = len) 1:/# fill_stbytes_sub /#.
qed.

lemma asubwrite_app_dump (S: WArray200.t) a0 a1 off len L n p d1 l1 d2 l2:
 size L + n <= len => 0 <= n => p = off + d1 => d2 = d1 + n => l2 = l1 - n =>
 asubwrite a0 a1 off L 0 len d1 l1 =>
 asubwrite a0 (A.fill (fun i => S.[i - p]) p n a1) off (L ++ sub S 0 n) 0 len d2 l2.
proof.
move=> Hsz Hn Hp -> -> H1.
apply (asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H1).
move: H1; rewrite /asubwrite => [[_ [Hd1 Hl1]]].
rewrite -(fill_stbytes_sub S a1 p n n) 1:/#.
by apply asubwrite_fill; rewrite ?size_sub //; smt(size_ge0).
qed.

lemma asubwrite_to_list a0 a1 L d1 l1:
 size L = _ASIZE =>
 asubwrite a0 a1 0 L 0 _ASIZE d1 l1 => to_list a1 = L.
proof.
move=> Hsz; rewrite /asubwrite => [[-> _]].
apply (eq_from_nth W8.zero); first by rewrite size_to_list Hsz.
move=> i; rewrite size_to_list => Hi.
rewrite (nth_change_dfl witness) 1:size_to_list 1:/# get_to_list filliE //= Hsz ifT 1:/#.
by apply nth_change_dfl => /#.
qed.

lemma asubwrite_squeeze_last r8 st a0 a1 d1 l1 p:
 0 < r8 <= 200 => 0 < _ASIZE %% r8 => p = d1 =>
 asubwrite a0 a1 0 (squeezeblocks r8 st (_ASIZE %/ r8)) 0 _ASIZE d1 l1 =>
 to_list (A.fill (fun i => (stbytes (st_i st (_ASIZE %/ r8 + 1))).[i - p]) p (_ASIZE %% r8) a1)
 = SQUEEZE1600 r8 _ASIZE st.
proof.
move=> Hr C -> H; apply (asubwrite_to_list a0 _ _ (d1 + _ASIZE %% r8) (l1 - _ASIZE %% r8)).
 by rewrite size_SQUEEZE1600 //; exact _ASIZE_ge0.
rewrite (SQUEEZE1600_split r8 _ASIZE st) // 1:_ASIZE_ge0 C /=.
have Hsz: size (squeezeblocks r8 st (_ASIZE %/ r8)) = r8 * (_ASIZE %/ r8).
 by rewrite size_squeezeblocks //; smt(divz_ge0 _ASIZE_ge0).
apply (asubwrite_app_dump _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) => //; last smt().
by rewrite Hsz; smt(_ASIZE_ge0).
qed.

lemma asubwrite_squeeze_fin r8 st a0 a1 d1 l1:
 0 < r8 <= 200 => !(0 < _ASIZE %% r8) =>
 asubwrite a0 a1 0 (squeezeblocks r8 st (_ASIZE %/ r8)) 0 _ASIZE d1 l1 =>
 to_list a1 = SQUEEZE1600 r8 _ASIZE st.
proof.
move=> Hr C; rewrite (SQUEEZE1600_split r8 _ASIZE st) // 1:_ASIZE_ge0 ifF // cats0.
apply asubwrite_to_list.
by rewrite size_squeezeblocks //; smt(divz_ge0 _ASIZE_ge0).
qed.

(* budgeted sub-writes of a prefix (array) [sub S 0 k]: one step, a skipped step
   (budget exhausted), and changing or truncating the budget *)
lemma asubwrite_sub_step (S: WArray200.t) a0 a1 a2 off len k n k1 lw d1 l1 d2 l2:
 0 <= k => 0 <= n => k1 = k + n =>
 asubwrite a0 a1 off (sub S 0 k) 0 len d1 l1 =>
 lw = sub S k n =>
 asubwrite a1 a2 off lw d1 l1 d2 l2 =>
 asubwrite a0 a2 off (sub S 0 k1) 0 len d2 l2.
proof.
move=> Hk Hn -> H1 -> H2.
by rewrite (sub_cat S 0 k n) //=; exact (asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H1 H2).
qed.

lemma asubwrite_sub_skip (S: WArray200.t) a0 a1 off len k k' d1 l1:
 0 <= k <= k' => !(0 < l1) =>
 asubwrite a0 a1 off (sub S 0 k) 0 len d1 l1 =>
 asubwrite a0 a1 off (sub S 0 k') 0 len d1 l1.
proof.
move=> Hk Hl; rewrite /asubwrite !size_sub 1,2:/# => [[-> [-> El]]].
have ->: min k' (max 0 len) = min k (max 0 len) by smt().
split; last smt().
rewrite tP => i Hi; rewrite !filliE //=.
case: (0 + 0 <= i - off < min k (max 0 len)) => C; last by smt().
by rewrite !nth_sub /#.
qed.

lemma asubwrite_take_budget a0 a1 off (lw: W8.t list) n dlt len d1 l1:
 0 <= n => len <= n =>
 asubwrite a0 a1 off lw dlt len d1 l1 =>
 asubwrite a0 a1 off (take n lw) dlt len d1 l1.
proof.
move=> Hn Hl; rewrite /asubwrite size_take' // => [[-> [-> ->]]].
have ->: min (if n <= size lw then n else size lw) (max 0 len) = min (size lw) (max 0 len) by smt().
split; last done.
rewrite tP => i Hi; rewrite !filliE //=.
by case: (off + dlt <= i < off + dlt + min (size lw) (max 0 len)) => C //; rewrite nth_take /#.
qed.

lemma asubwrite_untake a0 a1 off (lw: W8.t list) n dlt len d1 l1:
 0 <= n => len <= n =>
 asubwrite a0 a1 off (take n lw) dlt len d1 l1 =>
 asubwrite a0 a1 off lw dlt len d1 l1.
proof.
move=> Hn Hl; rewrite /asubwrite size_take' // => [[-> [-> ->]]].
have ->: min (if n <= size lw then n else size lw) (max 0 len) = min (size lw) (max 0 len) by smt().
split; last done.
rewrite tP => i Hi; rewrite !filliE //=.
by case: (off + dlt <= i < off + dlt + min (size lw) (max 0 len)) => C //; rewrite nth_take /#.
qed.

lemma asubwrite_rebudget a0 a1 off (lw: W8.t list) dlt len len' d1 l1 l1':
 size lw <= len => size lw <= len' => l1' = len' - size lw =>
 asubwrite a0 a1 off lw dlt len d1 l1 =>
 asubwrite a0 a1 off lw dlt len' d1 l1'.
proof.
move=> H1 H2 ->; rewrite /asubwrite => [[-> [-> _]]].
by rewrite (_: min (size lw) (max 0 len) = size lw) 1:/# (_: min (size lw) (max 0 len') = size lw) 1:/#.
qed.

lemma asubwrite_dump_take (S: WArray200.t) a0 a1 off len k d1 l1:
 0 <= len <= k =>
 asubwrite a0 a1 off (sub S 0 k) 0 len d1 l1 =>
 a1 = A.fill (fun i => S.[i - off]) off len a0 /\ d1 = len.
proof.
move=> Hl; rewrite /asubwrite size_sub 1:/# => [[-> [-> _]]].
by rewrite (_: min k (max 0 len) = len) 1:/# /= (fill_stbytes_sub S a0 off len k) /#.
qed.

module MM = {
  proc __a_ilen_read_upto8_at (buf:W8.t A.t, offset:int, dELTA:int,
                               lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ M.__SHLQ (w, (aT - cUR));
        dELTA <- (dELTA + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          w <@ M.__SHLQ (w, (aT - cUR));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <-
          (dELTA + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ M.__SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <-
          (zeroextu64
          (get8_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA))
          );
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
          t8 <@ M.__SHLQ (t8, (aT - cUR));
          w <- (w `|` t8);
          aT <- (aT + 1);
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (tRAIL <> 0))) {
          t8 <- (W64.of_int (tRAIL %% 256));
          t8 <- (t8 `<<` (W8.of_int (8 * (aT - cUR))));
          w <- (w `|` t8);
          aT <- (aT + 1);
          tRAIL <- 0;
        } else {
          
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto16_at (buf:W8.t A.t, offset:int, dELTA:int,
                                lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ M.__SHLDQ (w, (aT - cUR));
        dELTA <- (dELTA + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ __a_ilen_read_upto8_at (buf,
          offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t64_0) <@ __a_ilen_read_upto8_at (buf,
          offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (dELTA, lEN, tRAIL, aT, t64_1) <@ __a_ilen_read_upto8_at (buf,
          offset, dELTA, lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto32_at (buf:W8.t A.t, offset:int, dELTA:int,
                                lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT, t128_0) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (dELTA, lEN, tRAIL, aT, t128_1) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_bcast_upto8_at (buf:W8.t A.t, offset:int,
                                     dELTA:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ M.__SHLQ_256 (w256, aT - cUR);
        dELTA <- (dELTA + (cUR + 8 - aT));
        lEN <- (lEN - (cUR + 8 - aT));
        aT <- (cUR + 8);
      } else {
        (dELTA, lEN, tRAIL, aT, w) <@ __a_ilen_read_upto8_at (buf, offset,
        dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc __a_ilen_write_upto8 (buf:W8.t A.t, offset:int, dELTA:int,
                             lEN:int, w:W64.t) : W8.t A.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set32_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set16_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set8_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __a_ilen_write_upto16 (buf:W8.t A.t, offset:int, dELTA:int,
                              lEN:int, w:W128.t) : W8.t A.t * int *
                                                   int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set128_direct (WA.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set64_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA) (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- MOVV_64 (truncateu64 w);
        (buf, dELTA, lEN) <@ __a_ilen_write_upto8 (buf, offset, dELTA, 
        lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __a_ilen_write_upto32 (buf:W8.t A.t, offset:int, dELTA:int,
                              lEN:int, w:W256.t) : W8.t A.t * int *
                                                   int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set256_direct (WA.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set128_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ __a_ilen_write_upto16 (buf, offset, dELTA, 
        lEN, t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __a_rlen_read_upto8 (a:W8.t A.t, off:int, len:int) : int *
                                                                   W64.t = {
    var w:W64.t;
    var zf:bool;
    var sh:W8.t;
    var x:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    if ((8 <= len)) {
      w <- (get64_direct (WA.init8 (fun i => a.[i])) off);
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        w <-
        (zeroextu64 (get32_direct (WA.init8 (fun i => a.[i])) off));
        off <- (off + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        x <-
        (zeroextu64 (get16_direct (WA.init8 (fun i => a.[i])) off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        off <- (off + 2);
        sh <- (sh + (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        x <-
        (zeroextu64 (get8_direct (WA.init8 (fun i => a.[i])) off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        off <- (off + 1);
      } else {
        
      }
    }
    return (off, w);
  }
  proc __a_rlen_write_upto8 (buf:W8.t A.t, off:int, data:W64.t,
                             len:int) : W8.t A.t * int = {
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    if ((8 <= len)) {
      buf <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf.[i])) off data))
      );
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set32_direct (WA.init8 (fun i => buf.[i])) 
        off (truncateu32 data))));
        off <- (off + 4);
        data <- (data `>>` (W8.of_int 32));
      } else {
        
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set16_direct (WA.init8 (fun i => buf.[i])) 
        off (truncateu16 data))));
        off <- (off + 2);
        data <- (data `>>` (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set8_direct (WA.init8 (fun i => buf.[i])) off
        (truncateu8 data))));
        off <- (off + 1);
      } else {
        
      }
    }
    return (buf, off);
  }
}.


lemma a_ilen_read_upto8_at_ll: islossless MM.__a_ilen_read_upto8_at
by islossless.

hoare a_ilen_read_upto8_at_h _buf _off _dlt _len _tb _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> asubread _buf _off (u64bytes res.`5) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3.
proof.
proc; simplify.
if => //.
 by auto => |> [[H|H]|H]; apply asubread0; rewrite size_to_list ?u64bytes0 // /#.
sp; if => //.
 (* 8 <= lEN *)
 wp; ecall (SHLQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 by apply asubread_u64.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur /\ tRAIL=_tb
         /\ dELTA=_dlt /\ lEN=_len /\ aT=_at==> _).
 by move => /> /#.
pose n0 := min (_cur + 8 - _at) (_len %/ 4 * 4).
seq 1: ( #[:2,3,4:7]pre
       /\ asubread _buf _off (u64bytes w) _cur _at _dlt (_len %/ 4 * 4) 0 aT dELTA (_len %/ 4 * 4-n0) 0
       /\ dELTA = _dlt+n0 /\ lEN = _len - n0 /\ aT=_at+n0).
 if => //.
  (* 4 <= lEN  *)
  wp; ecall (SHLQ_h w (aT-cUR)); auto => |> *.
  split; first smt().
  move=> ??.
  rewrite /n0.
  have ->: _len %/ 4 * 4 = 4 by smt().
  have ->: (_dlt + if _cur + 8 <= _at + 4 then _cur + 8 - _at else 4)
          = _dlt + min (_cur+8-_at) 4 by smt().
  have ->: (if _cur + 8 <= _at + 4 then _cur + 8 else _at + 4)
          = _at + min (_cur+8-_at) 4 by smt().
  split; last smt().
  by apply asubread_u32.
 auto => |> ??????; split; last smt().
 rewrite /n0.
 have ->: (_len %/ 4 * 4 - min (_cur + 8 - _at) (_len %/ 4 * 4)) = _len %/ 4 * 4 by smt().
 by apply asubread0; rewrite u64bytes0 size_nseq /#.
pose n1 := min (_cur+8-_at) (_len %/ 2 * 2).
exlim aT => at1; exlim lEN => len1; exlim dELTA => dlt1.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur /\ tRAIL=_tb
         /\ dELTA=dlt1 /\ lEN=len1 /\ aT=at1
         /\ asubread _buf _off (u64bytes w) _cur _at _dlt (_len%/4*4) 0
                     at1 dlt1 (_len %/ 4 * 4 - n0) 0
         /\ dlt1=_dlt+n0 /\ len1=_len-n0 /\ at1=_at+n0
         ==> _).
 by move => />.
seq 1: ( #[/:9]pre
      /\ asubread _buf _off (u64bytes w) _cur _at _dlt (_len %/ 2 * 2) 0
                  aT dELTA (_len%/2*2-n1) 0
      /\ dELTA=_dlt+n1 /\ lEN=_len-n1 /\ aT=_at+n1).
 if => //.
  (* 2 <= lEN *)
  wp; ecall (SHLQ_h t16 (aT-cUR)); auto => |> &m ????? H1??.
  split; first smt().
  move=> ??; split; last smt().
  rewrite -!addzA.
  have ->: (n0 + if _cur + 8 <= _at + (n0 + 2) then _cur + (8 - (_at + n0)) else 2)=n1 by smt().
  have ->: (if _cur + 8 <= _at + (n0 + 2) then _cur + 8 else _at + (n0 + 2))=_at+n1 by smt().
  rewrite (addzA _at).
  by apply (asubread_w4_w2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
 auto => |> ??????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En0: n0 = _cur+8-_at by smt().
 have En1: n1 = n0 by smt().
 split; last smt().
 rewrite En1 {3}En0.
 by apply (asubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
pose n2 := min (_cur+8-_at) _len.
exlim aT => at2; exlim lEN => len2; exlim dELTA => dlt2.
conseq (: _cur <= _at < _cur+8 /\ 0 <= _len < 8 /\ (_len<>0 \/ _tb<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur /\ tRAIL=_tb
         /\ dELTA=dlt2 /\ lEN=len2 /\ aT=at2
         /\ asubread _buf _off (u64bytes w) _cur _at _dlt (_len%/2*2) 0
                     at2 dlt2 (_len %/ 2 * 2 - n1) 0
         /\ dlt2=_dlt+n1 /\ len2=_len-n1 /\ at2=_at+n1
         ==> _).
 by move => />.
seq 1: ( #[/:9]pre
       /\ asubread _buf _off (u64bytes w) _cur _at _dlt _len 0
                   aT dELTA (_len-n2) 0
       /\ dELTA=_dlt+n2 /\ lEN=_len-n2 /\ aT=_at+n2).
 if => //.
  (* 1 <= lEN *)
  wp; ecall (SHLQ_h t8 (aT-cUR)); auto => |> ?????? H1??.
  split; first smt(). 
  move=> ??; split; last smt().
  rewrite -!addzA.
  have ->: n1+1=n2 by smt().
  rewrite (addzA _at).
  by apply (asubread_w2_w1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
 auto => |> &m ?????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En1: n1 = _cur+8-_at by smt().
 have En2: n2 = n1 by smt().
 split; last smt().
 rewrite En2 {3}En1.
 by apply (asubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
if => //.
 auto => |> &m ?????H??.
 have ->: 1 = b2i (_tb<>0) by smt().
 by apply asubread_tb; smt().
auto => |> &m ?????H; rewrite negb_and => [[C|C]]; last smt().
have {3}->: n2 =  _cur + 8 - _at by smt().
apply (asubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
qed.

phoare a_ilen_read_upto8_at_ph _buf _off _dlt _len _tb _cur _at:
 [ MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> asubread _buf _off (u64bytes res.`5) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_read_upto8_at_ll (a_ilen_read_upto8_at_h _buf _off _dlt _len _tb _cur _at). qed.

lemma a_ilen_read_upto16_at_ll: islossless MM.__a_ilen_read_upto16_at
by islossless.

hoare a_ilen_read_upto16_at_h _buf _off _dlt _len _tb _cur _at:
 MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> asubread _buf _off (u128bytes res.`5) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3.
proof.
proc; simplify.
if => //.
 auto => |> H.
 apply asubread0.
  by rewrite size_to_list ?u128bytes0 // /#.
 by rewrite size_to_list /#.
(* 16 <= lEN *)
if => //.
 wp; ecall (SHLDQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 by apply asubread_u128.
(* lEN < 16 *)
if => //.
 (* CUR+8 <= AT *)
 wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT); auto => |>.
 rewrite !negb_or negb_and => |> ???????? [dlt0 len0 tb0 at0 w0] /= H.
 by apply asubread_u64_u128; smt().
wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT).
wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL cUR aT).
auto => |>; rewrite !negb_or negb_and. 
move => ??? []dlt0 len0 tb0 at0 w0 |> H0.
move=> []dlt1 len1 tb1 at1  w2 /= H1.
rewrite -u64bytes_cat.
by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).
qed.

phoare a_ilen_read_upto16_at_ph _buf _off _dlt _len _tb _cur _at:
 [ MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> asubread _buf _off (u128bytes res.`5) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3
 ] = 1%r.
proof.
by conseq a_ilen_read_upto16_at_ll
          (a_ilen_read_upto16_at_h _buf _off _dlt _len _tb _cur _at).
qed.

lemma a_ilen_read_upto32_at_ll: islossless MM.__a_ilen_read_upto32_at
by islossless.

hoare a_ilen_read_upto32_at_h _buf _off _dlt _len _tb _cur _at:
 MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> asubread _buf _off (u256bytes res.`5) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3.
proof.
proc; simplify.
if => //.
 auto => |> H. 
 apply asubread0.
  by rewrite size_to_list ?u256bytes0 // /#.
 by rewrite size_to_list /#.
(* 32 <= lEN *)
sp; if => //.
 auto => |> ??.
 by apply asubread_u256.
(* lEN < 16 *)
if => //.
 (* CUR+16 <= AT *)
 wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL (cUR+16) aT); auto => |>.
 rewrite !negb_or negb_and => |> ??????? [dlt0 len0 tb0 at0 w0] /= H.
 by apply asubread_u128_u256; smt().
wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL (cUR+16) aT).
wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL cUR aT).
auto => |>.
rewrite !negb_or negb_and. 
move => ???[]dlt0 len0 tb0 at0 w0 |> H0 []dlt1 len1 tb1 at1 w1 /= H1.
rewrite -u128bytes_cat.
by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 _).
qed.

lemma a_ilen_read_bcast_upto8_at_ll: islossless MM.__a_ilen_read_bcast_upto8_at
by islossless.

equiv a_ilen_read_bcast_upto8_at_eq:
 MM.__a_ilen_read_bcast_upto8_at
 ~ MM.__a_ilen_read_upto8_at
 : ={arg}
 ==> (res.`1,res.`2,res.`3,res.`4,res.`5){1}
     = (res.`1,res.`2,res.`3,res.`4,VPBROADCAST_4u64 (truncateu64 (VMOV_64 res.`5))){2}.
proof.
proc; simplify.
if => //=.
 auto => />.
 by move=> *; clear; circuit.
sp; if => //=.
 inline*; auto => /> &m *; split.
  move=> *.
  rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
  by rewrite /W64.(`<<`) trunc_VMOV_64 of_uintK modz_small 1:/# of_uintK modz_small /#.
 move=> *.
 rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
 by rewrite /W64.(`<<`) trunc_VMOV_64 1:/# of_uintK modz_small /#.
inline *.
rcondf {1} 8; first by auto.
rcondf {1} 8; first by auto.
wp 12 4.
conseq (: ={buf,offset,dELTA,aT,cUR,lEN,tRAIL} ==> ={w,aT,cUR,buf,offset,dELTA,lEN,tRAIL}) => //.
by sim.
qed.

(* the broadcast read is the plain read, broadcast to the four lanes *)
hoare a_ilen_read_bcast_upto8_at_h _buf _off _dlt _len _tb _cur _at:
 MM.__a_ilen_read_bcast_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_tb /\ cUR=_cur /\ aT=_at
 ==> exists w, res.`5 = VPBROADCAST_4u64 w
     /\ asubread _buf _off (u64bytes w) _cur _at _dlt _len _tb res.`4 res.`1 res.`2 res.`3.
proof.
conseq a_ilen_read_bcast_upto8_at_eq (a_ilen_read_upto8_at_h _buf _off _dlt _len _tb _cur _at).
 by move=> &1 />; exists arg{1}.
move=> &1 &2 /= [E1 [E2 [E3 [E4 E5]]]] H.
by exists res{2}.`5; rewrite E1 E2 E3 E4 E5 trunc_VMOV_64.
qed.

lemma a_ilen_write_upto8_ll: islossless MM.__a_ilen_write_upto8
by islossless.

hoare a_ilen_write_upto8_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u64bytes _w) _dlt _len res.`2 res.`3.
proof.
proc; simplify.
if => //=; last first.
 auto => /> Hlen; rewrite /asubwrite ler_maxl 1:/# ler_minr; first smt(size_ge0).
 by rewrite tP => i Hi; rewrite filliE // /#.
if => //=.
 by auto => /> Hlen0 Hlen1; rewrite /asubwrite a_set64_fill /u64bytes size_to_list ler_maxr 1:/# ler_minl 1:/#.
(* 0 < lEN < 8: pieces of 4, 2 and 1 bytes; [_len - lEN] bytes written *)
seq 1: (0 <= lEN < 4 /\ lEN <= _len < 8 /\ offset = _off /\ dELTA = _dlt + (_len - lEN)
        /\ buf = A.fill (fun i => (u64bytes _w).[i-(_off+_dlt)]) (_off+_dlt) (_len - lEN) _buf
        /\ u64bytes w = drop (_len - lEN) (u64bytes _w) ++ u8zeros (_len - lEN)).
 if => //.
  auto => /> Hlen0 Hlen1 Hlen4.
  rewrite (_: _len - (_len - 4) = 4) 1:/# a_set32_fill u32bytes_trunc.
  rewrite (upto8_shr (u64bytes _w) _w 0 4 32) ?size_to_list ?drop0 ?nseq0 ?cats0 //=.
  do 2!(split; first smt()).
  by rewrite tP => i Hi; rewrite !filliE //=; smt(nth_take).
 auto => /> *; rewrite drop0 nseq0 cats0 /=; do 2!(split; first smt()).
 by rewrite tP => i Hi; rewrite filliE // /#.
seq 1: (0 <= lEN < 2 /\ lEN <= _len < 8 /\ offset = _off /\ dELTA = _dlt + (_len - lEN)
        /\ buf = A.fill (fun i => (u64bytes _w).[i-(_off+_dlt)]) (_off+_dlt) (_len - lEN) _buf
        /\ u64bytes w = drop (_len - lEN) (u64bytes _w) ++ u8zeros (_len - lEN)).
 if => //.
  auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
  rewrite a_set16_fill u16bytes_trunc.
  rewrite (_: _off + (_dlt + (_len - lEN{m})) = _off + _dlt + (_len - lEN{m})) 1:/#.
  rewrite (_: _len - (lEN{m} - 2) = _len - lEN{m} + 2) 1:/#.
  rewrite (awrite_upto8_step _ _buf (_off+_dlt) (u64bytes _w) (_len - lEN{m}) 2 w{m}) ?size_to_list // 1..2:/#.
  rewrite (upto8_shr (u64bytes _w) w{m} (_len - lEN{m}) 2 16) ?size_to_list // 1..2:/#.
  smt().
 by auto => /> /#.
if => //.
 auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
 rewrite a_set8_fill u8bytes_trunc /asubwrite size_to_list.
 rewrite (_: _off + (_dlt + (_len - lEN{m})) = _off + _dlt + (_len - lEN{m})) 1:/#.
 rewrite (awrite_upto8_step _ _buf (_off+_dlt) (u64bytes _w) (_len - lEN{m}) 1 w{m}) ?size_to_list // 1..2:/#.
 by rewrite (_: _len - lEN{m} + 1 = _len) 1:/# /#.
auto => /> &m Hlen0 Hlen1 Hlen2 Hlen3 Hw Hlen4.
have ->: lEN{m} = 0 by smt().
by rewrite /asubwrite size_to_list ler_maxr 1:/# ler_minr /#.
qed.

phoare a_ilen_write_upto8_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u64bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto8_ll (a_ilen_write_upto8_h _buf _off _dlt _len _w). qed.

lemma a_ilen_write_upto16_ll: islossless MM.__a_ilen_write_upto16
by islossless.

hoare a_ilen_write_upto16_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u128bytes _w) _dlt _len res.`2 res.`3.
proof.
proc; simplify.
if => //=; last first.
 auto => /> Hlen; rewrite /asubwrite ler_maxl 1:/# ler_minr; first smt(size_ge0).
 by rewrite tP => i Hi; rewrite filliE // /#.
if => //=.
 by auto => /> H0 H16; apply asubwrite_set128 => /#.
(* 0 < lEN < 16: an optional low u64, then the rest via __a_ilen_write_upto8 *)
seq 1: (0 < _len < 16 /\ offset = _off
        /\ ((8 <= _len /\ asubwrite _buf buf _off (take 8 (u128bytes _w)) _dlt _len dELTA lEN
             /\ w = VPUNPCKH_2u64 _w _w)
         \/ (_len < 8 /\ buf = _buf /\ dELTA = _dlt /\ lEN = _len /\ w = _w))).
 if => //.
  auto => /> H0 H16 H8; split; first smt().
  have Hm: asubwrite _buf (A.init (WA.get8 (WA.set64_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) (MOVV_64 (truncateu64 _w)))))
             _off (take 8 (u128bytes _w)) _dlt _len (_dlt + 8) (_len - 8).
   by rewrite take8_u128bytes /MOVV_64; apply asubwrite_set64 => /#.
  by left.
 by auto => /> /#.
ecall (a_ilen_write_upto8_h buf offset dELTA lEN t64).
auto => |> &m H0 H16 Hc [b2 d2 l2] /= H2.
case: Hc => [[H8 [H Hw]]|[H8 [Hb [Hd [Hl Hw]]]]].
 move: H2; rewrite Hw /MOVV_64 => H2.
 have := asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H H2.
 by rewrite take8_u128bytes -u128bytes_split.
move: H2; rewrite Hb Hd Hl Hw /MOVV_64 -take8_u128bytes => H2.
by apply (asubwrite_untake _ _ _ _ 8 _ _ _ _ _ _ H2) => /#.
qed.

phoare a_ilen_write_upto16_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u128bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto16_ll (a_ilen_write_upto16_h _buf _off _dlt _len _w). qed.

lemma a_ilen_write_upto32_ll: islossless MM.__a_ilen_write_upto32
by islossless.

hoare a_ilen_write_upto32_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u256bytes _w) _dlt _len res.`2 res.`3.
proof.
proc; simplify.
if => //=; last first.
 auto => /> Hlen; rewrite /asubwrite ler_maxl 1:/# ler_minr; first smt(size_ge0).
 by rewrite tP => i Hi; rewrite filliE // /#.
if => //=.
 by auto => /> H0 H32; apply asubwrite_set256 => /#.
(* 0 < lEN < 32: an optional low u128, then the rest via __a_ilen_write_upto16 *)
seq 2: (0 < _len < 32 /\ offset = _off
        /\ ((16 <= _len /\ asubwrite _buf buf _off (take 16 (u256bytes _w)) _dlt _len dELTA lEN
             /\ t128 = VEXTRACTI128 _w (W8.of_int 1))
         \/ (_len < 16 /\ buf = _buf /\ dELTA = _dlt /\ lEN = _len /\ t128 = truncateu128 _w))).
 seq 1: (#pre /\ t128 = truncateu128 w); first by auto.
 if => //.
  auto => /> H0 H32 H16; split; first smt().
  have Hm: asubwrite _buf (A.init (WA.get8 (WA.set128_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) (truncateu128 _w))))
             _off (take 16 (u256bytes _w)) _dlt _len (_dlt + 16) (_len - 16).
   by rewrite take16_u256bytes; apply asubwrite_set128 => /#.
  by left.
 by auto => /> /#.
ecall (a_ilen_write_upto16_h buf offset dELTA lEN t128).
auto => |> &m H0 H32 Hc [b2 d2 l2] /= H2.
case: Hc => [[H16 [H Ht]]|[H16 [Hb [Hd [Hl Ht]]]]].
 move: H2; rewrite Ht => H2.
 have := asubwrite_cat _ _ _ _ _ _ _ _ _ _ _ _ H H2.
 by rewrite take16_u256bytes -u256bytes_split.
move: H2; rewrite Hb Hd Hl Ht -take16_u256bytes => H2.
by apply (asubwrite_untake _ _ _ _ 16 _ _ _ _ _ _ H2) => /#.
qed.

phoare a_ilen_write_upto32_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u256bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto32_ll (a_ilen_write_upto32_h _buf _off _dlt _len _w). qed.

lemma a_rlen_read_upto8_ll: islossless MM.__a_rlen_read_upto8
by islossless.

equiv a_rlen_ilen_read_eq:
 MM.__a_rlen_read_upto8 ~ MM.__a_ilen_read_upto8_at
 : a{1} = buf{2} /\ off{1} = dELTA{2} /\ offset{2} = 0 /\ len{1} = lEN{2}
   /\ tRAIL{2} = 0 /\ cUR{2} = 0 /\ aT{2} = 0 /\ 0 <= len{1}
 ==> res.`1{1} = res.`1{2} /\ res.`2{1} = res.`5{2}.
proof.
proc; inline *; case: (8 <= len{1}).
+ rcondt{1} 1; first by auto.
  rcondf{2} 1; first by auto => /#.
  rcondt{2} 1; first by auto => /#.
  by rcondf{2} 4; [auto | auto => />].
rcondf{1} 1; first by auto.
wp; skip => /> &2 H0 H1.
have T1 : (TEST_64 (W64.of_int lEN{2}) W64.one).`5 = (lEN{2} %/ 1 %% 2 = 0).
+ by rewrite -(test64_zf lEN{2} 1) /#.
rewrite T1 (test64_zf lEN{2} 4) 1,2:/# (test64_zf lEN{2} 2) 1,2:/#.
have : lEN{2} \in iota_ 0 8 by rewrite mem_iota /#.
rewrite -iotaredE /=.
case => [->|]; first by move=> /=; circuit.
move: (WA.get32_direct (WA.init8 (A."_.[_]" buf{2})) dELTA{2})
      (WA.get16_direct (WA.init8 (A."_.[_]" buf{2})) dELTA{2})
      (WA.get16_direct (WA.init8 (A."_.[_]" buf{2})) (dELTA{2} + 4))
      (WA.get8 (WA.init8 (A."_.[_]" buf{2})) dELTA{2})
      (WA.get8 (WA.init8 (A."_.[_]" buf{2})) (dELTA{2} + 2))
      (WA.get8 (WA.init8 (A."_.[_]" buf{2})) (dELTA{2} + 4))
      (WA.get8 (WA.init8 (A."_.[_]" buf{2})) (dELTA{2} + 6)) => a32 b0 b4 c0 c2 c4 c6.
have M16 : W8.of_int 16 `&` W8.of_int 63 = W8.of_int 16 by circuit.
have M32 : W8.of_int 32 `&` W8.of_int 63 = W8.of_int 32 by circuit.
have M48 : W8.of_int 48 `&` W8.of_int 63 = W8.of_int 48 by circuit.
rewrite M16 M32 M48; clear M16 M32 M48 T1 H0 H1.
rewrite !(shl8_mulE _ 16) // !(shl8_mulE _ 32) // !(shl8_mulE _ 48) // /=.
by do 6! (case => [->|] /=; first by circuit); move=> -> /=; circuit.
qed.

hoare a_rlen_read_upto8_h _buf _off _len:
 MM.__a_rlen_read_upto8
 : a=_buf /\ off=_off /\ len=_len /\ 0 <= _off /\ 0 <= _len /\ _off + _len <= _ASIZE
 ==> srspec (u64bytes res.`2) 0 0 (sub _buf _off _len) _len 0
     /\ res.`1 = _off + min 8 (max 0 _len).
proof.
case: (0 <= _off /\ 0 <= _len /\ _off + _len <= _ASIZE) => [[H0 [H1 H2]] | H]; last first.
+ by conseq (: false ==> _) => //.
conseq a_rlen_ilen_read_eq (a_ilen_read_upto8_at_h _buf 0 _off _len 0 0 0).
+ by move=> &1 [#] -> -> -> _; exists (_buf, 0, _off, _len, 0, 0, 0).
move=> &1 &2 [#] -> ->; rewrite /asubread /= => [#] Hs _ -> _ _.
by split; [exact (Hs _) | rewrite size_to_list /srincr /#].
qed.

phoare a_rlen_read_upto8_ph _buf _off _len:
 [ MM.__a_rlen_read_upto8
 : a=_buf /\ off=_off /\ len=_len /\ 0 <= _off /\ 0 <= _len /\ _off + _len <= _ASIZE
 ==> srspec (u64bytes res.`2) 0 0 (sub _buf _off _len) _len 0
     /\ res.`1 = _off + min 8 (max 0 _len)
 ] = 1%r.
proof. by conseq a_rlen_read_upto8_ll (a_rlen_read_upto8_h _buf _off _len). qed.

lemma a_rlen_write_upto8_ll: islossless MM.__a_rlen_write_upto8
by islossless.

equiv a_rlen_ilen_write_eq:
 MM.__a_rlen_write_upto8 ~ MM.__a_ilen_write_upto8
 : buf{1} = buf{2} /\ off{1} = dELTA{2} /\ offset{2} = 0 /\ len{1} = lEN{2}
   /\ data{1} = w{2} /\ 0 <= len{1}
 ==> res.`1{1} = res.`1{2} /\ res.`2{1} = res.`2{2}.
proof.
proc; case: (8 <= len{1}).
+ by rcondt{1} 1; [auto | rcondt{2} 1; [auto => /# | rcondt{2} 1; [auto => /# | auto => />]]].
rcondf{1} 1; first by auto.
seq 1 0 : (buf{1} = buf{2} /\ off{1} = dELTA{2} /\ offset{2} = 0 /\ len{1} = lEN{2}
           /\ data{1} = w{2} /\ 0 <= len{1} < 8 /\ zf{1} = (len{1} %/ 4 %% 2 = 0)).
+ by auto => /> &2 H0 H1; rewrite (test64_zf lEN{2} 4) /#.
case: (len{1} = 0).
+ rcondf{2} 1; first by auto => /#.
  rcondf{1} 1; first by auto => /#.
  rcondf{1} 2; first by auto => /> &2 *; rewrite (test64_zf 0 2).
  rcondf{1} 3; first by auto => /> &2 *; have /= := test64_zf 0 1.
  by auto.
rcondt{2} 1; first by auto => /#.
rcondf{2} 1; first by auto => /#.
seq 1 1 : (buf{1} = buf{2} /\ off{1} = dELTA{2} /\ offset{2} = 0 /\ lEN{2} = len{1} %% 4
           /\ data{1} = w{2} /\ 0 < len{1} < 8).
+ by if; [move=> /> /# | auto => /> /# | auto => /> /#].
seq 2 1 : (buf{1} = buf{2} /\ off{1} = dELTA{2} /\ offset{2} = 0 /\ lEN{2} = len{1} %% 2
           /\ data{1} = w{2} /\ 0 < len{1} < 8).
+ seq 1 0 : (#pre /\ zf{1} = (len{1} %/ 2 %% 2 = 0)).
  + by auto => /> &1 &2 *; rewrite (test64_zf len{1} 2) /#.
  by if; [move=> /> /# | auto => /> /# | auto => /> /#].
seq 1 0 : (#pre /\ zf{1} = (len{1} %/ 1 %% 2 = 0)).
+ by auto => /> &1 &2 *; rewrite -(test64_zf len{1} 1) /#.
by if; [move=> /> /# | auto => /> /# | auto => /> /#].
qed.

hoare a_rlen_write_upto8_h _buf _off _w _len:
 MM.__a_rlen_write_upto8
 : buf=_buf /\ off=_off /\ len=_len /\ data = _w /\ 0 <= _len
 ==> res.`1 = A.fill (fun i => (u64bytes _w).[i-_off]) _off (min 8 (max 0 _len)) _buf
     /\ res.`2 = _off + min 8 (max 0 _len).
proof.
conseq a_rlen_ilen_write_eq (a_ilen_write_upto8_h _buf 0 _off _len _w).
+ by move=> &1 [#] -> -> -> -> H; exists (_buf, 0, _off, _len, _w).
by move=> &1 &2 [#] -> ->; rewrite /asubwrite size_to_list /= => [#] -> -> _.
qed.

phoare a_rlen_write_upto8_ph _buf _off _w _len:
 [ MM.__a_rlen_write_upto8
 : buf=_buf /\ off=_off /\ len=_len /\ data = _w /\ 0 <= _len
 ==> res.`1 = A.fill (fun i => (u64bytes _w).[i-_off]) _off (min 8 (max 0 _len)) _buf
     /\ res.`2 = _off + min 8 (max 0 _len)
 ] = 1%r.
proof. by conseq a_rlen_write_upto8_ll (a_rlen_write_upto8_h _buf _off _w _len). qed.

(*
lemma subread_specP N buf off dlt len trail cur at dlt' at' w':
 0 <= N =>
 cur <= at =>
 subread_pre cur at off dlt len trail =>
 subread_spec N buf off dlt len trail cur at dlt' 0 0 at' w' =>
 at' = at + len + b2i (trail<>0)
 /\
 dlt' = dlt + len
 /\
 bytes2state (nseq at W8.zero ++ sub buf (off+dlt) len ++ [W8.of_int trail])
 = bytes2state (nseq cur W8.zero++w').
proof.
move=> Hn Hcur Hpre Hspec.
move: (Hpre) (Hspec Hn Hpre) => {Hspec} /> ?????????? H1 H2 H3 H4 H5.
rewrite !b2i0 /= => H6 H7 H8.
split; first smt().
rewrite tP => i Hi.
rewrite !initiE //= !nth_w64L_from_bytes 1..2:/#.
congr; apply W8u8.Pack.ext_eq => k Hk.
rewrite !get_of_list //.
rewrite eq_sym !nth_take 1..4:/# !nth_drop 1..4:/# -catA nth_cat 1:size_nseq ?Eat.
case: (8 * i + k < max 0 cur) => Ccur //.
 rewrite nth_cat ?size_nseq ifT 1:/#.
 by rewrite !nth_nseq_if /#.
rewrite eq_sym nth_cat size_nseq /=.
case: (8*i+k < max 0 at) => C1.
 by rewrite nth_nseq_if nth_bytes_at /#.
have ->: max 0 at = at by smt().
have ->: max 0 cur = cur by smt().
case: (len=0) => C2.
 by rewrite C2 nth_bytes_at 1..2:/# sub0 /#.
rewrite nth_bytes_at 1:/# 1:/#.
case: (0 <= at - cur <= 8 * i + k - cur < N) => ?.
 smt().
rewrite nth_cat ?size_sub 1:/#.
case: (8 * i + k - at < len) => ? //.
 by rewrite nth_out /#.
smt().
qed.

lemma bytes_at_absorb _buf _off _len _tb _at:
 0 <= _len => 0 <= _at =>
 bytes2state (nseq _at W8.zero ++ A.sub _buf _off _len ++ [W8.of_int _tb]) =
 bytes2state (bytes_at 200 0 _at (sub _buf _off _len ++ [W8.of_int _tb])).
proof.
move => *.
rewrite /bytes_at drop0 /_statebytes -!bytes2stbytesP.
apply stbytes_inj.
rewrite !stwordsK tP => i Hi.
rewrite !get_of_list 1..2:// nth_take 1..2:/# eq_sym nth_cat.
rewrite !size_cat !size_nseq !size_sub 1:/# /= lez_maxr 1:/# addzA catA.
case: (i < _at + _len+1) => C//.
 rewrite eq_sym nth_out.
 by rewrite !size_cat !size_nseq !size_sub 1:/# /= lez_maxr 1:/# /#.
by rewrite nth_nseq 1:/#.
qed.


lemma subread_full buf off dlt len tb at dlt' len' tb' at' wl:
 subread_pre 0 at off dlt len tb => 
 subread_spec 200 buf off dlt len tb 0 at dlt' len' tb' at' wl =>
 at+len+b2i (tb<>0) <= 200 =>
 len' = 0 /\ tb' = 0
 /\ at'=at+len+b2i(tb<>0) /\ dlt'=len+dlt
 /\ bytes2state (u8zeros at ++ sub buf (off+dlt) len ++ [W8.of_int tb])
    = bytes2state wl.
proof.
move=> Hpre Hspec.
move: (Hspec _ Hpre) => //.
move: Hpre => /= Hpre [#] Hpre' -> /= *.
do (split; first smt()).
by rewrite bytes_at_absorb 1..2:/#.
qed.


lemma subread_finished size buf off dlt len tb at dlt' len' tb' at' wl:
 0 <= size =>
 subread_pre 0 at off dlt len tb => 
 subread_spec size buf off dlt len tb 0 at dlt' len' tb' at' wl =>
 len' = 0 =>
 tb' = 0 =>
 at'= max at (at+len+b2i(tb<>0)) /\ dlt'=len+dlt
 /\ bytes2state (u8zeros at ++ sub buf (off+dlt) len ++ [W8.of_int tb])
    = bytes2state wl.
proof.
move=> Hsize Hpre Hspec Hlen' Htb'.
move: (Hspec Hsize Hpre).
move: Hpre => /= Hpre [#] Hpre' -> /= *.
do (split; first smt()).
case: (len=0 /\ tb=0) => C.
 rewrite -!bytes2stbytesP; apply stbytes_inj; rewrite !stwordsK tP => i Hi.
 rewrite !get_of_list 1..2:// nth_bytes_at 1..2:/#.
 by move: C => [-> ->]; rewrite sub0 cats0 /= -nseq1 cat_nseq 1..2:/# nth_nseq_if /#.
have: at+len+b2i(tb<>0) <= size by smt().
move=> C'.
rewrite -!bytes2stbytesP; apply stbytes_inj; rewrite !stwordsK tP => i Hi.
rewrite !get_of_list 1..2:// nth_bytes_at 1..2:/# /=.
case: (0 <= at <= i < size) => Ci.
 by rewrite -!catA nth_cat size_nseq ifF /#.
move: Ci. rewrite andaE negb_and (:0 <= at) 1:/# /= => [[Ci1|Ci2]].
 by rewrite -catA nth_cat size_nseq ifT 1:/# nth_nseq_if /#.
rewrite nth_cat size_cat size_nseq size_sub 1:/# ifF 1:/#.
case: (tb=0) => Ctb.
 by rewrite Ctb /#.
by rewrite ifF /#.
qed.
*)


(*
lemma fill_le0 f off len (buf: W8.t A.t):
 len <= 0 =>
 fill f off len buf = buf.
proof.
move=> H; rewrite fillE tP => i Hi.
by rewrite initiE //= ifF 1:/#.
qed.
*)

end ReadWriteArray.
