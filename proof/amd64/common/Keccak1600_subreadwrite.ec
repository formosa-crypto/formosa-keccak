require import AllCore IntDiv List StdOrder.

require import BitEncoding.
import BS2Int.
import IntOrder.

from Jasmin require import JModel_x86.
from CryptoSpecs require import Keccak1600_Spec.
from JazzEC require import Keccak1600_Jazz.

require import Keccak_bindings.

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


lemma get_u256bytes i w:
 (u256bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 32) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

lemma get_u128bytes i w:
 (u128bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 16) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

lemma get_u64bytes i w:
 (u64bytes w).[i] = w \bits8 i.
proof.
case: (0 <= i < 8) => Hi.
 by rewrite nth_to_list.
rewrite bits8E nth_out ?size_to_list //.
apply W8.ext_eq => k Hk.
by rewrite zerowE initiE //= get_out /#.
qed.

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

lemma u128bytes_cat (w0 w1: W128.t):
 u128bytes w0 ++ u128bytes w1
 = u256bytes (VINSERTI128 (zeroextu256 w0) w1 W8.one).
proof.
by rewrite /VINSERTI128 to_uint1 /= /u128bytes /u256bytes /= zeroextu256E.
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
 by rewrite /VPSLL_4u64 of_uintK modz_small /#.
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

lemma srspec_shl tb w cur at l len:
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
apply srspec_shl => //; first smt().
by apply loadW64_memread; smt().
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
 wp; ecall (SHLDQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 admit (*by apply (subread_u128 _buf _off _dlt _len _trail _cur _at _).
msubread Glob.mem{`&hr}
  (u128bytes (loadW128 Glob.mem{`&hr} _buf `<<<` 8 * (_at - _cur))) _cur _at
  _buf _len _tb (_cur + 16) (_buf + (16 - (_at - _cur)))
  (_len - (16 - (_at - _cur))) _tb
*).
(* lEN < 16 *)
if => //.
 (* CUR+8 <= AT *)
 wp; ecall(m_ilen_read_upto8_at_h buf lEN tRAIL (cUR+8) aT); auto => |>.
 rewrite !negb_or negb_and => |> &m ???????? [dlt0 len0 tb0 at0 w0] /= H.
admit (*
_: ! _len < 0
_: ! _at < _cur
_: ! _cur + 16 < _at
_: _cur + 16 <> _at
_: _len <> 0 \/ _tb <> 0
_: ! 16 < _len
_: 16 <> _len
_: _cur + 8 <= _at
dlt0: int
len0: int
tb0: int
at0: int
w0: W64.t
H: msubread Glob.mem{m} (u64bytes w0) (_cur + 8) _at _buf _len _tb at0 dlt0
     len0 tb0
------------------------------------------------------------------------
msubread Glob.mem{m} (u128bytes (VPINSR_2u64 zero w0 one)) _cur _at _buf _len
  _tb at0 dlt0 len0 tb0
*).
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
admit(* by apply subread_u256.
_: 32 <= _len
------------------------------------------------------------------------
msubread Glob.mem{m} (u256bytes (loadW256 Glob.mem{m} _buf)) _cur _cur _buf
  _len _tb (_cur + 32) (_buf + 32) (_len - 32) _tb
*).
(* lEN < 16 *)
if => //.
 (* CUR+16 <= AT *)
 wp; ecall(m_ilen_read_upto16_at_h buf lEN tRAIL (cUR+16) aT); auto => |>.
 rewrite !negb_or negb_and => |> ???????? [dlt0 len0 tb0 at0 w0] /= H.
admit(*
w0: W128.t
H: msubread Glob.mem{`&hr} (u128bytes w0) (_cur + 16) _at _buf _len _tb at0
     dlt0 len0 tb0
------------------------------------------------------------------------
msubread Glob.mem{`&hr} (u256bytes (VINSERTI128 zero w0 one)) _cur _at _buf
  _len _tb at0 dlt0 len0 tb0
*).
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

lemma trunc_zext_u64_u128 w:
 truncateu64 (W2u64.zeroextu128 w) = w.
proof. by circuit. qed.

lemma trunc_VMOV_64 w:
 truncateu64 (VMOV_64 w) = w.
proof. by circuit. qed.

equiv m_ilen_read_bcast_upto8_at_eq:
 M.__m_ilen_read_bcast_upto8_at
 ~ M.__m_ilen_read_upto8_at
 : ={arg, Glob.mem}
 ==> (res.`1,res.`2,res.`3,res.`4,res.`5){1}
     = (res.`1,res.`2,res.`3,res.`4,VPBROADCAST_4u64 (truncateu64 (zeroextu128 res.`5))){2}.
proof.
proc; simplify.
if => //=.
 auto => />.
 by move=> *; clear; circuit.
sp; if => //=.
 inline*; auto => /> &m *; split.
  move=> *.
  rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
  by rewrite /W64.(`<<`) trunc_zext_u64_u128 of_uintK modz_small 1:/# of_uintK modz_small /#.
 move=> *.
 rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
 by rewrite /W64.(`<<`) trunc_zext_u64_u128 1:/# of_uintK modz_small /#.
inline *.
rcondf {1} 6; first by auto.
rcondf {1} 6; first by auto.
wp 10 4.
conseq (: ={Glob.mem,buf,aT,cUR,lEN,tRAIL} ==> ={w,aT,cUR,buf,lEN,tRAIL}) => //.
 move=> /> &2 H at w.
 rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=.
 by rewrite trunc_zext_u64_u128 trunc_VMOV_64.
by sim.
qed.

lemma m_rlen_read_upto8_ll: islossless M.__m_rlen_read_upto8
by islossless.

hoare m_rlen_read_upto8_h _buf _len:
 M.__m_rlen_read_upto8
 : buf=_buf /\ len=_len
 ==> srspec (u64bytes res.`2) 0 0 (memread Glob.mem _buf _len) _len 0.
proof.
proc; simplify.
admitted.

phoare m_rlen_read_upto8_ph _buf _len:
 [ M.__m_rlen_read_upto8
 : buf=_buf /\ len=_len
 ==> srspec (u64bytes res.`2) 0 0 (memread Glob.mem _buf _len) _len 0
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
 admit (* storeW64 _m _buf _w = stores _m _buf (u64bytes _w) *).
admitted.

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
admitted.

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
admitted.

phoare m_ilen_write_upto32_ph (_m: global_mem_t) _buf _len _w:
 [ M.__m_ilen_write_upto32
 : _m=Glob.mem /\ buf=_buf /\ lEN=_len /\ w = _w
 ==> msubwrite _m Glob.mem (u256bytes _w) _buf _len res.`1 res.`2
 ] = 1%r.
proof. by conseq m_ilen_write_upto32_ll (m_ilen_write_upto32_h _m _buf _len _w). qed.

lemma m_rlen_write_upto8_ll: islossless M.__m_rlen_write_upto8
by islossless.

hoare m_rlen_write_upto8_h _m _buf _w _len:
 M.__m_rlen_write_upto8
 : _m=Glob.mem /\ buf=_buf /\ len=_len /\ data = _w
 ==> Glob.mem = stores _m _buf (take _len (u64bytes _w))
     /\ res = _buf + min 8 (max 0 _len).
proof.
proc; simplify.
admitted.

phoare m_rlen_write_upto8_ph _m _buf _w _len:
 [ M.__m_rlen_write_upto8
 : _m=Glob.mem /\ buf=_buf /\ len=_len /\ data = _w
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

(* Some auxiliary lemmata *)

lemma sub0 (buf: W8.t A.t) off:
 sub buf off 0 = [].
proof. by rewrite -size_eq0 size_sub /#. qed.


lemma size_sub' ['a] (buf:'a A.t) k len:
 size (sub buf k len) = max 0 len.
proof.
case: (0<=len) => H.
 by rewrite size_sub /#.
by rewrite /sub mkseq0_le /#.
qed.

lemma drop_sub (buf: W8.t A.t) off len sz cur at:
 0 <= sz =>
 drop (srincr sz cur at len) (sub buf off len)
 = sub buf (off+srincr sz cur at len) (len-srincr sz cur at len).
proof.
move=> Hsz; apply (eq_from_nth W8.zero).
rewrite size_drop' /srincr !size_sub' 1:/#.
rewrite size_drop' size_sub' => i Hi.
rewrite nth_sub /srl' 1:/# nth_drop; 1..2: smt(size_ge0).
by rewrite nth_sub; smt(size_ge0).
qed.



(***************************************
      ARRAY reads/writes
****************************************)


op asubread (buf:W8.t A.t) off lw (cur at dlt len tb at2 dlt2 len2 tb2: int) =
 srspec lw cur at (sub buf (off+dlt) len) len tb
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
  by apply absurd => _; rewrite /srpre size_sub' /#.
+ split; last smt().
  by move=> Hpre; rewrite size_nseq; smt(nth_u8zeros).
+ rewrite ler_maxr; first smt(size_ge0).
  move=> H; split; last smt().
  move=> Hpre; split.
   by rewrite srpre_next; smt(size_ge0).
  rewrite u8prefAbsorbP => i; rewrite size_nseq size_sub' nth_u8zeros.
  case: (0 <= i < size lw) => C; last smt().
  by rewrite nth_out /#.
split; last smt().
by move=> ?; rewrite sub0 size_nseq; smt(size_ge0 nth_u8zeros).
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
move => Hpre; move:(Hpre).
have Hl: sub buf (off + dlt1) len1 = srl (size lw1) cur at (sub buf (off + dlt) len).
 smt(size_ge0 drop_sub). 
by apply (srspec_cat lw1 lw2 cur at (sub buf (off + dlt) len) len tb) => // /#.
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
 0 <= _off+_dlt =>
 _off + _dlt + 8 <= _ASIZE =>
 8 <= _len =>
 0 <= _at-_cur < 8 =>
 asubread _buf _off (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))) _cur _at
            _dlt _len _tb (_cur + 8) (_dlt + (_cur + 8 - _at)) (_len - (_cur + 8 - _at)) _tb.
proof.
move=> Hoff0 Hoff1 Hlen Hat; rewrite /asubread; split; last first.
 by rewrite size_to_list; smt(size_sub).
move=> Hpre; move: (Hpre).
apply srspec_shl => //; first smt().
by apply getW64_bytearray. 
qed.


(*
lemma loadW32_memread m buf len:
 4 <= len =>
 u8prefAt (u32bytes (loadW32 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 4) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u32bytes loadW32_bits8 // ler_maxr // size_to_list C /=.
by rewrite /loadW8 nth_mkseq 1:/#.
qed.
*)

(*
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
*)

(*
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
*)

(*
lemma loadW16_memread m buf len:
 2 <= len =>
 u8prefAt (u16bytes (loadW16 m buf)) 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 2) => C; last first.
 by rewrite nth_out size_to_list 1:/# ifF /#.
rewrite get_u16bytes ler_maxr // size_to_list C /=.
by rewrite /loadW16 W2u8.pack2bE // initiE // nth_mkseq /#. 
qed.
*)

(*
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
*)

(*
lemma loadW8_memread m buf len:
 1 <= len =>
 u8prefAt [loadW8 m buf] 0 (memread m buf len).
proof.
move=> Hlen i; case: (0 <= i < 1) => C; last first.
 by rewrite ifF /#.
rewrite ifT 1:/# ler_maxr //= C /=.
by rewrite /loadW8 nth_mkseq /#. 
qed.
*)

(*
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
*)

(*
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
*)



op asubwrite (a a2: W8.t A.t) off lw (dlt len:int) dlt2 len2 =
 a2 = A.fill (fun i => lw.[i-off+dlt]) (off+dlt) len a
 /\ dlt2 = dlt + min (size lw) (max 0 len)
 /\ len2 = len - min (size lw) (max 0 len).

lemma asubwrite_cat a a1 a2 off lw1 lw2 dlt len dlt1 len1 dlt2 len2:
 asubwrite a a1 off lw1 dlt len dlt1 len1 =>
 asubwrite a1 a2 off lw2 dlt1 len1 dlt2 len2 =>
 asubwrite a a2 off (lw1++lw2) dlt len dlt2 len2.
proof.
move=> />; split; last smt(size_ge0 size_cat).
rewrite !fillE tP => i Hi; rewrite !initiE //= initiE //=.
case: (off + dlt <= i < off + dlt + len) => C; last first.
 by rewrite ifF; first smt(size_ge0).
rewrite nth_cat.
case: (i - off + dlt < size lw1) => C1.
 rewrite ifF //.
 admit.
rewrite ifT //.
 admit.
congr.
admit.
qed.


module MM = {
  proc __a_ilen_read_upto8_at (buf:W8.t A.t, offset:int, dELTA:int,
                               lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if ((((lEN < 0) \/ (aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
    if ((((lEN < 0) \/ (aT < cUR) \/ ((cUR + 16) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
          w <- (zeroextu128 t64_0);
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
    if ((((lEN < 0) \/ (aT < cUR) \/ ((cUR + 32) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
    var aT8:int;
    var w:W64.t;
    var t128:W128.t;
    if ((((lEN < 0) \/ (aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        aT8 <- (aT - cUR);
        w256 <-
        (VPBROADCAST_4u64
        (get64_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ M.__SHLQ_256 (w256, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT <- (cUR + 8);
      } else {
        aT8 <- (aT - cUR);
        (dELTA, lEN, tRAIL, aT, w) <@ __a_ilen_read_upto8_at (buf, offset,
        dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (zeroextu128 w);
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
        t64 <- (truncateu64 w);
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
  proc __a_rlen_read_upto8_noninline (a:W8.t A.t, off_:int, len_:int) : 
  int * W64.t = {
    var w:W64.t;
    var zf:bool;
    var sh:W8.t;
    var x:W64.t;
    var off:int;
    var len:int;
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
    off <- off_;
    len <- len_;
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
    off_ <- off;
    return (off_, w);
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
 apply asubread_u64. smt().
asubread _buf _off
  (u64bytes
     (get64_direct (init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))) _cur _at _dlt _len _tb (_cur + 8)
  (_dlt + (_cur + 8 - _at)) (_len - (_cur + 8 - _at)) _tb
*).
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
admit(*  by apply msubread_u32.
asubread _buf _off
  (u64bytes
     (zeroextu64 (get32_direct (init8 ("_.[_]" _buf)) (_off + _dlt)) `<<<`
      8 * (_at - _cur))) _cur _at _dlt 4 0 (_at + min (_cur + 8 - _at) 4)
  (_dlt + min (_cur + 8 - _at) 4) (4 - min (_cur + 8 - _at) 4) 0
*).
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
  wp; ecall (SHLQ_h t16 (aT-cUR)); auto => |> ?????? H1??.
  split; first smt().
  move=> ??; split; last smt().
  rewrite -!addzA.
  have ->: (n0 + if _cur + 8 <= _at + (n0 + 2) then _cur + (8 - (_at + n0)) else 2)=n1 by smt().
  have ->: (if _cur + 8 <= _at + (n0 + 2) then _cur + 8 else _at + (n0 + 2))=_at+n1 by smt().
  rewrite (addzA _at).
admit (*  by apply (msubread_w4_w2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
H1: asubread _buf _off (u64bytes w{`&hr}) _cur _at _dlt (_len %/ 4 * 4) 0
      (_at + n0) (_dlt + n0) (_len %/ 4 * 4 - n0) 0
_: _at + n0 < _cur + 8
_: 2 <= _len - n0
_: 0 <= _at + n0 - _cur
_: _at + n0 - _cur < 8
------------------------------------------------------------------------
asubread _buf _off
  (u64bytes
     (w{`&hr} `|`
      (zeroextu64 (get16_direct (init8 ("_.[_]" _buf)) (_off + (_dlt + n0))) `<<<`
       8 * (_at + n0 - _cur)))) _cur _at _dlt (_len %/ 2 * 2) 0 (_at + n1)
  (_dlt + n1) (_len %/ 2 * 2 - n1) 0
*).
 auto => |> ??????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En0: n0 = _cur+8-_at by smt().
 have En1: n1 = n0 by smt().
 split; last smt().
 rewrite En1 {3}En0.
admit (* by apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
H: asubread _buf _off (u64bytes w{`&hr}) _cur _at _dlt (_len %/ 4 * 4) 0
     (_at + n0) (_dlt + n0) (_len %/ 4 * 4 - n0) 0
_: ! _at + n0 < _cur + 8
En0: n0 = _cur + 8 - _at
En1: n1 = n0
------------------------------------------------------------------------
asubread _buf _off (u64bytes w{`&hr}) _cur _at _dlt (_len %/ 2 * 2) 0
  (_at + n0) (_dlt + n0) (_len %/ 2 * 2 - (_cur + 8 - _at)) 0
*).
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
admit(*  by apply (msubread_w2_w1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
H1: asubread _buf _off (u64bytes w{`&hr}) _cur _at _dlt (_len %/ 2 * 2) 0
      (_at + n1) (_dlt + n1) (_len %/ 2 * 2 - n1) 0
_: _at + n1 < _cur + 8
_: 1 <= _len - n1
_: 0 <= _at + n1 - _cur
_: _at + n1 - _cur < 8
------------------------------------------------------------------------
asubread _buf _off
  (u64bytes
     (w{`&hr} `|`
      (zeroextu64 (get8 (init8 ("_.[_]" _buf)) (_off + (_dlt + n1))) `<<<`
       8 * (_at + n1 - _cur)))) _cur _at _dlt _len 0 (_at + n2) (_dlt + n2)
  (_len - n2) 0
*).
 auto => |> &m ?????H.
 rewrite negb_and; move => [?|?]; last smt().
 have En1: n1 = _cur+8-_at by smt().
 have En2: n2 = n1 by smt().
 split; last smt().
 rewrite En2 {3}En1.
admit(* by apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
H: asubread _buf _off (u64bytes w{m}) _cur _at _dlt (_len %/ 2 * 2) 0
     (_at + n1) (_dlt + n1) (_len %/ 2 * 2 - n1) 0
_: ! _at + n1 < _cur + 8
En1: n1 = _cur + 8 - _at
En2: n2 = n1
------------------------------------------------------------------------
asubread _buf _off (u64bytes w{m}) _cur _at _dlt _len 0 (_at + n1)
  (_dlt + n1) (_len - (_cur + 8 - _at)) 0
*).
if => //.
 auto => |> &m ?????H??.
 have ->: 1 = b2i (_tb<>0) by smt().
admit(* by apply msubread_tb; smt().
H: asubread _buf _off (u64bytes w{m}) _cur _at _dlt _len 0 (_at + n2)
     (_dlt + n2) (_len - n2) 0
_: _at + n2 < _cur + 8
_: _tb <> 0
------------------------------------------------------------------------
asubread _buf _off
  (u64bytes
     (w{m} `|` (of_int (_tb %% 256) `<<` of_int (8 * (_at + n2 - _cur)))))
  _cur _at _dlt _len _tb (_at + n2 + b2i (_tb <> 0)) (_dlt + n2) (_len - n2)
  0
*).
auto => |> &m ?????H; rewrite negb_and => [[C|C]]; last smt().
have {3}->: n2 =  _cur + 8 - _at by smt().
admit(* apply (msubread_ahead _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); smt().
H: asubread _buf _off (u64bytes w{m}) _cur _at _dlt _len 0 (_at + n2)
     (_dlt + n2) (_len - n2) 0
C: ! _at + n2 < _cur + 8
------------------------------------------------------------------------
asubread _buf _off (u64bytes w{m}) _cur _at _dlt _len _tb (_at + n2)
  (_dlt + n2) (_len - (_cur + 8 - _at)) _tb
*).
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
admitted(*
proc; simplify.

if => //.
 auto => |> H.
 apply asubread0.
  admit.
 by rewrite size_to_list /#.

(* 16 <= lEN *)
if => //.
 wp; ecall (SHLDQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 admit (*by apply (subread_u128 _buf _off _dlt _len _trail _cur _at _).*).

(* lEN < 16 *)
if => //.
 (* CUR+8 <= AT *)
 wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT); auto => |>.
 rewrite !negb_or negb_and => |> ????????; split; first smt().
 move=> _ [dlt0 len0 tb0 at0 w0] /= H.
admit (*
 have H0:= subread_spec_ahead8 _buf _off _dlt _len _trail _cur _at _;first  smt().
 rewrite -zeroextu128_zero -u64bytes_cat.
 by apply (subread_spec_cat 8 8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).*).

wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT).
wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL cUR aT).
auto => |>; rewrite !negb_or negb_and. 
move => |>*; split; first smt().
move => _ []dlt0 len0 tb0 at0 w0 |> H0.
split; first smt().
move=> _ []dlt1 len1 tb1 at1  w2 /= H1.
rewrite -u64bytes_cat.
by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).
qed.
*).

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
  admit.
 by rewrite size_to_list /#.

(* 32 <= lEN *)
sp; if => //.
 auto => |> ??.
admit(* by apply subread_u256.*).

(* lEN < 16 *)
if => //.
 (* CUR+16 <= AT *)
 wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL (cUR+16) aT); auto => |>.
 rewrite !negb_or negb_and => |> ??????? [dlt0 len0 tb0 at0 w0] /= H.
admit(*
 have H0:= subread_spec_ahead16 _buf _off _dlt _len _trail _cur _at _;first  smt().
 rewrite -zeroextu256_zero -u128bytes_cat.
 by apply (subread_spec_cat 16 16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0) => //.*).
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
     = (res.`1,res.`2,res.`3,res.`4,VPBROADCAST_4u64 (truncateu64 (zeroextu128 res.`5))){2}.
proof.
proc; simplify.
if => //=.
 auto => />.
 by move=> *; clear; circuit.
sp; if => //=.
 inline*; auto => /> &m *; split.
  move=> *.
admit(*
  rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
  by rewrite /W64.(`<<`) trunc_zext_u64_u128 of_uintK modz_small 1:/# of_uintK modz_small /#.
*).
 move=> *.
admit(*
 rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr => />.
 by rewrite /W64.(`<<`) trunc_zext_u64_u128 1:/# of_uintK modz_small /#.*).
inline *.
rcondf {1} 9; first by auto.
rcondf {1} 9; first by auto.
wp 13 4.
conseq (: ={buf,offset,dELTA,aT,cUR,lEN,tRAIL} ==> ={w,aT,cUR,buf,offset,dELTA,lEN,tRAIL}) => //.
by sim.
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
 auto => /> Hlen.
admitted.

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
 auto => /> Hlen.
admitted.

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
 auto => /> Hlen.
admitted.

phoare a_ilen_write_upto32_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u256bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto32_ll (a_ilen_write_upto32_h _buf _off _dlt _len _w). qed.

lemma a_rlen_read_upto8_ll: islossless MM.__a_rlen_read_upto8
by islossless.

hoare a_rlen_read_upto8_h _buf _off _len:
 MM.__a_rlen_read_upto8
 : a=_buf /\ off=_off /\ len=_len
 ==> srspec (u64bytes res.`2) 0 0 (sub _buf _off _len) _len 0.
proof.
proc. simplify.
admitted.

phoare a_rlen_read_upto8_ph _buf _off _len:
 [ MM.__a_rlen_read_upto8
 : a=_buf /\ off=_off /\ len=_len
 ==> srspec (u64bytes res.`2) 0 0 (sub _buf _off _len) _len 0
 ] = 1%r.
proof. by conseq a_rlen_read_upto8_ll (a_rlen_read_upto8_h _buf _off _len). qed.

lemma a_rlen_write_upto8_ll: islossless MM.__a_rlen_write_upto8
by islossless.

hoare a_rlen_write_upto8_h _buf _off _w _len:
 MM.__a_rlen_write_upto8
 : buf=_buf /\ off=_off /\ len=_len /\ data = _w
 ==> res.`1 = A.fill (fun i => (u64bytes _w).[i-_off]) _off _len _buf
     /\ res.`2 = _off +  min 8 (max 0 _len).
proof.
proc; simplify.
admitted.

phoare a_rlen_write_upto8_ph _buf _off _w _len:
 [ MM.__a_rlen_write_upto8
 : buf=_buf /\ off=_off /\ len=_len /\ data = _w
 ==> res.`1 = A.fill (fun i => (u64bytes _w).[i-_off]) _off _len _buf
     /\ res.`2 = _off +  min 8 (max 0 _len)
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


lemma subread_spec_ahead8 _buf _off _dlt _len _tb _cur _at:
 _cur + 8 <= _at =>
 subread_spec 8 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u64bytes W64.zero).
proof.
move => H; rewrite /subread_spec => _ Hpre; split; first by smt().
split; last smt().
apply (eq_from_nth W8.zero); rewrite size_to_list.
 by rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at // ifF 1:/#.
by rewrite nth_to_list W8u8.get_zero.
qed.

lemma subread_spec_ahead16 _buf _off _dlt _len _tb _cur _at:
 _cur + 16 <= _at =>
 subread_spec 16 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u128bytes W128.zero).
proof.
move => H; rewrite /subread_spec => _ Hpre; split; first by smt().
split; last smt().
apply (eq_from_nth W8.zero); rewrite size_to_list.
 by rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at // ifF 1:/#.
by rewrite nth_to_list W16u8.get_zero.
qed.

lemma subread_spec_ahead32 _buf _off _dlt _len _tb _cur _at:
 _cur + 32 <= _at =>
 subread_spec 32 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u256bytes W256.zero).
proof.
move => H; rewrite /subread_spec => _ Hpre; split; first by smt().
split; last smt().
apply (eq_from_nth W8.zero); rewrite size_to_list.
 by rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at 1..2:/# ifF 1:/#.
by rewrite nth_to_list W32u8.get_zero.
qed.

lemma subread_spec_empty8 _buf _off _dlt _len _tb _cur _at:
 _len <= 0 /\ _tb = 0 =>
 subread_spec 8 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u64bytes W64.zero).
proof.
move => [Hlen ->]; rewrite /subread_spec /u64bytes /= !b2i0 /= => Hpre; split; first by smt().
have ->: _len=0 by smt().
split; last smt().
apply (eq_from_nth W8.zero).
 rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at 1..2:/#.
case: (0 <= _at - _cur <= i < 8) => C//.
by rewrite nth_cat ?size_sub 1:/# sub0 /=.
qed.

lemma subread_spec_empty16 _buf _off _dlt _len _tb _cur _at:
 _len <= 0 /\ _tb = 0 =>
 subread_spec 16 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u128bytes W128.zero).
proof.
move => [Hlen ->]; rewrite /subread_spec /u128bytes /= !b2i0 /= => Hpre; split; first by smt().
have ->: _len=0 by smt().
split; last smt().
apply (eq_from_nth W8.zero).
 by rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at 1..2:/# /=.
case: (0 <= _at - _cur <= i < 16) => C//.
by rewrite nth_cat ?size_sub 1:/# sub0 /=.
qed.

lemma subread_spec_empty32 _buf _off _dlt _len _tb _cur _at:
 _len <= 0 /\ _tb = 0 =>
 subread_spec 32 _buf _off _dlt _len _tb _cur _at _dlt _len _tb _at (u256bytes W256.zero).
proof.
move => [Hlen ->]; rewrite /subread_spec /u256bytes /= !b2i0 /= => Hpre; split; first by smt().
have ->: _len=0 by smt().
split; last smt().
apply (eq_from_nth W8.zero).
 by rewrite size_bytes_at /#.
move=> i Hi; rewrite nth_bytes_at 1..2:/# /=. 
case: (0 <= _at - _cur <= i < 32) => C//.
by rewrite nth_cat ?size_sub 1:/# sub0 /=.
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

lemma get8_bytes (buf: W8.t A.t) off:
 0 <= off < _ASIZE =>
 get8_direct (WA.init8 ("_.[_]" buf)) off
 = buf.[off].
proof. by move=> Hoff; rewrite /get8 initiE. qed.


lemma bits8_shl_get64 buf off k i:
 0 <= off =>
 0 <= k < 8 =>
 0 <= i < 8 =>
 off + 8 <= _ASIZE =>
 get64_direct (WA.init8 (A."_.[_]" buf)) off `<<<` 8 * k \bits8 i
 = if i < k then W8.zero else buf.[off+i-k].
proof.
move=> ????; rewrite bits8_u64_shl8 1:// get64_bytes 1..2:/#.
case: (i<k) => // C.
by rewrite nth_sub /#.
qed.

*)
(*
lemma subread_u128 _buf _off _dlt _len _trail _cur _at:
 16 <= _len =>
 0 <= _at-_cur < 16 =>
 subread_spec 16 _buf _off _dlt _len _trail _cur _at
  (_dlt + (16 - (_at - _cur))) (_len - (16 - (_at - _cur))) _trail (_cur + 16)
  (u128bytes
     (get128_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))).
proof.
move=> Hen Hcur _ Hpre; split; first smt().
split; last smt().
apply (eq_from_nth W8.zero).
 rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
 by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
move=> i; rewrite size_to_list => Hi.
rewrite nth_bytes_at //.
rewrite get_u128bytes bits8_u128_shl8 //.
case: (_at-_cur <= i) => C.
 by rewrite ifF 1:/# ifT 1:/# nth_cat size_sub 1:/# ifT 1:/# nth_sub 1:/# get128_bytes 1..2:/# nth_sub /#.
by rewrite ifT 1:/# ifF 1:/#.
qed.

lemma subread_u64 _buf _off _dlt _len _trail _cur _at:
 8 <= _len =>
 0 <= _at-_cur < 8 =>
 subread_spec 8 _buf _off _dlt _len _trail _cur _at (_dlt + (_cur + 8 - _at))
  (_len - (_cur + 8 - _at)) _trail (_cur + 8)
  (u64bytes
     (get64_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt) `<<<`
      8 * (_at - _cur))).
proof.
move=> Hen Hcur _ Hpre; split; first smt().
split; last smt().
apply (eq_from_nth W8.zero).
 rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
 by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
move=> i; rewrite size_to_list => Hi.
rewrite nth_bytes_at //.
rewrite get_u64bytes bits8_u64_shl8 //.
case: (_at-_cur <= i) => C.
 by rewrite ifF 1:/# ifT 1:/# nth_cat size_sub 1:/# ifT 1:/# nth_sub 1:/# get64_bytes 1..2:/# nth_sub /#.
by rewrite ifT 1:/# ifF 1:/#.
qed.

lemma subread_u32 n _buf _off _dlt _cur _at :
 0 <= _at-_cur < 8 =>
 n = min (_cur + 8 - _at) 4 =>
 subread_spec 8 _buf _off _dlt 4 0 _cur
   _at (_dlt+n) (4-n) 0 (_at+n)
   (u64bytes (zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)) `<<<`
      8 * (_at - _cur))).
proof.
move=> Hen Hcur _ Hpre; split; first smt().
split; last smt().
apply (eq_from_nth W8.zero).
 rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
 by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
move=> i; rewrite size_to_list => Hi.
rewrite nth_bytes_at //.
rewrite get_u64bytes bits8_u64_shl8 //.
case: (_at-_cur <= i) => C //=.
 rewrite ifF 1:/# ifT 1:/# nth_cat size_sub 1:/# bits8_zeroextu64_32.
 rewrite (:i - (_at - _cur)=_cur + i - _at) 1:/#; case: (0<= _cur + i - _at < 4) => ? //.
  by rewrite get32_bytes /#.
 case: (_cur + i - _at < 4) => // ?.
 by rewrite nth_sub /#.
by rewrite ifT 1:/#.
qed.

lemma u64bits8_subread i buf off cur dlt len tb at dlt1 len1 tb1 at1 (w:W64.t):
 subread_pre cur at off dlt len tb =>
 subread_spec 8 buf off dlt len tb cur at dlt1 len1 tb1 at1 (u64bytes w) =>
 w \bits8 i
 = (bytes_at 8 cur at (sub buf (off + dlt) len++[of_int tb])).[i].
proof.
move=> Hpre H; move: (H _ Hpre) => // |> ?E???.
by rewrite -get_u64bytes E.
qed.

lemma subread_w4_u16 n1 buf off cur dlt len at dlt1 len1 at1 w:
 0 <= len < 8 =>
 2 <= len%%4 =>
 0 <= at-cur < 8 =>
 at+n1 = min (cur+8) (at+len%/4*4+2) =>
 subread_spec 8 buf off dlt (len%/4*4) 0 cur at
   dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt (len%/2*2) 0 cur at
   (dlt+n1) (len%/2*2-n1) 0 (at+n1)
   (u64bytes
     (w `|`
      (zeroextu64
         (get16_direct (WA.init8 ("_.[_]" buf)) (off + dlt1)) `<<<` 8*(at1-cur)))).
proof.
move=> Hlen Hlen2 Hcur Hat H _ Hpre; split; first smt().
have Hpre': subread_pre cur at off dlt (len %/ 4 * 4) 0 by smt().
split.
 apply (eq_from_nth W8.zero).
  rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
  by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
 move=> i; rewrite size_to_list => Hi.
 rewrite get_u64bytes orb8E bits8_u64_shl8 //.
 rewrite (u64bits8_subread _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre' H).
 rewrite bits8_zeroextu64_16 !nth_bytes_at // get16_bytes 1..2:/#.
 case: (0 <= at - cur <= i < 8) => ?.
  case: (i < at1 - cur) => ?.
   by rewrite orw0 !nth_cat !size_sub 1..2:/# /= !ifT 1..2:/# !nth_sub /#.
  case: (0 <= i - (at1 - cur) < 2) => ?.
   rewrite nth_sub 1:/# !nth_cat !size_sub 1..2:/# ifF 1:/# ifT 1:/# /=.
   by rewrite nth_sub /#.
  by rewrite orw0 !nth_cat !size_sub 1..2:/# ifF 1:/# ifF 1:/#.
 rewrite or0w; case: (i < at1-cur) => ? //.
 case: (0 <= i - (at1 - cur) < 2) => ? //.
 by rewrite nth_sub /#.
smt().
qed.

lemma subread_w4_ahead buf off cur dlt len at dlt1 len1 at1 w:
 0 <= len < 8 =>
 0 <= at-cur < 8 =>
 at1 = cur+8 =>
 subread_spec 8 buf off dlt (len%/4*4) 0 cur at
   dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt (len%/2*2) 0 cur at
   dlt1 (len%/2*2-(cur+8-at)) 0 at1 (u64bytes w).
proof.
move=> Hlen Hcur Hat H _ Hpre; split; first smt().
split.
 move: (H _ _); 1..2:smt().
 move => |> _ -> ??.
 apply (eq_from_nth W8.zero); rewrite !size_bytes_at // => k Hk.
 rewrite !nth_bytes_at //; first smt().
 case: (0 <= at - cur <= k < 8) => ?//.
 rewrite !nth_cat !size_sub 1..2:/#.
 case: (cur + k - at < len %/ 4 * 4) => ?.
  by rewrite ifT 1:/# !nth_sub /#.
 by rewrite ifF 1:/#.
smt().
qed.

lemma subread_w2_u8 n2 buf off cur dlt len at dlt1 len1 at1 w:
 0 <= len < 8 =>
 1 <= len%%2 =>
 0 <= at1-cur < 8 =>
 at+n2 = at+len =>
 subread_spec 8 buf off dlt (len%/2*2) 0 cur at
   dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt len 0 cur at
   (dlt+n2) (len-n2) 0 (at+n2)
   (u64bytes
     (w `|`
      (zeroextu64
         (get8_direct (WA.init8 ("_.[_]" buf)) (off + dlt1)) `<<<` 8*(at1-cur)))).
proof.
move=> Hlen Hlen2 Hcur Hat H _ Hpre; split; first smt().
have Hpre': subread_pre cur at off dlt (len %/ 2 * 2) 0 by smt().
split.
 apply (eq_from_nth W8.zero).
  rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
  by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
 move=> i; rewrite size_to_list => Hi.
 rewrite get_u64bytes orb8E bits8_u64_shl8 //.
 rewrite (u64bits8_subread _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre' H).
 rewrite bits8_zeroextu64_8 !nth_bytes_at // get8_bytes 1:/#.
 case: (0 <= at - cur <= i < 8) => ?.
  case: (i < at1 - cur) => ?.
   by rewrite orw0 !nth_cat !size_sub 1..2:/# /= !ifT 1..2:/# !nth_sub /#.
  case: (i = (at1 - cur)) => ?.
   rewrite !nth_cat !size_sub 1..2:/# ifF 1:/# ifT 1:/# /=.
   by rewrite nth_sub /#.
  by rewrite ifF 1:/# orw0 !nth_cat !size_sub 1..2:/# ifF 1:/# ifF 1:/#.
 rewrite or0w; case: (i < at1-cur) => ? //.
 by rewrite ifF 1:/#.
smt().
qed.

lemma subread_w2_ahead buf off cur dlt len at dlt1 len1 at1 w:
 0 <= len < 8 =>
 0 <= at-cur < 8 =>
 at1 = cur+8 =>
 subread_spec 8 buf off dlt (len%/2*2) 0 cur at
   dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt len 0 cur at
   dlt1 (len-(cur+8-at)) 0 at1 (u64bytes w).
proof.
move=> Hlen Hcur Hat H _ Hpre; split; first smt().
split.
 move: (H _ _); 1..2:smt().
 move => |> _ -> ??.
 apply (eq_from_nth W8.zero); rewrite !size_bytes_at // => k Hk.
 rewrite !nth_bytes_at //; first smt().
 case: (0 <= at - cur <= k < 8) => ?//.
 rewrite !nth_cat !size_sub 1..2:/#.
 case: (cur + k - at < len %/ 2 * 2) => ?.
  by rewrite ifT 1:/# !nth_sub /#.
 by rewrite ifF 1:/#.
smt().
qed.

lemma subread_w8_trail buf off cur dlt len trail at dlt1 len1 at1 w:
 trail <> 0 =>
 0 <= len < 8 =>
 0 <= at-cur < 8 =>
 at1 < cur+8 =>
 subread_spec 8 buf off dlt len 0 cur at dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt len trail cur at dlt1 len1 0 (at1+1)
   (u64bytes
     (w `|` (W64.of_int (trail %% 256) `<<` W8.of_int (8 * (at1 - cur))))).
proof.
move=> Htb Hlen Hlen2 Hat H _ Hpre.
have Hpre': subread_pre cur at off dlt len 0 by smt().
move: (H _ Hpre') => // /> ????????E??.
split; first smt().
split.
 apply (eq_from_nth W8.zero); rewrite size_to_list ?size_bytes_at // => k Hk.
 rewrite b2i0 /=.
 rewrite get_u64bytes orb8E -get_u64bytes E !nth_bytes_at //.
 case: (0 <= at - cur <= k < 8) => ?; last first.
  rewrite or0w bits8E; apply W8.ext_eq => j Hj /=.
  rewrite initiE //= /(`<<`) of_uintK (modz_small _ W8.modulus) 1:/# /=.
  by rewrite (:0 <= k * 8 + j < 64) 1:/# /= of_intwE /#.
 rewrite !nth_cat size_sub 1:/#.
 case: (cur + k - at < len) => C.
  rewrite bits8E /=; pose W:= W8.init _.
  have ->: W = W8.zero.
   apply W8.ext_eq => j Hj; rewrite zerowE /W initiE /(`<<`) //=.
   by rewrite of_intwE /#.
  by rewrite orw0.
 rewrite or0w.
 rewrite /(`<<`) bits8E; apply W8.ext_eq => j Hj /=.
 rewrite initiE //=.
 have ->: forall n, (W64.of_int (trail %% 256)).[n] = (W8.of_int trail).[n].
  move=> n; case: (0 <= n < 8) => ?.
   by rewrite !of_intwE (:trail%%256=trail) 1:/# /W64.int_bit /W8.int_bit /#.
  case: (0 <= n < 64) => ?.
   rewrite W8.get_out 1:/# of_intwE /W64.int_bit.
   rewrite (:trail %% 256 %% W64.modulus = trail) 1:/#.
   have ?: 8 <= n < 64 by smt().
   rewrite divz_small; split; first smt().
   move=> _. apply (ltr_le_trans W8.modulus); first smt().
   rewrite ger0_norm; first smt(expr_ge0).
   by apply ler_weexpn2l => /#.
  by rewrite !get_out /#.
 case: (cur + k - at - len = 0) => ?.
  smt().
 by rewrite zerowE get_out /#.
smt().
qed.

lemma subread_w8_trail_ahead buf off cur dlt len trail at dlt1 len1 at1 w:
 0 <= len < 8 =>
 0 <= at-cur < 8 =>
 at1 = cur+8 =>
 subread_spec 8 buf off dlt len 0 cur at dlt1 len1 0 at1 (u64bytes w) =>
 subread_spec 8 buf off dlt len trail cur at dlt1 len1 trail at1 (u64bytes w).
proof.
move=> Hlen Hcur Hat H _ Hpre; split; first smt().
split.
 move: (H _ _); 1..2:smt().
 move => |> _ -> ??.
 apply (eq_from_nth W8.zero); rewrite !size_bytes_at // => k Hk.
 rewrite !nth_bytes_at //; first smt().
 case: (0 <= at - cur <= k < 8) => ?//.
 by rewrite !nth_cat !size_sub /#.
smt().
qed.
*)

(*
lemma a_ilen_read_upto8_at_h _buf _off _dlt _len _trail _cur _at:
 (* 0 <= _len => *)
 hoare [
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5) ].
proof.
case: (_len < 0) => Hlen.
 conseq (:_ ==> true) => //.
 by move => /> /#.
proc; simplify.

if => //.
 auto => |> [[H|H]|H]. 
 + move=> _; rewrite /subread_pre => /> ?????????.
   rewrite (:!_cur<=_at) 1:/# /= => [[Elen Etb]].
   rewrite !Elen !Etb; split; first smt().
   split.
    by rewrite sub0 bytes_at_zeros 1:/# /u64bytes /= !get_zero -mkseq_nseq /mkseq -iotaredE. 
   smt().
  + by apply subread_spec_ahead8; smt().
  by apply subread_spec_empty8; smt().

sp; if => //.
 (* 8 <= lEN *)
 wp; ecall (SHLQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 by apply subread_u64.

conseq (: _cur <= _at < _cur+8 /\ _len < 8 /\ (_len<>0 \/ _trail<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur /\ tRAIL=_trail
         /\ dELTA=_dlt /\ lEN=_len /\ aT=_at==> _).
 by move => /> /#.

pose n0 := min (_cur + 8 - _at) (_len %/ 4 * 4).
seq 1: ( #[:7]pre
       /\ subread_spec 8 _buf _off _dlt (_len %/ 4 * 4) 0 _cur _at dELTA (_len %/ 4 * 4-n0) 0 aT (u64bytes w)
       /\ dELTA = _dlt+n0 /\ lEN = _len - n0 /\ aT=_at+n0).
 if => //.
  (* 4 <= lEN  *)
  wp; ecall (SHLQ_h w (aT-cUR)); auto => /> *.
  split; first smt().
  move=> ??.
  rewrite /n0.
  have ->: _len %/ 4 * 4 = 4 by smt().
  have ->: (_dlt + if _cur + 8 <= _at + 4 then _cur + 8 - _at else 4)
          = _dlt + min (_cur+8-_at) 4 by smt().
  have ->: (if _cur + 8 <= _at + 4 then _cur + 8 else _at + 4)
          = _at + min (_cur+8-_at) 4 by smt().
  split.
   by apply (subread_u32 (min (_cur+8-_at) 4) _buf _off _dlt _cur _at _ _); smt().
  smt().
 auto => /> ?????.
 rewrite /n0.
 have ->: _len%/4*4 = 0 by smt().
 rewrite ler_minr 1:/# /=.
 by apply subread_spec_empty8.

pose n1 := min (_cur+8-_at) (_len %/ 2 * 2).
exlim aT => at1; exlim lEN => len1; exlim dELTA => dlt1.
conseq (: _cur <= _at < _cur+8 /\ _len < 8 /\ (_len<>0 \/ _trail<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur
         /\ tRAIL=_trail /\ dELTA=dlt1 /\ lEN=len1 /\ aT=at1
         /\ subread_spec 8 _buf _off _dlt (_len%/4*4) 0 _cur
             _at dlt1 (_len %/ 4 * 4 - n0) 0 at1 (u64bytes w)
         /\ dlt1=_dlt+n0 /\ len1=_len-n0 /\ at1=_at+n0
         ==> _).
 by move => />. 

seq 1: ( #[/:8]pre
/\ subread_spec 8 _buf _off _dlt (_len %/ 2 * 2) 0 _cur
    _at dELTA (_len%/2*2-n1) 0 aT (u64bytes w) 
/\ dELTA=_dlt+n1 /\ lEN=_len-n1 /\ aT=_at+n1).
 if => //.
  (* 2 <= lEN *)
  wp; ecall (SHLQ_h t16 (aT-cUR)); auto => /> ????? H1??.
  split; first smt(). 
  move=> ??; split.
   rewrite -!addzA.
   have ->: (n0 + if _cur + 8 <= _at + (n0 + 2) then _cur + (8 - (_at + n0)) else 2)=n1 by smt().
   have ->: (if _cur + 8 <= _at + (n0 + 2) then _cur + 8 else _at + (n0 + 2))=_at+n1 by smt().
   rewrite (addzA _at).
   by apply (subread_w4_u16 n1 _buf _off _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
  smt().
 auto => /> &m ????H.
 rewrite negb_and; move => [?|?].
  have En0: n0 = _cur+8-_at by smt().
  have En1: n1 = n0 by smt().
  split.
   rewrite En1 {2}En0.
   by apply (subread_w4_ahead _buf _off _ _ _ _ _ _ _ _ _ _ _ H); smt().
  smt().
 have ->: (_len %/ 2 * 2) = (_len %/ 4 * 4) by smt().
 have ->: n1 = n0 by smt().
 split; first smt().
 smt(). 

pose n2 := min (_cur+8-_at) _len.
exlim aT => at2; exlim lEN => len2; exlim dELTA => dlt2.
conseq (: _cur <= _at < _cur+8 /\ _len < 8 /\ (_len<>0 \/ _trail<>0) 
         /\ buf=_buf /\ offset=_off /\ cUR=_cur
         /\ tRAIL=_trail /\ dELTA=dlt2 /\ lEN=len2 /\ aT=at2
         /\ subread_spec 8 _buf _off _dlt (_len%/2*2) 0 _cur
             _at dlt2 (_len %/ 2 * 2 - n1) 0 at2 (u64bytes w)
         /\ dlt2=_dlt+n1 /\ len2=_len-n1 /\ at2=_at+n1
         ==> _).
 by move => />. 

seq 1: ( #[/:8]pre
       /\ subread_spec 8 _buf _off _dlt _len 0 _cur
                         _at dELTA (_len-n2) 0 aT (u64bytes w) 
       /\ dELTA=_dlt+n2 /\ lEN=_len-n2 /\ aT=_at+n2).
 if => //.
  (* 1 <= lEN *)
  wp; ecall (SHLQ_h t8 (aT-cUR)); auto => /> ????? H1??.
  split; first smt(). 
  move=> ??; split.
   rewrite -!addzA.
   have ->: n1+1=n2 by smt().
   rewrite (addzA _at).
   by apply (subread_w2_u8 n2 _buf _off _ _ _ _ _ _ _ _ _ _ _ _ H1); smt().
  smt().
 auto => /> &m ????H.
 rewrite negb_and; move => [?|?].
  have En1: n1 = _cur+8-_at by smt().
  have En2: n2 = n1 by smt().
  split.
   rewrite En2 {2}En1.
   by apply (subread_w2_ahead _buf _off _ _ _ _ _ _ _ _ _ _ _ H); smt().
  smt().
 have ->: _len = _len %/ 2 * 2 by smt().
 have ->: n2 = n1 by smt().
 split; first smt().
 smt(). 

if => //.
 auto => /> &m ????H??.
 by apply subread_w8_trail => /#.
auto => /> &m ????H; rewrite negb_and => [[C|C]].
 by apply subread_w8_trail_ahead => /#.
smt().
qed.


hoare a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5).
proof.
proc; simplify.

if => //.
 auto => |>  [[H|H]|H]. 
 + move=> _; rewrite /subread_pre => /> ?????????.
   rewrite (:!_cur<=_at) 1:/# /= => [[Elen Etb]].
   rewrite !Elen !Etb; split; first smt().
   split.
    rewrite sub0 bytes_at_zeros 1:/# /u128bytes /= !get_zero.
    by rewrite -mkseq_nseq /mkseq -iotaredE.
   smt().
  + by apply subread_spec_ahead16; smt().
  by apply subread_spec_empty16; smt().

(* 16 <= lEN *)
if => //.
 wp; ecall (SHLDQ_h w (aT-cUR)); auto => |> *.
 split; first smt().
 move=> ??.
 by apply (subread_u128 _buf _off _dlt _len _trail _cur _at _).

(* lEN < 16 *)
if => //.
 (* CUR+8 <= AT *)
 wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT); auto => |>.
 rewrite !negb_or negb_and => |> ??????? [dlt0 len0 tb0 at0 w0] /= H.
 have H0:= subread_spec_ahead8 _buf _off _dlt _len _trail _cur _at _;first  smt().
 rewrite -zeroextu128_zero -u64bytes_cat.
 by apply (subread_spec_cat 8 8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).

wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL (cUR+8) aT).
wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL cUR aT).
auto => |>.
rewrite !negb_or negb_and. 
move => ???[]dlt0 len0 tb0 at0 w0 |> H0 []dlt1 len1 tb1 at1 w1 /= H1.
rewrite -u64bytes_cat.
by apply (subread_spec_cat 8 8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0).
qed.

phoare a_ilen_read_upto16_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto16_at_ll
          (a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at).
qed.

lemma subread_u256 _buf _off _dlt _len _trail _cur _at:
 32 <= _len =>
 _at-_cur = 0 =>
 subread_spec 32 _buf _off _dlt _len _trail _cur _at
  (_dlt + 32) (_len - 32) _trail (_at + 32)
  (u256bytes
     (get256_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt))).
proof.
move=> Hen Hcur _ Hpre; split; first smt().
split; last smt().
apply (eq_from_nth W8.zero).
 rewrite size_to_list size_take // size_cat size_nseq ler_maxr //=.
 by rewrite size_drop 1:/# !size_cat size_sub 1:/# size_nseq /= /#.
move=> i; rewrite size_to_list => Hi.
rewrite nth_bytes_at 1..2:/#.
rewrite get_u256bytes get256E pack32bE // initiE //= initiE 1:/#.
by rewrite ifT 1:/# nth_cat size_sub 1:/# ifT 1:/# nth_sub /#.
qed.

hoare a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5).
proof.
proc; simplify.

if => //.
 auto => |> [[H|H]|H]. 
 + move=> _; rewrite /subread_pre => /> ?????????.
   rewrite (:!_cur<=_at) 1:/# /= => [[Elen Etb]].
   rewrite !Elen !Etb; split; first smt().
   split.
    rewrite sub0 bytes_at_zeros /u256bytes 1:/# /= !get_zero.
    by rewrite -mkseq_nseq /mkseq -iotaredE.
   smt().
  + by apply subread_spec_ahead32; smt().
  by apply subread_spec_empty32; smt().

(* 32 <= lEN *)
sp; if => //.
 auto => |> ??.
 by apply subread_u256.

(* lEN < 16 *)
if => //.
 (* CUR+16 <= AT *)
 wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL (cUR+16) aT); auto => |>.
 rewrite !negb_or negb_and => |> ?????? [dlt0 len0 tb0 at0 w0] /= H.
 have H0:= subread_spec_ahead16 _buf _off _dlt _len _trail _cur _at _;first  smt().
 rewrite -zeroextu256_zero -u128bytes_cat.
 by apply (subread_spec_cat 16 16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0) => //.
wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL (cUR+16) aT).
wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL cUR aT).
auto => |>.
rewrite !negb_or negb_and. 
move => ???[]dlt0 len0 tb0 at0 w0 |> H0 []dlt1 len1 tb1 at1 w1 /= H1.
rewrite -u128bytes_cat.
by apply (subread_spec_cat 16 16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 _).
qed.

phoare a_ilen_read_upto32_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto32_at
   : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off+ _dlt /\ _off + _dlt + _len <= _ASIZE /\ 0 <= _len /\ 0 <= _trail /\
   _trail < 256 /\ _at - _cur + _len + b2i (_trail <> 0) <= 200
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto32_at_ll
          (a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at).
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

(*
op subwrite_mpre n ptr len =
 0 <= n /\ 0 <= ptr /\ 0 <= len.

op subwrite_mspec n mem ptr len l mem1 ptr1 len1 =
 subwrite_mpre n ptr len =>
 mem1 = stores mem ptr (take (min len 8) l)
 /\ ptr1 = ptr + min len 8
 /\ len1 = len - min len 8.

op subwrite_apre n off dlt len =
 0 <= n /\ 0 <= off /\ 0 <= dlt /\ 0 <= len /\ off + dlt + min len n <= _ASIZE.

op subwrite_aspec n (buf: W8.t A.t) off dlt len l buf1 dlt1 len1 =
 subwrite_apre n off dlt len =>
 buf1 = A.fill (fun i => nth W8.zero l (i-off+dlt)) (off+dlt) len buf
 /\ dlt1 = dlt + min len 8
 /\ len1 = len - min len 8.


op subread_mpre cur at ptr len tb =
 0 <= cur /\ 0 <= at /\ 0 <= ptr /\ 0 <= len /\ 0 <= tb < 256 /\
 at + len + b2i (tb<>0) <= 200 /\
 (cur <= at || len=0 /\ tb=0).

op reads len (m: global_mem_t) (a: address) = mkseq (fun i => m.[a+i]) len.

op subread_mspec
 (size: int)
 mem (ptr len tb cur at: int)
 (ptr' len' tb' at': int) (w: W8.t list)
 : bool =
 0 <= size =>
 subread_mpre cur at ptr len tb =>
 subread_pre (cur+size) at' ptr' len' tb'
 /\ w = bytes_at size cur at (reads len mem ptr) ++ [W8.of_int tb]
 /\ at+len+b2i(tb<>0)=at'+len'+b2i(tb'<>0)
 /\ (tb'=tb || len'=0 && tb'=0)
 /\ dlt+len = dlt'+len'
 /\ at' = max at
              (min (cur+size)
                   (at+len+b2i (tb<>0)))
 /\ len' = max 0 (len - (max 0 (cur+size-at))).

op subread_apre cur at off dlt len tb =
 0 <= cur /\ 0 <= at /\ 0 <= off /\ 0 <= dlt /\ 0 <= len /\ 0 <= tb < 256 /\
 off + dlt + len <= _ASIZE /\
 at + len + b2i (tb<>0) <= 200 /\
 (cur <= at || len=0 /\ tb=0).

op subread_aspec
 (size: int)
 (buf: W8.t A.t) (off dlt len tb cur at: int)
 (dlt' len' tb' at': int) (w: W8.t list)
 : bool =
 0 <= size =>
 subread_pre cur at off dlt len tb =>
 subread_pre (cur+size) at' off dlt' len' tb'
 /\ w = bytes_at size cur at (sub buf (off+dlt) len ++ [W8.of_int tb])
 /\ at+len+b2i(tb<>0)=at'+len'+b2i(tb'<>0)
 /\ (tb'=tb || len'=0 && tb'=0)
 /\ dlt+len = dlt'+len'
 /\ at' = max at
              (min (cur+size)
                   (at+len+b2i (tb<>0)))
 /\ len' = max 0 (len - (max 0 (cur+size-at))).
*)

(*
(* buf,delta,len = *)
hoare a_ilen_write_upto8_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u64bytes _w) _dlt _len res.`2 res.`3.
proof.
proc; simplify.
if => //=; last first.
 auto => /> Hlen.
 by rewrite fill_le0 1:/# size_to_list /#.
if => //.
 auto => /> _ ?; split.
 rewrite tP => i Hi.
 rewrite initiE // filliE // get8_set64_directE.
admit (* 0 <= _off+_dlt *).
admit (* 0 <= _off+_dlt <= ASIZE-8 *).
case: (_off + _dlt <= i < _off + _dlt + 8) => ?.
 rewrite ifT 1:/#.
 admit.
rewrite /get8 initiE // ifF. admit.
smt().
by rewrite size_to_list /#.

(* seq 1: ( subwrite_spec buf (off+dlt) (len%/4*4) *)
if => //.
admitted.

phoare a_ilen_write_upto8_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u64bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto8_ll (a_ilen_write_upto8_h _buf _off _dlt _len _w). qed.



hoare a_ilen_write_upto16_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u128bytes _w) _dlt _len res.`2 res.`3.
proof.
admitted.

phoare a_ilen_write_upto16_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u128bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto16_ll (a_ilen_write_upto16_h _buf _off _dlt _len _w). qed.

hoare a_ilen_write_upto32_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u256bytes _w) _dlt _len res.`2 res.`3.
proof.
admitted.

phoare a_ilen_write_upto32_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w
 ==> asubwrite _buf res.`1 _off (u256bytes _w) _dlt _len res.`2 res.`3
 ] = 1%r.
proof. by conseq a_ilen_write_upto32_ll (a_ilen_write_upto32_h _buf _off _dlt _len _w). qed.
*)



(*.
lemma sub_cat (buf: W8.t A.t) off dlt x y:
  0 <= off =>
  0 <= dlt =>
  0 <= y =>
  0 <= x =>
  y <= x =>
  sub buf (off + dlt) x =
  sub buf (off + dlt) y ++
  sub buf (off + dlt + y) (x-y).
proof.
move =>*.
  pose l1 := sub buf (off + dlt) x.
  pose l2 := sub buf (off + dlt) y ++
             sub buf (off + dlt + y) (x-y).
  rewrite (eq_from_nth witness l1 l2).
  + rewrite size_cat !size_sub /#. rewrite size_sub 1:/# => i i_bnd.
    + rewrite nth_cat size_sub 1:/# nth_sub 1:/#. 
      case(i < y) => i_small; by rewrite nth_sub /#.
   smt().
qed.

lemma aux a b c d e f:
  0 <= a =>
  0 <= b =>
  0 <= c =>
  a + b + min c f <= d =>
  0 <= e < min c f =>
    0 <= a + b + e < d.
proof.
  move => H0 H1 H2.
  case(c < f) => c_small.
  + rewrite !lez_minl 1:/# => *. split. smt(). move=> *. rewrite (ltr_le_trans (a+b+c)) /#.
  + rewrite !lez_minr 1:/# => *. split. smt(). move=> *. rewrite (ltr_le_trans (a+b+f)) /#. 
qed.
    
lemma u8_from_u64 x _w:
  0 <= x =>
  x < 8 =>
  W8.of_int (W64.to_uint _w %/ 2 ^ (8*x)) = (_w \bits8 x).
    proof.
  move => *.
  rewrite /(\bits8) (W8.ext_eq _ (W8.init(fun j=> _w.[x * 8 + j]))). move => x0 x0_bnd.
  + rewrite /of_int /to_uint bs2int_div 1:/# -(cat_take_drop 8 (drop (8*x) (w2bits _w))).
    rewrite -(bs2intD _ _ 8) 1:size_take 1:/# 1:size_drop 1:/# 1:size_w2bits 1:/#.
    rewrite dvdz_modzDr 1:/# int2bs_mod.
    have{1}->: 8 = size (take 8 (drop (8*x) (w2bits _w)))
      by rewrite size_take 1:/# size_drop 1:/# size_w2bits /#.
    rewrite bs2intK /bits2w !initE !ifT ..2:/# /= nth_take ..2:/# nth_drop ..2:/#.
    rewrite get_w2bits /#. smt().
  qed.

lemma u16_from_u64 x i _w:
  x <= i =>
  i < x+2 => 
  0 <= x =>
  x < 6 =>
  (W16.of_int (W64.to_uint _w %/ 2 ^ (8*x)) \bits8 i - x) = (_w \bits8 i).
proof.
  move => *.
  rewrite /(\bits8) (W8.ext_eq _ (W8.init(fun j=> _w.[i * 8 + j]))). move => x0 x0_bnd.
  + rewrite /of_int /to_uint bs2int_div 1:/# -(cat_take_drop 16 (drop (8*x) (w2bits _w))).
    rewrite -(bs2intD _ _ 16) 1:size_take 1:/# 1:size_drop 1:/# 1:size_w2bits 1:/#.
    rewrite !initE !ifT ..2:/# /= dvdz_modzDr 1:/# int2bs_mod.
    have{1}->: 16 = size (take 16 (drop (8*x) (w2bits _w)))
      by rewrite size_take 1:/# size_drop 1:/# size_w2bits /#.
    rewrite bs2intK /bits2w !initE ifT 1:/# /= nth_take ..2:/# nth_drop ..2:/#.
    rewrite get_w2bits /#. smt().
qed.

lemma u32_from_u64 i _w: 
  0 <= i =>
  i < 4 =>
(W32.of_int (W64.to_uint _w) \bits8 i) = (_w \bits8 i).
proof.
  move => *.
  rewrite /(\bits8) (W8.ext_eq _ (W8.init(fun j=> _w.[i * 8 + j]))). move => x0 x0_bnd.
  + rewrite /of_int /to_uint initE ifT 1:/# -(cat_take_drop 32 (w2bits _w)).
    rewrite -(bs2intD _ _ 32) 1:size_take 1:/# 1:size_w2bits 1:/# dvdz_modzDr 1:/#.
    rewrite int2bs_mod /=. have{1}->: 32 = size (take 32 (w2bits _w))
      by rewrite size_take 1:/# size_w2bits /#.
    rewrite bs2intK /bits2w !initE ifT 1:/# /= nth_take ..2:/# get_w2bits /#. smt().
qed.


op subwrite_pre (off dlt len size :int) : bool =
  0 <= off /\ 0 <= dlt /\ 0 <= len /\ 8 <= size /\ off + dlt + min len size <= _ASIZE.

op subwrite_spec
 w (size: int)
 (buf: W8.t A.t) (off dlt len: int)
 (buf': W8.t A.t) (dlt' len': int)
 : bool =
 subwrite_pre off dlt len size =>
 subwrite_pre off dlt len size /\
 sub buf' 0 (off + dlt) = 
 sub buf 0 (off + dlt) /\
 sub buf' (off + dlt) (min len size) = 
 take (min len size) (W8u8.to_list w) /\
 dlt' = dlt + min len size /\
 len' = max 0 (len - size).


lemma u64_from_u64 buf off dlt len size w:
  subwrite_pre off dlt len size =>
  sub (A.init (get8 (set64_direct (WA.init8 (A."_.[_]" buf)) (off + dlt) w))) (off + dlt)
     (min len 8) =
  take len (to_list w).
proof.
  rewrite /subwrite_pre => H0.
  + rewrite /sub /to_list -map_take /iotared take_iota minrC.
    pose f1:= (fun (i : int) => (A.init (get8 (set64_direct
                (WA.init8 ("_.[_]" buf)) (off + dlt) w))).[ off + dlt + i]).
    rewrite (eq_in_mkseq f1 (((\bits8) w))). move => i i_bnd.
    + rewrite /f1 /get8 /set64_direct initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /=.
      rewrite initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /= ifT /#. smt().
qed.

hoare a_ilen_write_upto8_at_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w /\
   subwrite_pre _off _dlt _len 8
 ==> subwrite_spec _w 8 _buf _off _dlt _len res.`1 res.`2 res.`3.
proof.
proc. if => //=; last first.
+ auto => /> *. do split; 1..4: smt(); 2..: smt().
  + have->: _len = 0 by smt(). rewrite /sub mkseq0 take0 /#.
(* 8 <= len *)
if => //=. auto => /> *. 
  + do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set8 /set64_direct initE.
      rewrite ifT 1:/# /= ifF 1:/# initE ifT /#. smt().
    rewrite (u64_from_u64 _buf _off _dlt _len 8 _w) /#.
(* 4 <= LEN < 8 *)
case( 7 <= lEN).
+ rcondt 1. auto => /#.
  rcondt 5. auto => /#.
  rcondt 9. auto => /#.
  auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set16_direct /set32_direct.
      rewrite /init8 /truncateu8 get_setE 1:/# ifF 1:/# initE ifT 1:/# initE ifT 1:/#.
      rewrite /= initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# initE ifT 1:/# initE.
      rewrite ifT 1:/# /= ifF 1:/# initE /#. smt().
  + rewrite /sub /set16_direct /to_list -map_take /iotared take_iota minrC lez_minr 1:/#.
    rewrite /truncateu16 /set32_direct /truncateu32 (eq_in_mkseq _ ((\bits8) _w)).
    move => i i_bnd /=. rewrite /get8 /init8 initE ifT 1:/# /=.
    case(i = 6) => i_max.
    + rewrite get_setE 1:/# ifT 1:/# /truncateu8 !shr_div_le ..2:/# -divzMl ..2:/#.
      have->: 2^16 * 2^32 = 2^(8 * 6) by smt(). rewrite u8_from_u64 /#.
    case(4 <= i) => i_mid.
    + rewrite get_setE 1:/# ifF 1:/# initE ifT 1:/# /= !initE !ifT ..2:/# /= ifT 1:/#.
      rewrite !opprD !addrA shr_div_le 1:/#.
      have->: _off + _dlt + i - _off - _dlt - 4 = i - 4 by smt().
      have->: W32.modulus = 2^(8*4) by smt().
      rewrite u16_from_u64 /#.
    + rewrite get_setE 1:/# ifF 1:/# initE ifT 1:/# /= !initE !ifT ..2:/# /= ifF 1:/#.
      rewrite initE ifT 1:/# initE ifT 1:/# !opprD initE.
      rewrite ifT 1:/# /= ifT 1:/#. have->: _off + _dlt + i + ((-_off) - _dlt) = i by smt().
      rewrite u32_from_u64 /#.  
    smt().
case(6 <= lEN).
+ rcondt 1. auto => /#.
  rcondt 5. auto => /#.
  rcondf 9. auto => /#.
  auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set16_direct /set32_direct.
      rewrite /init8 initE ifT 1:/# /= ifF 1:/# initE ifT 1:/# initE ifT 1:/# initE.
      rewrite ifT 1:/# /= initE ifF /#. smt().
  + rewrite /sub /set16_direct /truncateu16 /to_list -map_take /iotared take_iota minrC.
    rewrite lez_minr 1:/#/set32_direct /truncateu32 (eq_in_mkseq _ ((\bits8) _w)).
    move => i i_bnd /=. rewrite /get8 /init8 initE ifT 1:/# /=.
    case(4 <= i) => i_mid.
    + rewrite initE ifT 1:/# /= !initE ifT 1:/# !opprD !addrA shr_div_le 1:/#.
      have->: _off + _dlt + i - _off - _dlt - 4 = i - 4 by smt().
      have->: W32.modulus = 2^(8*4) by smt().
      rewrite u16_from_u64 /#.
    + rewrite initE ifT 1:/# /= !initE ifF 1:/# !ifT..3:/# !opprD /= ifT 1:/# /=.
      have->: _off + _dlt + i + ((-_off) - _dlt) = i by smt().
      rewrite u32_from_u64 /#.
    smt().
case(5 <= lEN).
+ rcondt 1. auto => /#.
  rcondf 5. auto => /#.
  rcondt 5. auto => /#.
  auto => />*. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set16_direct /set32_direct.
      rewrite /init8 get_setE 1:/# ifF 1:/# initE ifT 1:/# initE ifT 1:/# /= initE.
      rewrite ifT 1:/# /= ifF 1:/# initE /#. smt().
  + rewrite /sub /set16_direct /truncateu8 /to_list -map_take /iotared take_iota minrC.
    rewrite lez_minr 1:/#  /set32_direct /truncateu32 (eq_in_mkseq _ ((\bits8) _w)).
    move => i i_bnd /=. rewrite /get8 /init8 initE ifT 1:/# /=.
    case(4 <= i) => i_mid.
    + rewrite get_setE 1:/# ifT 1:/# shr_div_le 1:/#.
      have->: 32 = 8 * 4 by smt(). rewrite u8_from_u64 /#.
    + rewrite get_setE 1:/# ifF 1:/# initE ifT 1:/# /= !initE ifT 1:/# ifT 1:/# /= ifT 1:/#.
      have->:  _off + _dlt + i - (_off + _dlt) = i by smt().
      rewrite u32_from_u64 /#.  
    smt().
case(4 <= lEN).
  rcondt 1. auto => /#.
  rcondf 5. auto => /#.
  rcondf 5. auto => /#.
  auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set32_direct.
      rewrite /init8 initE ifT 1:/# /= ifF 1:/# initE /#. smt().
  + rewrite /sub /set32_direct /truncateu32 /to_list -map_take /iotared take_iota minrC.
    rewrite lez_minr 1:/#(eq_in_mkseq _ ((\bits8) _w)). move => i i_bnd /=.
    rewrite /get8 /init8 initE ifT 1:/# /= initE ifT 1:/# /= ifT 1:/# opprD.
    have->: _off + _dlt + i + ((-_off) - _dlt) = i by smt().
    rewrite u32_from_u64 /#.
    smt().
rcondf 1. auto => /#.
case(3 <= lEN).
  rcondt 1. auto => /#.
  rcondt 5. auto => /#.
  auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set16_direct /set32_direct.
      rewrite /init8 get_setE 1:/# ifF 1:/# initE ifT 1:/# initE ifT 1:/# /= initE.
      rewrite ifT 1:/# /= ifF 1:/# initE /#. smt().
  + rewrite /sub /set16_direct /truncateu16 /to_list -map_take /iotared take_iota minrC.
    rewrite lez_minr 1:/# /truncateu8 (eq_in_mkseq _ ((\bits8) _w)). move => i i_bnd /=.
    rewrite /get8 /init8 initE ifT 1:/# /=.
    case(2 <= i) => i_max.
    + rewrite get_setE 1:/# ifT 1:/# shr_div_le 1:/#.
      have->: 16 = 8 * 2 by smt(). rewrite u8_from_u64 /#.
    + rewrite get_setE 1:/# ifF 1:/# initE ifT 1:/# !initE !ifT ..2:/#/= ifT 1:/#.
      have->: _off + _dlt + i - (_off + _dlt) = i by smt().
      rewrite (u16_from_u64 0 i _w) /#.
    smt().
case(2 <= lEN).
  rcondt 1. auto => /#.
  rcondf 5. auto => /#.
  auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set16_direct.
      rewrite /init8 initE ifT 1:/# /= ifF 1:/# /= initE /#. smt().
  + rewrite /sub /set16_direct /truncateu16 /to_list -map_take /iotared take_iota minrC.
    rewrite lez_minr 1:/# (eq_in_mkseq _ ((\bits8) _w)). move => i i_bnd /=.
    rewrite /get8 /init8 initE ifT 1:/# /= initE ifT 1:/# /= ifT 1:/# opprD.
    have->: _off + _dlt + i + ((-_off) - _dlt) = i by smt().
    rewrite (u16_from_u64 0 i _w) /#.
    smt().
rcondf 1. auto => /#.
rcondt 1. auto => /#.
auto => /> *. do split; ..4: smt(); 3..: smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /init8 get_setE 1:/# ifF 1:/#.
      rewrite initE /#. smt().
  rewrite /sub /truncateu8 /to_list -map_take /iotared take_iota minrC lez_minr 1:/#.
  rewrite (eq_in_mkseq _ ((\bits8) _w)). move => i i_bnd /=.
  rewrite initE ifT 1:/# /get8 /init8 get_setE 1:/# ifT 1:/# (u8_from_u64 0 _w) /#.
  smt().
qed.

phoare a_ilen_write_upto8_at_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto8
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w /\
   subwrite_pre _off _dlt _len 8
 ==> subwrite_spec _w 8 _buf _off _dlt _len res.`1 res.`2 res.`3] = 1%r.
proof.
by conseq a_ilen_write_upto8_ll
          (a_ilen_write_upto8_at_h _buf _off _dlt _len _w).
qed.

op subwriteu128_spec 
  (w : W128.t) (size : int) 
  (buf : W8.t A.t) (off dlt len : int)
  (buf' : W8.t A.t) (dlt' len' : int) : bool =
  subwrite_pre off dlt len size =>
  subwrite_pre off dlt len size /\
  sub buf' 0 (off + dlt) = sub buf 0 (off + dlt) /\
  sub buf' (off + dlt) (min len size) = take len (to_list w) /\
  dlt' = dlt + min len size /\ len' = max 0 (len - size).

lemma u128_from_u128 buf off dlt len size w:
  size = 16 =>
  subwrite_pre off dlt len size =>
  sub (A.init (get8 (set128_direct (WA.init8 (A."_.[_]" buf)) (off + dlt) w))) (off + dlt)
     (min len 16) =
  take len (to_list w).
proof.
  rewrite /subwriteX_pre => H0 *.
  + rewrite /sub /to_list -map_take /iotared take_iota minrC.
    rewrite (eq_in_mkseq _ (((\bits8) w))). move => i i_bnd.
    + rewrite /get8 /set128_direct /= initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /=.
      rewrite initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /= ifT /#. smt().
qed.


lemma set_highu64 _len _w:
  take (_len - 8) (W8u8.to_list (truncateu64 (VPUNPCKH_2u64 _w _w))) =
          take (_len - 8) (drop 8 (to_list _w)).
proof.
  move => *.
  pose l1:= W8u8.to_list (truncateu64 (VPUNPCKH_2u64 _w _w)).
  pose l2:= drop 8 (W16u8.to_list _w).
  congr. rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_drop 1:/# !size_to_list /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_drop ..2:/# /l1 /to_list !nth_to_list_in ..2:/#.
    rewrite /truncateu64 /VPUNPCKH_2u64 /interleave_gen /get_hi_2u64 /=.
    rewrite /of_int /to_uint bs2int_mod 1:/#.
    have{1}->: 64 = size (take 64 (w2bits (pack2 [_w \bits64 1; _w \bits64 1]))).
      by rewrite size_take 1:/# size_w2bits /#.
    rewrite bs2intK (W8.ext_eq _ (_w \bits8 8 + i)). move => x0 x0_bnd.
  + rewrite /pack2_t /bits2w /w2bits take_mkseq 1:/# /= /(\bits8) /= initE ifT 1:/#/=.
    rewrite initE ifT 1:/# /= nth_mkseq 1:/# initE ifT 1:/# /(\bits64) /=.
    rewrite /of_list initE ifT 1:/# /= ifT 1:/# !initE !ifT /#. smt().
  smt().
qed.

lemma set_lowu64 buf off dlt len w:
  0 <= off =>
  0 <= dlt =>
  0 <= len =>
  off + dlt + 8 <= _ASIZE =>
  sub (A.init (get8 (set64_direct (WA.init8 (A."_.[_]" buf)) (off + dlt) 
  (MOVV_64 (truncateu64 w))))) (off + dlt) 8 =
  take 8 (W16u8.to_list w).
proof.
 move =>*.
 pose l1:= sub (A.init (get8 (set64_direct (WA.init8 ("_.[_]" buf)) (off + dlt) 
           (MOVV_64 (truncateu64 w))))) (off + dlt) 8.
  pose l2:= take 8 (W16u8.to_list w).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_mkseq size_take 1:/# size_to_list /#.
  + rewrite size_mkseq lez_maxr 1:/# => i i_bnd.
    rewrite nth_mkseq 1:/# /= initE ifT 1:/# /get8 /set64_direct.
    rewrite initE ifT 1:/# /= ifT 1:/# /MOVV_64 /truncateu64.
    have->: off + dlt + i - (off + dlt) = i by smt().
    rewrite nth_take ..2:/# (W8.ext_eq _ (W16u8.to_list w).[i]). move => x x_bnd.
    + rewrite nth_to_list /(\bits8) !initE !ifT ..2:/# /= /of_int /to_uint.
      rewrite bs2int_mod 1:/#. 
      have{1}->:64=size (take 64 (w2bits w))by rewrite size_take 1:/# size_w2bits /#.
      rewrite bs2intK get_bits2w 1:/# nth_take ..2:/# get_w2bits /#.
      smt().
    smt().
qed.


hoare a_ilen_write_upto16_at_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w /\
   subwrite_pre _off _dlt _len 16
 ==> subwriteu128_spec _w 16 _buf _off _dlt _len res.`1 res.`2 res.`3.
proof.
proc.
if => //=; first last.
auto => /> *. rewrite /subwrite_pre.
  do split; ..4:smt(); 2..:smt().
  + rewrite /sub /to_list -map_take /iotared take_iota minrC.
    rewrite (eq_in_mkseq _ (((\bits8) _w))) /#.
(*16 <= lEN *)
if => //=.
  auto => /> *. do split; ..4:smt(); 3..:smt().
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set8 /set128_direct initE.
      rewrite ifT 1:/# /= ifF 1:/# initE ifT /#. smt().
  rewrite (u128_from_u128 _ _ _ _ 16) /#. 
(* 8 <= lEN *)
case(8 <= lEN). 
  rcondt 1. auto => /#.
  ecall(a_ilen_write_upto8_at_h buf offset dELTA lEN t64). 
  auto => /> H0 H1 H2 H3 H4 H5 H6. split; first by smt().
  rewrite /subwrite_spec =>H7 H8 H9 H10 result _H0 _H1.
  move: _H0. rewrite /subwrite_pre H7 H8 H9 H10 implyTb !addrA=> [#]?????.
  have->: _off + _dlt + 8 - 8 = _off + _dlt by smt().
  rewrite lez_minl 1:/# => h0 h1 h2 h3.
  rewrite h2 h3. do split; ..3: smt(); 3..: smt().
  move: h0. rewrite !(sub_cat _ 0 0 (_off + _dlt + 8) (_off + _dlt)) ..10:/#.
  have->: _off + _dlt + 8 - (_off + _dlt) = 8 by smt().
  have->: 0 + 0 + (_off + _dlt) = _off + _dlt by smt().
  rewrite eqseq_cat. rewrite !size_sub /#. move => [#] h0_0 h0_1.
  rewrite h0_0.
    rewrite (eq_from_nth W8.zero _ (sub _buf 0 (_off + _dlt))).
    + rewrite !size_sub /#.
    + rewrite size_sub 1:/# => i i_bnd.
      rewrite /l1 !nth_sub ..2:/# initE ifT 1:/# /get8 /set64_direct initE ifT 1:/#.
      rewrite /= ifF 1:/# initE /#. smt().
  rewrite (sub_cat result.`1 _off _dlt (min _len 16) 8) ..5:/#.
  rewrite lez_minl 1:/# h1.
  have->: take _len (W16u8.to_list _w) =
          take 8(to_list _w) ++ take (_len-8) (drop 8 (to_list _w))
          by rewrite -drop_take /#.
  rewrite set_highu64. congr.
  move: h0. rewrite !(sub_cat _ 0 0 (_off + _dlt + 8) (_off + _dlt)) ..10:/#.
  have->: _off + _dlt + 8 - (_off + _dlt) = 8 by smt().
  have->: 0 + 0 + (_off + _dlt) = _off + _dlt by smt().
  rewrite eqseq_cat. rewrite !size_sub /#. move => [#] h0_0 h0_1. print set_lowu64.
  rewrite h0_1 (set_lowu64 _buf _off _dlt _len _w) /#.
rcondf 1. auto => /#.
 ecall(a_ilen_write_upto8_at_h buf offset dELTA lEN t64). auto => /> H0 H1 H2 H3 H4 H5 H6. 
  split; first by smt().
  rewrite /subwrite_spec =>H7 H8 H9 H10 result _H0 _H1.
  move: _H0. rewrite /subwrite_pre H7 H8 H9 H10 implyTb => [#]?????.
  have->: _off + _dlt + 8 - 8 = _off + _dlt by smt().
  rewrite !lez_minl ..2:/#. move =>  h0 h1 h2 h3.
  rewrite h2 h3. do split; ..1: smt(); 3..: smt().
  + rewrite h0 /#.
  + rewrite h1. 
    pose l1:= take _len (W8u8.to_list (truncateu64 _w)).
    pose l2:= take _len (W16u8.to_list _w).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite !size_take ..2:/# !size_to_list /#.
    + rewrite size_take 1:/# size_to_list ifT 1:/#. move => i i_bnd.
      rewrite !nth_take ..4:/# !nth_to_list /truncateu64 /of_int /to_uint bs2int_mod.
      rewrite 1:/#. have{1}->:64=size (take 64 (w2bits _w)) 
        by rewrite size_take 1:/# size_w2bits /#.
      rewrite bs2intK (W8.ext_eq _ (_w \bits8 i)). move => x x_bnd.
      + rewrite /(\bits8) !initE !ifT..2:/# /= get_bits2w 1:/# nth_take..2:/#.
        rewrite get_w2bits /#. smt().
      smt().
qed.

phoare a_ilen_write_upto16_at_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto16
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w /\
   subwrite_pre _off _dlt _len 16
 ==> subwriteu128_spec _w 16 _buf _off _dlt _len res.`1 res.`2 res.`3] = 1%r.
proof.
by conseq a_ilen_write_upto16_ll
          (a_ilen_write_upto16_at_h _buf _off _dlt _len _w).
qed.

op subwriteu256_spec (w : W256.t) (size : int) (_ : W8.t A.t) (off dlt
  len : int) (buf' : W8.t A.t) (dlt' len' : int) : bool =
  subwrite_pre off dlt len size =>
  subwrite_pre off dlt len size /\
  sub buf' (off + dlt) (min len size) = take len (to_list w) /\
  dlt' = dlt + min len size /\ len' = max 0 (len - size).


lemma u256_from_u256 buf off dlt len size w:
  size = 32 =>
  subwrite_pre off dlt len size =>
  sub (A.init (get8 (set256_direct (WA.init8 (A."_.[_]" buf)) (off + dlt) w))) (off + dlt)
     (min len 32) =
  take len (to_list w).
proof.
  rewrite /subwriteX_pre => H0 *.
  + rewrite /sub /to_list -map_take /iotared take_iota minrC.
    rewrite (eq_in_mkseq _ (((\bits8) w))). move => i i_bnd.
    + rewrite /get8 /set256_direct /= initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /=.
      rewrite initE ifT 1:(aux off dlt len _ASIZE i size) ..5:/# /= ifT /#. smt().
qed.


lemma set_highu128 _len _w:
  take (_len - 16) (W16u8.to_list (VEXTRACTI128 _w one)) =
          take (_len - 16) (drop 16 (to_list _w)).
proof.
  move => *.
  pose l1:= W16u8.to_list (VEXTRACTI128 _w one).
  pose l2:= drop 16 (W32u8.to_list _w).
  congr. rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_drop 1:/# !size_to_list /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_drop ..2:/# /l1 /to_list !nth_to_list_in ..2:/# /VEXTRACTI128.
    rewrite (W8.ext_eq _ (_w \bits8 16 + i)). move => x x_bnd.
    + rewrite /(\bits128) /(\bits8) !initE !ifT ..2:/# /= initE ifT 1:/# nth_one /=.
      rewrite b2i1 /#. smt(). 
  smt().
qed.

lemma set_lowu128 buf off dlt len w:
  0 <= off =>
  0 <= dlt =>
  0 <= len =>
  off + dlt + 16 <= _ASIZE =>
  sub (A.init (get8 (set128_direct (WA.init8 (A."_.[_]" buf)) (off + dlt) 
  (truncateu128 w)))) (off + dlt) 16 =
  take 16 (W32u8.to_list w).
proof.
 move =>*.
 pose l1:= sub (A.init (get8 (set128_direct (WA.init8 ("_.[_]" buf)) (off + dlt) 
           (truncateu128 w)))) (off + dlt) 16.
  pose l2:= take 16 (W32u8.to_list w).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_mkseq size_take 1:/# size_to_list /#.
  + rewrite size_mkseq lez_maxr 1:/# => i i_bnd.
    rewrite nth_mkseq 1:/# /= initE ifT 1:/# /get8 /set128_direct.
    rewrite initE ifT 1:/# /= ifT 1:/# /truncateu128.
    have->: off + dlt + i - (off + dlt) = i by smt().
    rewrite nth_take ..2:/# (W8.ext_eq _ (W32u8.to_list w).[i]). move => x x_bnd.
    + rewrite nth_to_list /(\bits8) !initE !ifT ..2:/# /= /of_int /to_uint.
      rewrite bs2int_mod 1:/#. 
      have{1}->:128 = size (take 128 (w2bits w))
        by rewrite size_take 1:/# size_w2bits /#.
      rewrite bs2intK get_bits2w 1:/# nth_take ..2:/# get_w2bits /#.
      smt().
    smt().
qed.

hoare a_ilen_write_upto32_at_h _buf _off _dlt _len _w:
 MM.__a_ilen_write_upto32
 : buf = _buf /\ offset = _off /\ dELTA = _dlt /\ lEN = _len /\ w = _w /\ 
   subwrite_pre _off _dlt _len 32 ==>
   subwriteu256_spec _w 32 _buf _off _dlt _len res.`1 res.`2 res.`3.
proof.
proc.
if => //=; first last.
auto => /> *. rewrite /subwrite_pre.
  do split; ..4:smt(); 2..:smt().
  + rewrite /sub /to_list -map_take /iotared take_iota minrC.
    rewrite (eq_in_mkseq _ (((\bits8) _w))) /#.
(*32 <= lEN *)
if => //=.
  auto => /> *. do split; ..4:smt();2..: smt(). 
  rewrite (u256_from_u256 _ _ _ _ 32) /#. 
sp 1.
(* 16 <= lEN *)
case(16 <= lEN). 
  rcondt 1. auto => /#.
  ecall(a_ilen_write_upto16_at_h buf offset dELTA lEN t128). 
  auto => /> H0 H1 H2 H3 H4 H5 H6. 
  split; first by smt().
  rewrite /subwriteu128_spec =>H7 H8 H9 H10 result _H0 _H1.
  move: _H0. rewrite /subwrite_pre H7 H8 H9 H10 implyTb !addrA=> [#]?????.
  have->: _off + _dlt + 8 - 8 = _off + _dlt by smt().
  rewrite lez_minl 1:/# => h0 h1 h2 h3.
  rewrite h2. do split; ..3: smt(); 2..: smt().
  rewrite (sub_cat result.`1 _off _dlt (min _len 32) 16) ..5:/# lez_minl 1:/# h1.
  have->: take _len (W32u8.to_list _w) =
          take 16 (take _len (to_list _w)) ++ take (_len-16) (drop 16 (to_list _w)).
    rewrite -drop_take 1:/# cat_take_drop /#.
  rewrite set_highu128. congr.
  move: h0. rewrite !(sub_cat _ 0 0 (_off + _dlt + 16) (_off + _dlt)) ..10:/#.
  have->: _off + _dlt + 16 - (_off + _dlt) = 16 by smt().
  have->: 0 + 0 + (_off + _dlt) = _off + _dlt by smt().
  rewrite eqseq_cat. rewrite !size_sub /#. move => [#] h0_0 h0_1.
  rewrite h0_1 take_take (set_lowu128 _buf _off _dlt _len _w) /#.
rcondf 1. auto => /#.
  ecall(a_ilen_write_upto16_at_h buf offset dELTA lEN t128). 
  auto => /> H0 H1 H2 H3 H4 H5 H6. split; first by smt().
  rewrite /subwriteu128_spec =>H7 H8 H9 H10 result _H0 _H1.
  move: _H0. rewrite /subwrite_pre H7 H8 H9 H10 implyTb => [#]?????.
  have->: _off + _dlt + 8 - 8 = _off + _dlt by smt().
  rewrite !lez_minl ..2:/#. move =>  h0 h1 h2 h3.
  rewrite h2 h3. do split; ..1: smt(); 2..: smt().
  rewrite h1.
  pose l1:= take _len (W16u8.to_list (truncateu128 _w)).
  pose l2:= take _len (W32u8.to_list _w).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite !size_take ..2:/# !size_to_list /#.
  + rewrite size_take 1:/# size_to_list ifT 1:/#. move => i i_bnd.
    rewrite !nth_take ..4:/# !nth_to_list /truncateu128 /of_int /to_uint bs2int_mod 1:/#.
    have{1}->:128 = size (take 128 (w2bits _w)) 
      by rewrite size_take 1:/# size_w2bits /#.
    rewrite bs2intK (W8.ext_eq _ (_w \bits8 i)). move => x x_bnd.
    + rewrite /(\bits8) !initE !ifT..2:/# /= get_bits2w 1:/# nth_take..2:/# get_w2bits /#.
      smt().
    smt().
qed.

phoare a_ilen_write_upto32_at_ph _buf _off _dlt _len _w:
 [ MM.__a_ilen_write_upto32
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ w = _w /\
   subwrite_pre _off _dlt _len 32
 ==> subwriteu256_spec _w 32 _buf _off _dlt _len res.`1 res.`2 res.`3] = 1%r.
proof.
by conseq a_ilen_write_upto32_ll
          (a_ilen_write_upto32_at_h _buf _off _dlt _len _w).
qed.

*)


end ReadWriteArray.
