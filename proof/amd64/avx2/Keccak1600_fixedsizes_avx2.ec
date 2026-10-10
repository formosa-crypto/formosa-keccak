(******************************************************************************
   avx2/Keccak1600_fixedsizes.ec:

   Correctness proof for the Keccak (fixed-sized) memory and array 
  absorb/squeeze AVX2 implementation

******************************************************************************)

require import AllCore List Int IntDiv StdOrder.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200.
from JazzEC require import Array7 Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.


require import Keccak1600_avx2 Keccakf1600_avx2 Avx2_extra.
require import Keccak1600_subreadwrite.

import IntOrder.


op addstate_avx2 (s1: W256.t Array7.t, s2:state): W256.t Array7.t =
 stavx2_from_st25 (addstate (stavx2_to_st25 s1) s2).

op stavx2_pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 =
 sliceset256_64_25 
  (sliceset256_64_25 
   (sliceset256_64_25 
    (sliceset256_64_25 
     (sliceset256_64_25 (init_25_64 (fun i=>W64.zero)).[0 <- w0] (8*8) w1).[5 <- w2]
     (8*48)
     w3).[10 <- w4]
    (8 * 88)
    w5).[15 <- w6]
   (8*128)
   w7).[20 <- w8]
  (8*168)
  w9.


op stavx2bytes_pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 =
u64bytes w0 ++ u256bytes w1 ++ u64bytes w2 ++
 u256bytes w3 ++ u64bytes w4 ++ u256bytes w5 ++
 u64bytes w6 ++ u256bytes w7 ++ u64bytes w8 ++
 u256bytes w9.

lemma stavx2_packE w0 w1 w2 w3 w4 w5 w6 w7 w8 w9:
 stavx2_pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9
 = bytes2state (stavx2bytes_pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9).
proof.
rewrite /bytes2state /w64L_from_bytes /chunkify.
have ->/=: size
                (u64bytes w0 ++ u256bytes w1 ++ u64bytes w2 ++
                 u256bytes w3 ++ u64bytes w4 ++ u256bytes w5 ++
                 u64bytes w6 ++ u256bytes w7 ++ u64bytes w8 ++
                 u256bytes w9) = 200.
 by rewrite !size_cat !size_to_list.
rewrite b2i0 /= /mkseq -iotaredE /stavx2bytes_pack /=.
rewrite /u64bytes /u256bytes /= !W8u8.bits8E !W32u8.bits8E /pack8_t /=.
by circuit.
qed.

phoare addstate_r3456_avx2_zero_ph _st:
 [ M.__addstate_r3456_avx2
 : st=_st /\ r3=W256.zero /\ r4=W256.zero /\ r5=W256.zero /\ r6=W256.zero
 ==> res=_st
 ] = 1%r.
proof.
proc; simplify.
seq 1: #pre => //=.
 by inline*; auto => />; circuit.
by auto => />; circuit.
by hoare; inline*; auto => />; circuit.
qed.


(* the AVX2 partial-absorb predicate is the shared one on the 25-word view *)
lemma pabsorb_spec_avx2E r8 l st:
 pabsorb_spec_avx2 r8 l st <=> stavx2INV st /\ pabsorb_spec r8 l (stavx2_to_st25 st).
proof.
rewrite /pabsorb_spec_avx2 /pabsorb_spec /PABSORB1600 /stateabsorb; split.
 by move=> [Hr ->]; rewrite stavx2INV_from_st25 stavx2_from_st25K.
by move=> [Hinv [Hr Hs]]; rewrite Hr /= -Hs stavx2_to_st25K.
qed.

(* ------------------------------------------------------------------------ *)
(* Byte view of the AVX2 state for the dump: every word __dumpstate_*_avx2  *)
(* stores is a chunk [sub (stbytes (stavx2_to_st25 st)) o n] (lane order    *)
(* restored by the blends).                                                  *)
(* ------------------------------------------------------------------------ *)

abbrev dlane (st: W256.t Array7.t) k = (stavx2_to_st25 st).[k].

(* a stored u256 holding lanes k..k+3 / a stored u64 holding lane k *)
lemma dump_avx2_lanes4 (st: W256.t Array7.t) k o w:
 0 <= k => k + 4 <= 25 => o = 8*k =>
 w = u256_pack4 (dlane st k) (dlane st (k+1)) (dlane st (k+2)) (dlane st (k+3)) =>
 u256bytes w = sub (stbytes (stavx2_to_st25 st)) o 32.
proof. by move=> ?? -> ->; rewrite sub_stbytes_4lanes // /u256bytes /u64bytes u256_pack4_to_list. qed.

lemma dump_avx2_lane (st: W256.t Array7.t) k o w:
 0 <= k < 25 => o = 8*k => w = dlane st k =>
 u64bytes w = sub (stbytes (stavx2_to_st25 st)) o 8.
proof. by move=> ? -> ->; rewrite u64bytes_stword. qed.

lemma dump_avx2_w0 (st: W256.t Array7.t):
 take 8 (u256bytes st.[0]) = sub (stbytes (stavx2_to_st25 st)) 0 8.
proof.
have /= <- := u64bytes_stword (stavx2_to_st25 st) 0 _ => //.
rewrite /stavx2_to_st25 get_of_list //=.
by rewrite /u256bytes /u64bytes /=; do! split; circuit.
qed.

lemma dump_avx2_w1 (st: W256.t Array7.t):
 u256bytes st.[1] = sub (stbytes (stavx2_to_st25 st)) 8 32.
proof.
apply (dump_avx2_lanes4 st 1) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w2 (st: W256.t Array7.t):
 u64bytes (MOVV_64 (truncateu64 (VEXTRACTI128 st.[2] (W8.of_int 1))))
 = sub (stbytes (stavx2_to_st25 st)) 40 8.
proof.
apply (dump_avx2_lane st 5) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w3 (st: W256.t Array7.t):
 u256bytes (VPBLEND_8u32 (VPBLEND_8u32 st.[3] st.[4] (W8.of_int 240))
                         (VPBLEND_8u32 st.[6] st.[5] (W8.of_int 240)) (W8.of_int 195))
 = sub (stbytes (stavx2_to_st25 st)) 48 32.
proof.
apply (dump_avx2_lanes4 st 6) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w4 (st: W256.t Array7.t):
 u64bytes (MOVV_64 (truncateu64 (truncateu128 st.[2])))
 = sub (stbytes (stavx2_to_st25 st)) 80 8.
proof.
apply (dump_avx2_lane st 10) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w5 (st: W256.t Array7.t):
 u256bytes (VPBLEND_8u32 (VPBLEND_8u32 st.[6] st.[5] (W8.of_int 240))
                         (VPBLEND_8u32 st.[4] st.[3] (W8.of_int 240)) (W8.of_int 195))
 = sub (stbytes (stavx2_to_st25 st)) 88 32.
proof.
apply (dump_avx2_lanes4 st 11) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w6 (st: W256.t Array7.t):
 u64bytes (MOVV_64 (truncateu64 (VPUNPCKH_2u64 (VEXTRACTI128 st.[2] (W8.of_int 1))
                                               (VEXTRACTI128 st.[2] (W8.of_int 1)))))
 = sub (stbytes (stavx2_to_st25 st)) 120 8.
proof.
apply (dump_avx2_lane st 15) => //.
by rewrite trunc_unpckh /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w7 (st: W256.t Array7.t):
 u256bytes (VPBLEND_8u32 (VPBLEND_8u32 st.[5] st.[6] (W8.of_int 240))
                         (VPBLEND_8u32 st.[3] st.[4] (W8.of_int 240)) (W8.of_int 195))
 = sub (stbytes (stavx2_to_st25 st)) 128 32.
proof.
apply (dump_avx2_lanes4 st 16) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w8 (st: W256.t Array7.t):
 u64bytes (MOVV_64 (truncateu64 (VPUNPCKH_2u64 (truncateu128 st.[2]) (truncateu128 st.[2]))))
 = sub (stbytes (stavx2_to_st25 st)) 160 8.
proof.
apply (dump_avx2_lane st 20) => //.
by rewrite trunc_unpckh /stavx2_to_st25 !get_of_list //=; circuit.
qed.

lemma dump_avx2_w9 (st: W256.t Array7.t):
 u256bytes (VPBLEND_8u32 (VPBLEND_8u32 st.[4] st.[3] (W8.of_int 240))
                         (VPBLEND_8u32 st.[5] st.[6] (W8.of_int 240)) (W8.of_int 195))
 = sub (stbytes (stavx2_to_st25 st)) 168 32.
proof.
apply (dump_avx2_lanes4 st 21) => //.
by rewrite /stavx2_to_st25 !get_of_list //=; circuit.
qed.

abbrev avx2bytes (st: W256.t Array7.t) = stbytes (stavx2_to_st25 st).


require import BitEncoding.
import BitChunking.


lemma srspecP lw at l len tb:
 srpre 0 at l len tb =>
 at + len + b2i (tb<>0) <= size lw =>
 srspec lw 0 at l len tb =>
 bytes2state (u8zeros at ++ l ++ [W8.of_int tb])
 = bytes2state lw.
proof.
move=> Hpre Hat H.
move: (H Hpre) => {H}[_ H].
rewrite -!bytes2stbytesP; apply stbytes_inj; rewrite !stwordsK tP => i Hi.
rewrite !get_of_list 1..2:// H ler_maxr 1:/# /=.
rewrite -catA nth_cat size_nseq nth_u8zeros ler_maxr 1:/#.
case: (i<at) => ?; first smt(nth_out).
rewrite nth_cat nth_rcons.
case: (i-at < size l) => ?.
 by rewrite ifT 1:/#.
case: (i - at = size l) => ?; first smt().
rewrite ifF /#.
qed.

lemma srspecP0 lw at l len tb:
 len=0 /\ tb=0 =>
 srpre 0 at l len tb =>
 srspec lw 0 at l len tb =>
 bytes2state (u8zeros at ++ l ++ [W8.of_int tb])
 = bytes2state lw.
proof.
move=> [-> ->] /> Hat Hsz.
search (size _ = 0).
have ->: l=[] by smt(size_eq0).
move=> H; move: (H _); first smt().
move => {H}[_ H].
rewrite cats0 /= cats1 -nseqSr 1:/#.
have ->: lw = u8zeros (size lw).
apply (u8prefAt0 _ 0 at [] 0); first 2 smt(nseq0).
by rewrite -cat0s bytes2state_zext eq_sym -cat0s bytes2state_zext.
qed.

(*  msubread *)

op msubread_pre (cur at buf len tb: int): bool = 
 0<=cur /\ 0<=at /\ 0<=buf /\ 0<=len /\ 0<=tb<256 /\
 at + len + b2i(tb<>0) <= 200.

lemma msubreadP m lw at buf len tb at1 buf1 len1 tb1:
 msubread_pre 0 at buf len tb =>
 (at+len+b2i(tb<>0) <= size lw) \/ len1=0 /\ tb1=0 =>
 msubread m lw 0 at buf len tb at1 buf1 len1 tb1 =>
 bytes2state (u8zeros at ++ memread m buf len ++ [of_int tb])
 = bytes2state lw
 /\ at1 = at + len + b2i (tb<>0)
 /\ buf1 = buf + len
 /\ len1 = 0
 /\ tb1 = 0.
proof.
move => /> ?????? Hlw H; split; last smt().
case: (at <= size lw) => C; last first.
 have Elen: len=0 by smt().
 have Etb: tb=0 by smt().
 apply (srspecP0 _ _ _ _ _ _ _ H); first smt().
 by move=> />; rewrite Elen size_memread /#.
have HHlw: at + len + b2i (tb <> 0) <= size lw by smt().
apply (srspecP _ _ _ _ _ _ _ H) => //.
by rewrite /srpre size_memread 1:/# /#.
qed.

module Maux = {
  proc __addstate_m_avx2_aux(st : W256.t Array7.t, aT : int, buf : int, _LEN : int, _TRAILB : int) :
    W256.t Array7.t * int * int = {
    var r0 : W256.t;
    var r1 : W256.t;
    var t64_1 : W64.t;
    var t64_2 : W64.t;
    var t128_0 : W128.t;
    var t128_1 : W128.t;
    var t128_2 : W128.t;
    var r3 : W256.t;
    var t64_3 : W64.t;
    var r4 : W256.t;
    var t64_4 : W64.t;
    var r5 : W256.t;
    var t64_5 : W64.t;
    var r6 : W256.t;
    var r2 : W256.t;

    t64_1 <- W64.zero;
    if ((aT < 8)) {
      (buf, _LEN, _TRAILB, aT, t64_1) <@ M.__m_ilen_read_upto8_at(buf, _LEN, _TRAILB, 0, aT);
    } else { }

    r1 <- W256.zero;
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (buf, _LEN, _TRAILB, aT, r1) <@ M.__m_ilen_read_upto32_at(buf, _LEN, _TRAILB, 8, aT);
    } else { }

    t64_2 <- W64.zero;
    t64_3 <- W64.zero;
    t64_4 <- W64.zero;
    t64_5 <- W64.zero;
    r3 <- W256.zero;
    r4 <- W256.zero;
    r5 <- W256.zero;
    r6 <- W256.zero;
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (buf, _LEN, _TRAILB, aT, t64_2) <@ M.__m_ilen_read_upto8_at(buf, _LEN, _TRAILB, 40, aT);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (buf, _LEN, _TRAILB, aT, r3) <@ M.__m_ilen_read_upto32_at(buf, _LEN, _TRAILB, 48, aT);
        (buf, _LEN, _TRAILB, aT, t64_3) <@ M.__m_ilen_read_upto8_at(buf, _LEN, _TRAILB, 80, aT);
        (buf, _LEN, _TRAILB, aT, r4) <@ M.__m_ilen_read_upto32_at(buf, _LEN, _TRAILB, 88, aT);
        (buf, _LEN, _TRAILB, aT, t64_4) <@ M.__m_ilen_read_upto8_at(buf, _LEN, _TRAILB, 120, aT);
        (buf, _LEN, _TRAILB, aT, r5) <@ M.__m_ilen_read_upto32_at(buf, _LEN, _TRAILB, 128, aT);
        (buf, _LEN, _TRAILB, aT, t64_5) <@ M.__m_ilen_read_upto8_at(buf, _LEN, _TRAILB, 160, aT);
        (buf, _LEN, _TRAILB, aT, r6) <@ M.__m_ilen_read_upto32_at(buf, _LEN, _TRAILB, 168, aT);
      } else { }
    } else { }

    t128_0 <- (VMOV_64 t64_1);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    st.[0] <- (st.[0] `^` r0);

    st.[1] <- (st.[1] `^` r1);

    st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);

    t128_1 <- (VMOV_64 t64_2);
    t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
    t128_2 <- (VMOV_64 t64_3);
    t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
    r2 <- zeroextu256 t128_2;
    r2 <- VINSERTI128 r2 t128_1 (W8.of_int 1);
    st.[2] <- (st.[2] `^` r2);

    return (st, aT, buf);
  }
}.

equiv addstate_m_aux_eq:
 M.__addstate_m_avx2 ~ Maux.__addstate_m_avx2_aux
 : ={Glob.mem,arg} ==> ={res}.
proof.
proc; simplify.
swap {2} [14..16] -11.
seq 1 5: (#pre).
 sp; if => //=.
  wp; call m_ilen_read_bcast_upto8_at_eq; auto => &1 &2 /> ?.
  by move => [r1' r2' r3' r4' r5'] [r1 r2 r3 r4 r5] />.
 auto => /> &m _.
 by move: (st{m}) => _st; clear; circuit.
swap {2} 12 -9.
seq 1 3: (#pre); simplify.
 sp; if => //=; first by sim.
 auto => /> &m _.
 rewrite tP => i Hi; rewrite get_setE //.
 by case: (i=1) => //.
sp; if => //=. 
 seq 1 1: (#[/2:-2]pre /\ ={t64_2}) => //=. 
  call (: ={Glob.mem,arg} ==> ={res}); first by sim.
  by auto => />.
 sp; if => //=.
  swap {2} 9 -8; sp 0 1.
  swap {1} 3 3; swap {1} [5..6] 2.
  swap {1} [7..9] 2.
  by sim.
 wp; ecall {2} (addstate_r3456_avx2_zero_ph st{2}).
 auto => /> &m *.
 by move: (st{m}) (t64_2{m}) => _st _t64_2; clear; circuit.
wp; ecall {2} (addstate_r3456_avx2_zero_ph st{2}).
auto => /> &m *.
rewrite tP => i Hi; rewrite get_setE //.
case: (i=2) => //.
by move => /> *; move: (st{m}) => _st; clear; circuit.
qed.

(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ======================================
*)

lemma addstate_m_avx2_ll: islossless M.__addstate_m_avx2
 by islossless.

hoare addstate_m_avx2_h _mem _st _buf _len _tb _at:
 M.__addstate_m_avx2
 : Glob.mem=_mem /\ st=_st /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= _buf /\ 0 <= _tb < 256
 /\  stavx2INV _st
 ==> let l = u8zeros _at ++ memread _mem _buf _len ++ [W8.of_int _tb]
     in res.`1 = addstate_avx2 _st (bytes2state l)
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _buf + _len.
proof.
bypr => &m'; split => //.
move=> [Hmem] |> *.
have ->:
 Pr[M.__addstate_m_avx2(st{m'}, aT{m'}, buf{m'}, _LEN{m'},
                          _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addstate_avx2 st{m'}
        (bytes2state
           (u8zeros aT{m'} ++ memread _mem buf{m'} _LEN{m'} ++
            [W8.of_int _TRAILB{m'}])) /\
      res.`2 = aT{m'} + _LEN{m'} + b2i (_TRAILB{m'} <> 0) /\
      res.`3 = buf{m'} + _LEN{m'})]
 = Pr[Maux.__addstate_m_avx2_aux( st{m'}, aT{m'}, buf{m'}, _LEN{m'}
                               , _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addstate_avx2 st{m'}
        (bytes2state
           (u8zeros aT{m'} ++ memread _mem buf{m'} _LEN{m'} ++
            [W8.of_int _TRAILB{m'}])) /\
      res.`2 = aT{m'} + _LEN{m'} + b2i (_TRAILB{m'} <> 0) /\
      res.`3 = buf{m'} + _LEN{m'})].
byequiv addstate_m_aux_eq => /#.
clear _st _buf _len _tb _at.
pose _st := st{m'}; pose _buf := buf{m'}.
pose _len := _LEN{m'}; pose _tb := _TRAILB{m'}; pose _at := aT{m'}.
byphoare (_: Glob.mem=_mem /\ st=_st /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= buf /\ 0 <= _tb < 256
 /\  stavx2INV _st ==> _) => //; last by smt().
hoare.
clear; proc; simplify.
pose _statebytes := u8zeros _at ++ memread _mem _buf _len ++ [W8.of_int _tb].
seq 13: ( st=_st /\
          bytes2state _statebytes = bytes2state (stavx2bytes_pack t64_1 r1 t64_2 r3 t64_3 r4 t64_4 r5 t64_5 r6)
          /\ aT = _at + _len + b2i (_tb <> 0) /\ buf = _buf + _len /\ stavx2INV _st).
 seq 2: ( #[1:2,8:]pre
        /\ msubread_pre 0 _at _buf _len _tb
        /\ msubread _mem (u64bytes t64_1) 0 _at _buf _len _tb aT buf _LEN _TRAILB).
  case: (aT < 8).
   rcondt 2; first by auto.
   ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB 0 aT).
   by auto => &m |> /#.
  rcondf 2; first by auto.
  auto => |> *; split; first smt().
  apply msubread0; rewrite size_to_list; last smt().
  by rewrite u64bytes0.
 seq 2: ( #[/:-2]pre
        /\ msubread _mem (u64bytes t64_1++u256bytes r1) 0 _at _buf _len _tb aT buf _LEN _TRAILB).
  case: (aT < 40 /\ (0 < _LEN \/ _TRAILB <> 0)).
   rcondt 2; first by auto.
   ecall (m_ilen_read_upto32_at_h buf _LEN _TRAILB 8 aT).
   auto => &m |> ????? H0 ? Hsz [buf' len' tb' at' w'] /= H1.
   split; first smt().
   by apply (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  rcondf 2; first by auto.
  auto => &m |> ????? H0 /negb_and H.
  have H1:= msubread0 Glob.mem{m} (u256bytes zero) 8 aT{m} buf{m} _LEN{m} _TRAILB{m} _ _.
  + by rewrite u256bytes0 size_nseq /#.
  + rewrite size_to_list /#.
  by apply (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
 case: (0 < _LEN \/ _TRAILB <> 0).
  rcondt 9; first by auto.
  swap [2..8] 1.
  seq 2: ( #[/:-3]pre
         /\ msubread _mem (u64bytes t64_1++u256bytes r1++u64bytes t64_2)
                     0 _at _buf _len _tb aT buf _LEN _TRAILB).
   ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB 40 aT).
   auto => &m |> ????? H0 Hsz [buf' len' tb' at' w'] /= H1.
   split; first smt().
   by apply (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  sp; if => //=.
   wp; ecall (m_ilen_read_upto32_at_h buf _LEN _TRAILB 168 aT).
   ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB 160 aT).
   ecall (m_ilen_read_upto32_at_h buf _LEN _TRAILB 128 aT).
   ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB 120 aT).
   ecall (m_ilen_read_upto32_at_h buf _LEN _TRAILB 88 aT).
   ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB 80 aT).
   ecall (m_ilen_read_upto32_at_h buf _LEN _TRAILB 48 aT).
   auto => &m |> ???? Hpre H Hc.
   move=> [] /= dlt3 len3 tb3 at3 r3 H3.
   have {H H3} H3:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H3).
   move=> [] /= dlt2b len2b tb2b at2b t64_3 H2b.
   have {H3 dlt3 len3 tb3 at3 H2b} H2b:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H2b).
   move=> [] /= dlt4 len4 tb4 at4 r4 H4.
   have {H2b dlt2b len2b tb2b at2b H4} H4:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2b H4).
   move=> [] /= dlt2c len2c tb2c at2c t64_4 H2c.
   have {H4 dlt4 len4 tb4 at4 H2c} H2c:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H2c).
   move=> [] /= dlt5 len5 tb5 at5 r5 H5.
   have {H2c dlt2c len2c tb2c at2c H5} H5:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2c H5).
   move=> [] /= dlt2d len2d tb2d at2d t64_5 H2d.
   have {H5 dlt5 len5 tb5 at5 H2d} H2d:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H2d).
   move=> [] /= dlt6 len6 tb6 at6 r6 H6.
   have {H2d dlt2d len2d tb2d at2d H6} /= H6:= (msubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2d H6).
   by have HH:= msubreadP _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /= /#.
  auto => |> &m ????? H6 /negb_or [Hlen Htb].
  have HH:= msubreadP _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /=; first 2 smt().
  split.
   by rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA bytes2state_zext /#.
  smt().
 rcondf 9; first by auto.
 auto => |> &m ????? H6 ?.
 have HH:= msubreadP _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /=; first 2 smt().
 split.
  by rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA bytes2state_zext /#.
 smt().
(* handling the permutation part with 'circuit' *)
exlim t64_1 => _t64_1; exlim r1 => _r1; exlim t64_2 => _t64_2; exlim r3 => _r3; exlim t64_3 => _t64_3; exlim r4 => _r4; exlim t64_4 => _t64_4; exlim r5 => _r5; exlim t64_5 => _t64_5; exlim r6 => _r6.
move: _st => _st.
conseq (: st = _st /\ stavx2INV _st /\ t64_1=_t64_1 /\ r1=_r1 /\ t64_2=_t64_2 /\ r3=_r3 /\ t64_3=_t64_3 /\ r4=_r4 /\ t64_4=_t64_4 /\ r5=_r5 /\ t64_5=_t64_5 /\ r6=_r6 ==> st = addstate_avx2 _st (stavx2_pack _t64_1 _r1 _t64_2 _r3 _t64_3 _r4 _t64_4 _r5 _t64_5 _r6)) => //=.
 by rewrite /_astate stavx2_packE => /> * /#.
inline *; clear.
by circuit.
qed.

phoare addstate_m_avx2_ph _mem _st _buf _len _tb _at:
 [ M.__addstate_m_avx2
 : Glob.mem=_mem /\ st=_st /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= _buf /\ 0 <= _tb < 256
 /\  stavx2INV _st
 ==> let l = u8zeros _at ++ memread _mem _buf _len ++ [W8.of_int _tb]
     in res.`1 = addstate_avx2 _st (bytes2state l)
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _buf + _len
 ] = 1%r.
proof. by conseq addstate_m_avx2_ll (addstate_m_avx2_h _mem _st _buf _len _tb _at). qed.

lemma absorb_m_avx2_ll: islossless M.__absorb_m_avx2.
proof.
proc.
seq 2: true => //=; last first.
 if => //.
 by call addratebit_avx2_ll.
call addstate_m_avx2_ll.
if => //.
 wp; while true (iTERS-i).
 move=> z; wp.
 call keccakf1600_avx2_ll.
 call addstate_m_avx2_ll.
 by auto => /#.
wp; call keccakf1600_avx2_ll.
wp; call addstate_m_avx2_ll.
by auto => /#.
qed.

hoare absorb_m_avx2_h _mem _l _buf _len _r8 _tb:
 M.__absorb_m_avx2
 : Glob.mem=_mem /\ aT = size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
 /\ 0 <= _tb < 256 
 /\ 0 <= _buf
 /\ 0 <= _len
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ memread _mem _buf _len) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ memread _mem _buf _len) res.`1
          /\ res.`2 = (size _l + _len) %% _r8.
proof.
(* `buf - _buf` bytes of the input are absorbed (the state is tracked through
   its 25-word view); each block is closed by the shared pabsorb_fill and the
   last one by pabsorb_last, as in the ref absorb_m_h. *)
proc => /=.
seq 1: (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ 0 <= _len /\ 0 <= _buf
       /\ _buf <= buf <= _buf + _len /\ _LEN = _len - (buf - _buf)
       /\ aT = (size _l + (buf - _buf)) %% _r8 /\ aT + _LEN < _r8
       /\ stavx2INV st
       /\ pabsorb_spec _r8 (_l ++ take (buf - _buf) (memread _mem _buf _len)) (stavx2_to_st25 st)).
+ if => //; last first.
   auto => |> &m.
   rewrite pabsorb_spec_avx2E => [[Hinv H]] Htb0 Htb1 Hbuf Hlen Hg.
   have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec => [#].
   do 3!(split; first smt()).
   by rewrite Hinv /= take0 cats0.
  wp; while (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200 /\
             0 <= _len /\ 0 <= _buf /\
             iTERS = (_len - (_r8 - size _l %% _r8)) %/ _r8 /\ 0 <= i <= iTERS /\
             buf = _buf + (_r8 - size _l %% _r8 + i * _r8) /\ stavx2INV st /\
             pabsorb_spec _r8 (_l ++ take (_r8 - size _l %% _r8 + i * _r8) (memread _mem _buf _len)) (stavx2_to_st25 st)).
  + wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)); ecall (addstate_m_avx2_h Glob.mem st buf _RATE8 0 0).
    auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hlen Hbuf Hi0 Hi1 Hinv IH Hb.
    have Hm: 0 <= i{m} * _r8 by apply mulr_ge0 => /#.
    have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by rewrite ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_len - (_r8 - size _l %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ??? [st' at' buf'] /= Est _ Ebuf.
    rewrite Est /addstate_avx2 stavx2_from_st25K /=.
    rewrite stavx2INV_from_st25 stavx2_from_st25K /=.
    split; first smt().
    split; first smt().
    have Ed: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
    have Ha0: (size _l + (_r8 - size _l %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have Hf := pabsorb_fill _r8 _l (memread _mem _buf _len) (_r8 - size _l %% _r8 + i{m} * _r8) (stavx2_to_st25 st{m}).
    move: Hf; rewrite Ha0 /= => Hf.
    rewrite (_: _r8 - size _l %% _r8 + (i{m} + 1) * _r8 = _r8 - size _l %% _r8 + i{m} * _r8 + _r8) 1:/#.
    rewrite -(slice_memread _mem _buf _len (_r8 - size _l %% _r8 + i{m} * _r8) _r8) 1..3:/#.
    by apply Hf => //; rewrite ?size_memread //; smt().
  wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)); wp; ecall (addstate_m_avx2_h Glob.mem st buf (_RATE8 - aT) 0 aT).
  auto => |> &m.
  rewrite pabsorb_spec_avx2E => [[Hinv H]] Htb0 Htb1 Hbuf Hlen Hg.
  have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec => [#].
  have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ???? [st' at' buf'] /= Est _ Ebuf.
  rewrite Est /addstate_avx2 stavx2_from_st25K /=.
  rewrite stavx2INV_from_st25 stavx2_from_st25K /=.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   have Hf := pabsorb_fill _r8 _l (memread _mem _buf _len) 0 (stavx2_to_st25 st{m}).
   move: Hf => /=; rewrite take0 drop0 cats0 => Hf.
   rewrite -(take_memread' _mem _buf _len (_r8 - size _l %% _r8)) 1:/#.
   by apply Hf => //; rewrite ?size_memread //; smt().
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hinv0 Hs.
  have Ei: i0 = (_len - (_r8 - size _l %% _r8)) %/ _r8 by smt().
  have Ed: _len - (_r8 - size _l %% _r8) = (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 + (_len - (_r8 - size _l %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
  have Hq: 0 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by apply mulr_ge0 => /#.
  have Hmd: 0 <= (_len - (_r8 - size _l %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  move: Hs; rewrite Ei => Hs.
  rewrite (_: _buf + (_r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) - _buf = _r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) 1:/#.
  split; first smt().
  split; first smt().
  split.
   by rewrite (_: size _l + (_r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) = (size _l %/ _r8 + 1 + (_len - (_r8 - size _l %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
  by split; first smt().
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2_h _RATE8 st); ecall (addstate_m_avx2_h Glob.mem st buf _LEN _TRAILB aT); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hlen Hbuf Hb0 Hb1 Hfit Hinv H Htb.
  split; first smt().
  move=> ???? [st' at' buf'] /= Est _ Ebuf.
  rewrite Est /addstate_avx2 stavx2INV_from_st25 /= stavx2_from_st25K.
  have Hk: 0 <= buf{m} - _buf <= size (memread _mem _buf _len) by rewrite size_memread //; smt().
  have Hfit': (size _l + (buf{m} - _buf)) %% _r8 + (size (memread _mem _buf _len) - (buf{m} - _buf)) < _r8 by rewrite size_memread.
  have [Hl1 _] := pabsorb_last _r8 _l (memread _mem _buf _len) (buf{m} - _buf) (stavx2_to_st25 st{m}) _tb Hk Hfit' H.
  by rewrite /absorb_spec_avx2 -(drop_memread_cur _mem _buf _len buf{m}) 1:/# Hl1.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_m_avx2_h Glob.mem st buf _LEN _TRAILB aT); auto => |> &m.
move=> Hr0 Hr1 Hlen Hbuf Hb0 Hb1 Hfit Hinv H.
split; first smt().
move=> ???? [st' at' buf'] /= Est Eat _.
have Hk: 0 <= buf{m} - _buf <= size (memread _mem _buf _len) by rewrite size_memread //; smt().
have Hfit': (size _l + (buf{m} - _buf)) %% _r8 + (size (memread _mem _buf _len) - (buf{m} - _buf)) < _r8 by rewrite size_memread.
have [_ Hl0] := pabsorb_last _r8 _l (memread _mem _buf _len) (buf{m} - _buf) (stavx2_to_st25 st{m}) 0 Hk Hfit' H.
split.
 rewrite pabsorb_spec_avx2E Est /addstate_avx2 stavx2INV_from_st25 /= stavx2_from_st25K.
 by move: (Hl0 (eq_refl 0)) => /=; rewrite -(drop_memread_cur _mem _buf _len buf{m}) 1:/#.
rewrite Eat b2i0 /=.
have E: (size _l + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf)) = (size _l + _len) + (- (size _l + (buf{m} - _buf)) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf))) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_m_avx2_ph _mem _l _buf _len _r8 _tb:
 [ M.__absorb_m_avx2
 : Glob.mem=_mem /\ aT = size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
 /\ 0 <= _tb < 256 
 /\ 0 <= _buf
 /\ 0 <= _len
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ memread _mem _buf _len) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ memread _mem _buf _len) res.`1
          /\ res.`2 = (size _l + _len) %% _r8
 ] = 1%r.
proof. by conseq absorb_m_avx2_ll (absorb_m_avx2_h _mem _l _buf _len _r8 _tb). qed.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_m_avx2_ll: islossless M.__dumpstate_m_avx2
 by islossless.

hoare dumpstate_m_avx2_h _mem _buf _len _st:
 M.__dumpstate_m_avx2
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes (stavx2_to_st25 _st)) 0 _len)
  /\ res = _buf + _len.
proof.
proc => /=.
conseq (: Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ 0 <= _len <= 200
          ==> msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 200) _buf _len buf _LEN).
 by move=> &hr />.
 move=> &hr [#] _ _ _ _ Hl0 Hl1 _ m1 l1 b1 H.
 by apply (msubwrite_dump_take _ _ _ _ _ _ _ _ _ H).
(* lane 0: the first 8 bytes of st.[0] *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 8) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200).
 if.
  wp; ecall (m_ilen_write_upto32_h Glob.mem buf 8 st.[0]).
  auto => |> Hl0 Hl1 H8 [b1 l1] m1 /= H.
  rewrite -(dump_avx2_w0 _st).
  have Hs: size (take 8 (u256bytes _st.[0])) = 8 by rewrite size_take' // /u256bytes size_to_list.
  apply (msubwrite_rebudget _ _ _ _ 8 _len b1 l1 (_len - 8)); 1..3: by rewrite Hs.
  by apply (msubwrite_take_budget _ _ _ 8 _ _ _ _ _ _ H).
 ecall (m_ilen_write_upto32_h Glob.mem buf _LEN st.[0]).
 auto => |> Hl0 Hl1 H8 [b1 l1] m1 /= H.
 rewrite -(dump_avx2_w0 _st).
 by apply (msubwrite_take_budget _ _ _ 8 _ _ _ _ _ _ H) => /#.
(* lanes 1..4 *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 40) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200).
 ecall (m_ilen_write_upto32_h Glob.mem buf _LEN st.[1]).
 auto => |> &m H Hl0 Hl1 [b1 l1] m1 /= H1.
 exact (msubwrite_sub_step _ _ _ _ _ _ 8 32 40 _ _ _ _ _ _ _ _ H (dump_avx2_w1 _st) H1).
if; last first.
 auto => |> &m H Hl0 Hl1 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 40 200 _ _ _ C H).
(* lane 5 *)
seq 5: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 48) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ t128_0 = truncateu128 _st.[2]).
 wp; ecall (m_ilen_write_upto8_h Glob.mem buf _LEN t).
 auto => |> &m H Hl0 Hl1 C [b1 l1] m1 /= H1.
 exact (msubwrite_sub_step _ _ _ _ _ _ 40 8 48 _ _ _ _ _ _ _ _ H (dump_avx2_w2 _st) H1).
if; last first.
 auto => |> &m H Hl0 Hl1 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 48 200 _ _ _ C H).
(* lanes 6..9 *)
seq 6: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 80) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ t128_0 = truncateu128 _st.[2]
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 ecall (m_ilen_write_upto32_h Glob.mem buf _LEN t256_4).
 auto => |> &m H Hl0 Hl1 C [b1 l1] m1 /= H1.
 exact (msubwrite_sub_step _ _ _ _ _ _ 48 32 80 _ _ _ _ _ _ _ _ H (dump_avx2_w3 _st) H1).
(* lane 10 (and t128_0 moves to lane 20) *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 88) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 if.
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf _LEN t).
  auto => |> &m H Hl0 Hl1 C [b1 l1] m1 /= H1.
  exact (msubwrite_sub_step _ _ _ _ _ _ 80 8 88 _ _ _ _ _ _ _ _ H (dump_avx2_w4 _st) H1).
 auto => |> &m H Hl0 Hl1 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 80 88 _ _ _ C H).
(* lanes 11..14 *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 120) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 if.
  ecall (m_ilen_write_upto32_h Glob.mem buf _LEN t256_4).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 l1] m1 /= H1.
  split; first exact (msubwrite_sub_step _ _ _ _ _ _ 88 32 120 _ _ _ _ _ _ _ _ H (dump_avx2_w5 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 88 120 _ _ _ C H).
(* lane 15 *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 128) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf _LEN t).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 l1] m1 /= H1.
  split; first exact (msubwrite_sub_step _ _ _ _ _ _ 120 8 128 _ _ _ _ _ _ _ _ H (dump_avx2_w6 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 120 128 _ _ _ C H).
(* lanes 16..19 *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 160) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  ecall (m_ilen_write_upto32_h Glob.mem buf _LEN t256_4).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 l1] m1 /= H1.
  split; first exact (msubwrite_sub_step _ _ _ _ _ _ 128 32 160 _ _ _ _ _ _ _ _ H (dump_avx2_w7 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 128 160 _ _ _ C H).
(* lane 20 *)
seq 1: (msubwrite _mem Glob.mem (sub (avx2bytes _st) 0 168) _buf _len buf _LEN
        /\ st = _st /\ 0 <= _len <= 200
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  wp; ecall (m_ilen_write_upto8_h Glob.mem buf _LEN t).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 l1] m1 /= H1.
  rewrite Ht0 // in H1.
  exact (msubwrite_sub_step _ _ _ _ _ _ 160 8 168 _ _ _ _ _ _ _ _ H (dump_avx2_w8 _st) H1).
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (msubwrite_sub_skip _ _ _ _ _ 160 168 _ _ _ C H).
(* lanes 21..24 *)
if.
 ecall (m_ilen_write_upto32_h Glob.mem buf _LEN t256_4).
 auto => |> &m H Hl0 Hl1 C [b1 l1] m1 /= H1.
 exact (msubwrite_sub_step _ _ _ _ _ _ 168 32 200 _ _ _ _ _ _ _ _ H (dump_avx2_w9 _st) H1).
auto => |> &m H Hl0 Hl1 C.
exact (msubwrite_sub_skip _ _ _ _ _ 168 200 _ _ _ C H).
qed.

phoare dumpstate_m_avx2_ph _mem _buf _len _st:
 [ M.__dumpstate_m_avx2
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes (stavx2_to_st25 _st)) 0 _len)
  /\ res = _buf + _len
 ] = 1%r.
proof.
by conseq dumpstate_m_avx2_ll (dumpstate_m_avx2_h _mem _buf _len _st).
qed.

lemma squeeze_m_avx2_ll: islossless M.__squeeze_m_avx2.
proof.
proc.
seq 4: true => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_m_avx2_ll.
  call keccakf1600_avx2_ll.
  by auto => /#.
 auto => /#.
if => //.
call dumpstate_m_avx2_ll.
call keccakf1600_avx2_ll.
by auto.
qed.

hoare squeeze_m_avx2_h _mem _buf _len _st _r8:
 M.__squeeze_m_avx2
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 /\ stavx2INV _st
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st))
  /\ res = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1)).
proof.
proc.
seq 4: (0 <= _len /\ 0 < _r8 <= 200 /\ _buf + _len < W64.modulus /\ _RATE8 = _r8
        /\ lO = _len %% _r8
        /\ st = stavx2_from_st25 (st_i (stavx2_to_st25 _st) (_len %/ _r8))
        /\ buf = _buf + _r8 * (_len %/ _r8)
        /\ msubwrite _mem Glob.mem (squeezeblocks _r8 (stavx2_to_st25 _st) (_len %/ _r8))
                     _buf _len buf (_len - _r8 * (_len %/ _r8))).
 while (0 <= i <= _len %/ _r8 /\ 0 <= _len /\ 0 < _r8 <= 200 /\ _buf + _len < W64.modulus
        /\ _RATE8 = _r8 /\ iTERS = _len %/ _r8 /\ lO = _len %% _r8
        /\ st = stavx2_from_st25 (st_i (stavx2_to_st25 _st) i) /\ buf = _buf + _r8 * i
        /\ msubwrite _mem Glob.mem (squeezeblocks _r8 (stavx2_to_st25 _st) i)
                     _buf _len buf (_len - _r8 * i)).
  wp; ecall (dumpstate_m_avx2_h Glob.mem buf _RATE8 st).
  ecall (keccakf1600_avx2_h (st_i (stavx2_to_st25 _st) i)).
  auto => |> &m Hi0 Hi1 Hl Hr0 Hr1 Hb Hsw Hi.
  have Est: keccak_f1600_op (st_i (stavx2_to_st25 _st) i{m}) = st_i (stavx2_to_st25 _st) (i{m}+1).
   by rewrite /st_i iterS 1:/#.
  rewrite Est stavx2_from_st25K; split.
   split; first smt().
   by have := mul_divz_le _r8 _len (i{m}+1) _ _; smt().
  move=> _ _ _; do 3!(split; first smt()).
  rewrite squeezeblocks_step 1:/# 1:/#.
  apply (msubwrite_app _ _ _ _ _ _ _ _ _ _ _ _ _ Hsw).
  + rewrite size_squeezeblocks 1,2:/# size_sub 1:/#.
    by have := mul_divz_le _r8 _len (i{m}+1) _ _; smt().
  + by rewrite size_sub /#.
  + by rewrite size_sub /#.
 auto => |> Hl Hr0 Hr1 Hb Hinv; split.
  split; first smt(divz_ge0).
  split; first by rewrite /st_i iter0 // stavx2_to_st25K.
  by rewrite /squeezeblocks iota0 //= flatten_nil /msubwrite store0 /#.
 move=> mem i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _len %/ _r8 by smt().
if => //.
 ecall (dumpstate_m_avx2_h Glob.mem buf lO st).
 ecall (keccakf1600_avx2_h (st_i (stavx2_to_st25 _st) (_len %/ _r8))).
 auto => |> &m Hl Hr0 Hr1 Hb Hsw C.
 have Est: keccak_f1600_op (st_i (stavx2_to_st25 _st) (_len %/ _r8))
           = st_i (stavx2_to_st25 _st) (_len %/ _r8 + 1).
  by rewrite /st_i iterS 1:divz_ge0 /#.
 rewrite Est stavx2_from_st25K; split; first smt().
 move=> _ _ _; split.
  by apply (msubwrite_squeeze_last _ _ _ _ _ _ _ _ _ _ _ Hsw).
 by rewrite divz_pred_pos 1,2:/#.
auto => |> &m Hl Hr0 Hr1 Hb Hsw C.
split; first by apply (msubwrite_squeeze_fin _ _ _ _ _ _ _ _ _ _ _ Hsw).
by rewrite divz_pred_zero 1,2:/#.
qed.

phoare squeeze_m_avx2_ph _mem _buf _len _st _r8:
 [ M.__squeeze_m_avx2
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 /\ stavx2INV _st
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st))
  /\ res = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1))
 ] = 1%r.
proof.
by conseq squeeze_m_avx2_ll (squeeze_m_avx2_h _mem _buf _len _st _r8).
qed.


abstract theory KeccakArrayAvx2.

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


op asubread_pre (cur at off dlt len tb: int): bool = 
 0<=cur /\ 0<=at /\ 0<=off /\ 0<=dlt /\ 0<=len /\ 0<=tb<256 /\
 off + dlt + len <= _ASIZE /\
 at + len + b2i(tb<>0) <= 200.

lemma asubreadP buf off lw at dlt len tb at1 dlt1 len1 tb1:
 asubread_pre 0 at off dlt len tb =>
 (at+len+b2i(tb<>0) <= size lw) \/ len1=0 /\ tb1=0 =>
 asubread buf off lw 0 at dlt len tb at1 dlt1 len1 tb1 =>
 bytes2state (u8zeros at ++ sub buf (off+dlt) len ++ [of_int tb])
 = bytes2state lw
 /\ at1 = at + len + b2i (tb<>0)
 /\ dlt1 = dlt + len
 /\ len1 = 0
 /\ tb1 = 0.
proof.
move => /> ???????? Hlw H; split; last smt().
move: (H _); first smt().
move=> {H}H.
case: (at <= size lw) => C; last first.
 have Elen: len=0 by smt().
 have Etb: tb=0 by smt().
 apply (srspecP0 _ _ _ _ _ _ _ H); first smt().
 by move=> />; rewrite Elen size_sub /#.
have HHlw: at + len + b2i (tb <> 0) <= size lw by smt().
apply (srspecP _ _ _ _ _ _ _ H) => //.
by rewrite /srpre size_sub 1:/# /#.
qed.

module MM = {
  proc __addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
                        offset:int, _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                             int * int = {
    var dELTA:int;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, r0) <@ RW.MM.__a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {

    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ RW.MM.__a_ilen_read_upto32_at (buf, 
      offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {

    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ RW.MM.__a_ilen_read_upto8_at (buf,
      offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {

      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {

    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc __absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
                      _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ M._keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_avx2 (st, 0, buf, offset, _RATE8, 0);
        st <@ M._keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {

    }
    (st, aT,  _2) <@ __addstate_avx2 (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_avx2 (st, _RATE8);
    } else {

    }
    return (st, aT);
  }
  proc __dumpstate_avx2 (buf:W8.t A.t, offset:int, _LEN:int,
                         st:W256.t Array7.t) : W8.t A.t * int = {
    var dELTA:int;
    var t128_0:W128.t;
    var t128_1:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    dELTA <- 0;
    if ((8 <= _LEN)) {
      (buf, dELTA,  _0) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA, 8,
      st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA, 
      _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA, 
    _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA, 
      _LEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < _LEN)) {
        t256_0 <-
        (VPBLEND_8u32 st.[3] st.[4]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_1 <-
        (VPBLEND_8u32 st.[4] st.[3]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_2 <-
        (VPBLEND_8u32 st.[5] st.[6]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_3 <-
        (VPBLEND_8u32 st.[6] st.[5]
        (W8.of_int
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        t256_4 <-
        (VPBLEND_8u32 t256_0 t256_3
        (W8.of_int
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((1 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) +
        ((2 ^ 1) *
        ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
        ));
        (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA,
        _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA,
          _LEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {

        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_3 t256_1
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA,
          _LEN, t256_4);
        } else {

        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA,
          _LEN, t);
        } else {

        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_2 t256_0
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA,
          _LEN, t256_4);
        } else {

        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA,
          _LEN, t);
        } else {

        }
        if ((0 < _LEN)) {
          t256_4 <-
          (VPBLEND_8u32 t256_1 t256_2
          (W8.of_int
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((1 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) +
          ((2 ^ 1) *
          ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
          ));
          (buf, dELTA, _LEN) <@ RW.MM.__a_ilen_write_upto32 (buf, offset, dELTA,
          _LEN, t256_4);
        } else {

        }
      } else {

      }
    } else {

    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc __squeeze_avx2 (st:W256.t Array7.t, buf:W8.t A.t, _RATE8:int) : 
  W256.t Array7.t * W8.t A.t = {
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    offset <- 0;
    _LEN <- _ASIZE;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    i <- 0;
    while ((i < iTERS)) {
      st <@ M._keccakf1600_avx2 (st);
      (buf, offset) <@ __dumpstate_avx2 (buf, offset, _RATE8, st);
      i <- (i + 1);
    }
    if ((0 < lO)) {
      st <@ M._keccakf1600_avx2 (st);
      (buf, offset) <@ __dumpstate_avx2 (buf, offset, lO, st);
    } else {

    }
    return (st, buf);
  }
}.


module MMaux = {
  proc __addstate_avx2_aux (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
                            offset:int, _LEN:int, _TRAILB:int
                           ) : W256.t Array7.t * int * int = {
    var dELTA:int;
    var t64_1:W64.t;
    var t128_0:W128.t;
    var r0:W256.t;
    var r1:W256.t;
    var t64_2:W64.t;
    var t128_1:W128.t;
    var t128_2:W128.t;
    var r3:W256.t;
    var t64_3:W64.t;
    var r4:W256.t;
    var t64_4:W64.t;
    var r5:W256.t;
    var t64_5:W64.t;
    var r6:W256.t;
    var r2:W256.t;
    dELTA <- 0;

    t64_1 <- W64.zero;
    if ((aT < 8)) {
      (dELTA, _LEN, _TRAILB, aT, t64_1) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
    } else { }

    r1 <- W256.zero;
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ RW.MM.__a_ilen_read_upto32_at (buf, 
      offset, dELTA, _LEN, _TRAILB, 8, aT);
    } else { }

    t64_2 <- W64.zero;
    t64_3 <- W64.zero;
    t64_4 <- W64.zero;
    t64_5 <- W64.zero;
    r3 <- W256.zero;
    r4 <- W256.zero;
    r5 <- W256.zero;
    r6 <- W256.zero;
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ RW.MM.__a_ilen_read_upto8_at (buf,
      offset, dELTA, _LEN, _TRAILB, 40, aT);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        (dELTA, _LEN, _TRAILB, aT, r5) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        (dELTA, _LEN, _TRAILB, aT, r6) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 168, aT);
      } else { }
    } else { }
    offset <- (offset + dELTA);

    t128_0 <- (VMOV_64 t64_1);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    st.[0] <- (st.[0] `^` r0);

    st.[1] <- (st.[1] `^` r1);

    st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);

    t128_1 <- (VMOV_64 t64_2);
    t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
    t128_2 <- (VMOV_64 t64_3);
    t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
    r2 <- zeroextu256 t128_2;
    r2 <- VINSERTI128 r2 t128_1 (W8.of_int 1);
    st.[2] <- (st.[2] `^` r2);

    return (st, aT, offset);
  }
}.

lemma addstate_avx2_ll: islossless MM.__addstate_avx2
 by islossless.

equiv addstate_aux_eq:
 MM.__addstate_avx2 ~ MMaux.__addstate_avx2_aux
 : ={arg} ==> ={res}.
proc; simplify.
swap {2} [16..18] -12.
seq 2 6: (#pre /\ ={dELTA}).
 sp; if => //=.
  wp; call a_ilen_read_bcast_upto8_at_eq; auto => /> &m ?.
  by move => [r1' r2' r3' r4' r5'] [r1 r2 r3 r4 r5] />.
 auto => /> &m _.
 by move: (st{m}) => _st; clear; circuit.
swap {2} 13 -10.
seq 1 3: (#pre); simplify.
 sp; if => //=; first by sim.
 auto => /> &m _.
 rewrite tP => i Hi; rewrite get_setE //.
 by case: (i=1) => //.
sp; if => //=. 
 seq 1 1: (#[/2:-2]pre /\ ={t64_2}) => //=. 
  call (: ={arg} ==> ={res}); first by sim.
  by auto => />.
 sp; if => //=.
  swap {2} 10 -9; sp 0 1.
  swap {1} 3 3; swap {1} [5..6] 2.
  swap {1} [7..9] 2.
  swap {1} 15 -7.
  by sim.
 wp; ecall {2} (addstate_r3456_avx2_zero_ph st{2}).
 auto => /> &m *.
 by move: (st{m}) (t64_2{m}) => _st _t64_2; clear; circuit.
wp; ecall {2} (addstate_r3456_avx2_zero_ph st{2}).
auto => /> &m *.
rewrite tP => i Hi; rewrite get_setE //.
case: (i=2) => //.
by move => /> *; move: (st{m}) => _st; clear; circuit.
qed.

hoare addstate_avx2_h _st _buf _off _len _tb _at:
 MM.__addstate_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= offset /\ offset + _len <= _ASIZE /\ 0 <= _tb < 256
 /\  stavx2INV _st
 ==> let l = nseq _at W8.zero ++ sub _buf _off _len ++ [W8.of_int _tb]
     in res.`1 = addstate_avx2 _st (bytes2state l)
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _off + _len.
proof.
bypr => &m' |> *.
have ->:
 Pr[MM.__addstate_avx2(st{m'}, aT{m'}, buf{m'}, offset{m'}, _LEN{m'},
                          _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addstate_avx2 st{m'}
        (bytes2state
           (nseq aT{m'} W8.zero ++ sub buf{m'} offset{m'} _LEN{m'} ++
            [W8.of_int _TRAILB{m'}])) /\
      res.`2 = aT{m'} + _LEN{m'} + b2i (_TRAILB{m'} <> 0) /\
      res.`3 = offset{m'} + _LEN{m'})]
 = Pr[MMaux.__addstate_avx2_aux( st{m'}, aT{m'}, buf{m'}, offset{m'}, _LEN{m'}
                               , _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addstate_avx2 st{m'}
        (bytes2state
           (nseq aT{m'} W8.zero ++ sub buf{m'} offset{m'} _LEN{m'} ++
            [W8.of_int _TRAILB{m'}])) /\
      res.`2 = aT{m'} + _LEN{m'} + b2i (_TRAILB{m'} <> 0) /\
      res.`3 = offset{m'} + _LEN{m'})].
byequiv addstate_aux_eq => /#.
clear _st _buf _off _len _tb _at.
pose _st := st{m'}; pose _buf := buf{m'}; pose _off := offset{m'}.
pose _len := _LEN{m'}; pose _tb := _TRAILB{m'}; pose _at := aT{m'}.
byphoare (_: st=_st /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= offset /\ offset + _len <= _ASIZE /\ 0 <= _tb < 256
 /\  stavx2INV _st ==> _) => //; last by smt().
hoare.
clear; proc; simplify.
pose _statebytes := nseq _at W8.zero ++ sub _buf _off _len ++ [W8.of_int _tb].
seq 15: ( st=_st /\
          bytes2state _statebytes = bytes2state (stavx2bytes_pack t64_1 r1 t64_2 r3 t64_3 r4 t64_4 r5 t64_5 r6)
          /\ aT = _at + _len + b2i (_tb <> 0) /\ offset = _off + _len /\ stavx2INV _st).
 seq 3: ( #[1:3,8:]pre
        /\ asubread_pre 0 _at _off 0 _len _tb
        /\ asubread _buf _off (u64bytes t64_1) 0 _at 0 _len _tb aT dELTA _LEN _TRAILB).
  case: (aT < 8).
   rcondt 3; first by auto.
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 0 aT).
   by auto => &m /#.
  rcondf 3; first by auto.
  auto => |> *; split; first smt().
  apply asubread0; rewrite size_to_list; last smt().
  by rewrite u64bytes0.
 seq 2: ( #[/:-2]pre
        /\ asubread _buf _off (u64bytes t64_1++u256bytes r1) 0 _at 0 _len _tb aT dELTA _LEN _TRAILB).
  case: (aT < 40 /\ (0 < _LEN \/ _TRAILB <> 0)).
   rcondt 2; first by auto.
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 8 aT).
   auto => &m |> ?????? H0 ? Hsz [dlt' len' tb' at' w'] /= H1.
   by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  rcondf 2; first by auto.
  auto => &m |> ?????? H0 /negb_and H.
  have H1:= asubread0 _buf _off (u256bytes zero) 8 aT{m} dELTA{m} _LEN{m} _TRAILB{m} _ _.
  + by rewrite u256bytes0 size_nseq /#.
  + rewrite size_to_list /#.
  by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
 case: (0 < _LEN \/ _TRAILB <> 0).
  rcondt 9; first by auto.
  swap [2..8] 1.
  seq 2: ( #[/:-3]pre
         /\ asubread _buf _off (u64bytes t64_1++u256bytes r1++u64bytes t64_2)
                     0 _at 0 _len _tb aT dELTA _LEN _TRAILB).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 40 aT).
   auto => &m |> ?????? H0 Hsz [dlt' len' tb' at' w'] /= H1.
   by apply (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  sp; if => //=.
   wp; ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 168 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 160 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 128 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 120 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 88 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 80 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 48 aT).
   auto => &m |> ????? Hpre H Hc.
   move=> [] /= dlt3 len3 tb3 at3 r3 H3.
   have {H H3} H3:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H3).
   move=> [] /= dlt2b len2b tb2b at2b t64_3 H2b.
   have {H3 dlt3 len3 tb3 at3 H2b} H2b:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H2b).
   move=> [] /= dlt4 len4 tb4 at4 r4 H4.
   have {H2b dlt2b len2b tb2b at2b H4} H4:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2b H4).
   move=> [] /= dlt2c len2c tb2c at2c t64_4 H2c.
   have {H4 dlt4 len4 tb4 at4 H2c} H2c:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H2c).
   move=> [] /= dlt5 len5 tb5 at5 r5 H5.
   have {H2c dlt2c len2c tb2c at2c H5} H5:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2c H5).
   move=> [] /= dlt2d len2d tb2d at2d t64_5 H2d.
   have {H5 dlt5 len5 tb5 at5 H2d} H2d:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H2d).
   move=> [] /= dlt6 len6 tb6 at6 r6 H6.
   have {H2d dlt2d len2d tb2d at2d H6} /= H6:= (asubread_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2d H6).
   by have HH:= asubreadP _ _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /= /#.
  auto => |> &m ?????? H6 /negb_or [Hlen Htb].
  have HH:= asubreadP _ _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /=; first 2 smt().
  split.
   by rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA bytes2state_zext /#.
  smt().
 rcondf 9; first by auto.
 auto => |> &m ?????? H6 ?.
 have HH:= asubreadP _ _ _ _ _ _ _ _ _ _ _ _ _ H6; rewrite ?size_cat ?size_to_list /=; first 2 smt().
 split.
  by rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA bytes2state_zext /#.
 smt().
(* handling the permutation part with 'circuit' *)
exlim t64_1 => _t64_1; exlim r1 => _r1; exlim t64_2 => _t64_2; exlim r3 => _r3; exlim t64_3 => _t64_3; exlim r4 => _r4; exlim t64_4 => _t64_4; exlim r5 => _r5; exlim t64_5 => _t64_5; exlim r6 => _r6.
move: _st => _st.
conseq (: st = _st /\ stavx2INV _st /\ t64_1=_t64_1 /\ r1=_r1 /\ t64_2=_t64_2 /\ r3=_r3 /\ t64_3=_t64_3 /\ r4=_r4 /\ t64_4=_t64_4 /\ r5=_r5 /\ t64_5=_t64_5 /\ r6=_r6 ==> st = addstate_avx2 _st (stavx2_pack _t64_1 _r1 _t64_2 _r3 _t64_3 _r4 _t64_4 _r5 _t64_5 _r6)) => //=.
 by rewrite /_astate stavx2_packE => /> * /#.
inline *; clear.
by circuit.
qed.

lemma absorb_avx2_ll: islossless MM.__absorb_avx2.
proof.
proc.
seq 4: true => //=; last first.
 if => //.
 by call addratebit_avx2_ll.
call addstate_avx2_ll.
sp; if => //.
 wp; while true (iTERS-i).
 move=> z; wp.
 call keccakf1600_avx2_ll.
 call addstate_avx2_ll.
 by auto => /#.
wp; call keccakf1600_avx2_ll.
wp; call addstate_avx2_ll.
by auto => /#.
qed.

hoare absorb_avx2_h _l _buf _tb _r8:
 MM.__absorb_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
 /\ 0 <= _tb < 256 
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ to_list _buf) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ to_list _buf) res.`1
          /\ res.`2 = (size _l + _ASIZE) %% _r8.
proof.
(* `offset` bytes of the input are absorbed (the state is tracked through its
   25-word view); each block is closed by the shared pabsorb_fill and the last
   one by pabsorb_last, as in the ref absorb_h. *)
proc => /=.
have HA := _ASIZE_ge0.
seq 3: (buf = _buf /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ 0 <= offset <= _ASIZE /\ _LEN = _ASIZE - offset
       /\ aT = (size _l + offset) %% _r8 /\ aT + _LEN < _r8
       /\ stavx2INV st
       /\ pabsorb_spec _r8 (_l ++ take offset (to_list _buf)) (stavx2_to_st25 st)).
+ sp; if => //; last first.
   auto => |> &m.
   rewrite pabsorb_spec_avx2E => [[Hinv H]] Htb0 Htb1 Hg.
   have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec => [#].
   do 2!(split; first smt()).
   by rewrite Hinv /= take0 cats0.
  wp; while (buf = _buf /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200 /\
             iTERS = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 /\ 0 <= i <= iTERS /\
             offset = _r8 - size _l %% _r8 + i * _r8 /\ stavx2INV st /\
             pabsorb_spec _r8 (_l ++ take offset (to_list _buf)) (stavx2_to_st25 st)).
  + wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)); ecall (addstate_avx2_h st buf offset _RATE8 0 0).
    auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hi0 Hi1 Hinv IH Hb.
    have Hm: 0 <= i{m} * _r8 by apply mulr_ge0 => /#.
    have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by rewrite ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_ASIZE - (_r8 - size _l %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ???? [st' at' off'] /= Est _ Eoff.
    rewrite Est /addstate_avx2 stavx2_from_st25K /=.
    rewrite stavx2INV_from_st25 stavx2_from_st25K /=.
    split; first smt().
    split; first smt().
    have Ed: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
    have Ha0: (size _l + (_r8 - size _l %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have Hf := pabsorb_fill _r8 _l (to_list _buf) (_r8 - size _l %% _r8 + i{m} * _r8) (stavx2_to_st25 st{m}).
    move: Hf; rewrite Ha0 /= => Hf.
    rewrite Eoff -(slice_to_list _buf (_r8 - size _l %% _r8 + i{m} * _r8) _r8) 1..3:/#.
    by apply Hf => //; rewrite ?size_to_list; smt().
  wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)); wp; ecall (addstate_avx2_h st buf offset (_RATE8 - aT) 0 aT).
  auto => |> &m.
  rewrite pabsorb_spec_avx2E => [[Hinv H]] Htb0 Htb1 Hg.
  have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec => [#].
  have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ???? [st' at' off'] /= Est _ Eoff.
  rewrite Est /addstate_avx2 stavx2_from_st25K /=.
  rewrite stavx2INV_from_st25 stavx2_from_st25K /=.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   have Hf := pabsorb_fill _r8 _l (to_list _buf) 0 (stavx2_to_st25 st{m}).
   move: Hf => /=; rewrite take0 drop0 cats0 => Hf.
   rewrite Eoff -(take_to_list _buf (_r8 - size _l %% _r8)) 1:/#.
   by apply Hf => //; rewrite ?size_to_list; smt().
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hinv0 Hs.
  have Ei: i0 = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 by smt().
  have Ed: _ASIZE - (_r8 - size _l %% _r8) = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 + (_ASIZE - (_r8 - size _l %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
  have Hq: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by apply mulr_ge0 => /#.
  have Hmd: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite Ei; split; first smt().
  split; first smt().
  split; last smt().
  by rewrite (_: size _l + (_r8 - size _l %% _r8 + (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8) = (size _l %/ _r8 + 1 + (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_avx2_h _RATE8 st); ecall (addstate_avx2_h st buf offset _LEN _TRAILB aT); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Ho0 Ho1 Hfit Hinv H Htb.
  split; first smt().
  move=> ???? [st' at' off'] /= Est _ _.
  rewrite Est /addstate_avx2 stavx2INV_from_st25 /= stavx2_from_st25K.
  have Hk: 0 <= offset{m} <= size (to_list _buf) by rewrite size_to_list.
  have Hfit': (size _l + offset{m}) %% _r8 + (size (to_list _buf) - offset{m}) < _r8 by rewrite size_to_list.
  have [Hl1 _] := pabsorb_last _r8 _l (to_list _buf) offset{m} (stavx2_to_st25 st{m}) _tb Hk Hfit' H.
  by rewrite /absorb_spec_avx2 -(drop_to_list _buf offset{m}) 1:/# Hl1.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_avx2_h st buf offset _LEN _TRAILB aT); auto => |> &m.
move=> Hr0 Hr1 Ho0 Ho1 Hfit Hinv H.
split; first smt().
move=> ???? [st' at' off'] /= Est Eat _.
have Hk: 0 <= offset{m} <= size (to_list _buf) by rewrite size_to_list.
have Hfit': (size _l + offset{m}) %% _r8 + (size (to_list _buf) - offset{m}) < _r8 by rewrite size_to_list.
have [_ Hl0] := pabsorb_last _r8 _l (to_list _buf) offset{m} (stavx2_to_st25 st{m}) 0 Hk Hfit' H.
split.
 rewrite pabsorb_spec_avx2E Est /addstate_avx2 stavx2INV_from_st25 /= stavx2_from_st25K.
 by move: (Hl0 (eq_refl 0)) => /=; rewrite -(drop_to_list _buf offset{m}) 1:/#.
rewrite Eat b2i0 /=.
have E: (size _l + offset{m}) %% _r8 + (_ASIZE - offset{m}) = (size _l + _ASIZE) + (- (size _l + offset{m}) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l + offset{m}) %% _r8 + (_ASIZE - offset{m})) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_avx2_ph _l _buf _tb _r8:
 [ MM.__absorb_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
 /\ 0 <= _tb < 256 /\ 0 < _r8
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ to_list _buf) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ to_list _buf) res.`1
          /\ res.`2 = (size _l + _ASIZE) %% _r8
 ] = 1%r.
proof.
by conseq absorb_avx2_ll (absorb_avx2_h _l _buf _tb _r8).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_avx2_ll: islossless MM.__dumpstate_avx2
 by islossless.

hoare dumpstate_avx2_h _buf _off _len _st:
 MM.__dumpstate_avx2
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 ==> res.`1 = A.fill (fun i=>(stbytes (stavx2_to_st25 _st)).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len.
proof.
proc => /=; wp.
conseq (: buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st /\ 0 <= _len <= 200
          ==> asubwrite _buf buf _off (sub (avx2bytes _st) 0 200) 0 _len dELTA _LEN /\ offset = _off).
 move=> &hr [#] _ -> _ _ Hl0 Hl1 l1 b1 d1 [H _].
 have Hb: 0 <= _len <= 200 by done.
 by have [-> ->] := asubwrite_dump_take _ _ _ _ _ _ _ _ Hb H.
(* lane 0: the first 8 bytes of st.[0] *)
seq 2: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 8) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200).
 sp; if.
  wp; ecall (a_ilen_write_upto32_h buf offset dELTA 8 st.[0]).
  auto => |> Hl0 Hl1 H8 [b1 d1 l1] /= H.
  rewrite -(dump_avx2_w0 _st).
  have Hs: size (take 8 (u256bytes _st.[0])) = 8 by rewrite size_take' // /u256bytes size_to_list.
  apply (asubwrite_rebudget _ _ _ _ _ 8 _len d1 l1 (_len - 8)); 1..3: by rewrite Hs.
  by apply (asubwrite_take_budget _ _ _ _ 8 _ _ _ _ _ _ H).
 ecall (a_ilen_write_upto32_h buf offset dELTA _LEN st.[0]).
 auto => |> Hl0 Hl1 H8 [b1 d1 l1] /= H.
 rewrite -(dump_avx2_w0 _st).
 by apply (asubwrite_take_budget _ _ _ _ 8 _ _ _ _ _ _ H) => /#.
(* lanes 1..4 *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 40) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200).
 ecall (a_ilen_write_upto32_h buf offset dELTA _LEN st.[1]).
 auto => |> &m H Hl0 Hl1 [b1 d1 l1] /= H1.
 exact (asubwrite_sub_step _ _ _ _ _ _ 8 32 40 _ _ _ _ _ _ _ _ H (dump_avx2_w1 _st) H1).
if; last first.
 auto => |> &m H Hl0 Hl1 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 40 200 _ _ _ C H).
(* lane 5 *)
seq 5: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 48) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ t128_0 = truncateu128 _st.[2]).
 wp; ecall (a_ilen_write_upto8_h buf offset dELTA _LEN t).
 auto => |> &m H Hl0 Hl1 C [b1 d1 l1] /= H1.
 exact (asubwrite_sub_step _ _ _ _ _ _ 40 8 48 _ _ _ _ _ _ _ _ H (dump_avx2_w2 _st) H1).
if; last first.
 auto => |> &m H Hl0 Hl1 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 48 200 _ _ _ C H).
(* lanes 6..9 *)
seq 6: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 80) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ t128_0 = truncateu128 _st.[2]
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 ecall (a_ilen_write_upto32_h buf offset dELTA _LEN t256_4).
 auto => |> &m H Hl0 Hl1 C [b1 d1 l1] /= H1.
 exact (asubwrite_sub_step _ _ _ _ _ _ 48 32 80 _ _ _ _ _ _ _ _ H (dump_avx2_w3 _st) H1).
(* lane 10 (and t128_0 moves to lane 20) *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 88) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 if.
  wp; ecall (a_ilen_write_upto8_h buf offset dELTA _LEN t).
  auto => |> &m H Hl0 Hl1 C [b1 d1 l1] /= H1.
  exact (asubwrite_sub_step _ _ _ _ _ _ 80 8 88 _ _ _ _ _ _ _ _ H (dump_avx2_w4 _st) H1).
 auto => |> &m H Hl0 Hl1 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 80 88 _ _ _ C H).
(* lanes 11..14 *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 120) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ t128_1 = VPUNPCKH_2u64 (VEXTRACTI128 _st.[2] (W8.of_int 1)) (VEXTRACTI128 _st.[2] (W8.of_int 1))
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)
        /\ t256_3 = VPBLEND_8u32 _st.[6] _st.[5] (W8.of_int 240)).
 if.
  ecall (a_ilen_write_upto32_h buf offset dELTA _LEN t256_4).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 d1 l1] /= H1.
  split; first exact (asubwrite_sub_step _ _ _ _ _ _ 88 32 120 _ _ _ _ _ _ _ _ H (dump_avx2_w5 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 88 120 _ _ _ C H).
(* lane 15 *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 128) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_0 = VPBLEND_8u32 _st.[3] _st.[4] (W8.of_int 240)
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  wp; ecall (a_ilen_write_upto8_h buf offset dELTA _LEN t).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 d1 l1] /= H1.
  split; first exact (asubwrite_sub_step _ _ _ _ _ _ 120 8 128 _ _ _ _ _ _ _ _ H (dump_avx2_w6 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 120 128 _ _ _ C H).
(* lanes 16..19 *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 160) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ (0 < _LEN => t128_0 = VPUNPCKH_2u64 (truncateu128 _st.[2]) (truncateu128 _st.[2]))
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  ecall (a_ilen_write_upto32_h buf offset dELTA _LEN t256_4).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 d1 l1] /= H1.
  split; first exact (asubwrite_sub_step _ _ _ _ _ _ 128 32 160 _ _ _ _ _ _ _ _ H (dump_avx2_w7 _st) H1).
  smt().
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 128 160 _ _ _ C H).
(* lane 20 *)
seq 1: (asubwrite _buf buf _off (sub (avx2bytes _st) 0 168) 0 _len dELTA _LEN
        /\ offset = _off /\ st = _st /\ 0 <= _len <= 200
        /\ t256_1 = VPBLEND_8u32 _st.[4] _st.[3] (W8.of_int 240)
        /\ t256_2 = VPBLEND_8u32 _st.[5] _st.[6] (W8.of_int 240)).
 if.
  wp; ecall (a_ilen_write_upto8_h buf offset dELTA _LEN t).
  auto => |> &m H Hl0 Hl1 Ht0 C [b1 d1 l1] /= H1.
  rewrite Ht0 // in H1.
  exact (asubwrite_sub_step _ _ _ _ _ _ 160 8 168 _ _ _ _ _ _ _ _ H (dump_avx2_w8 _st) H1).
 auto => |> &m H Hl0 Hl1 Ht0 C.
 exact (asubwrite_sub_skip _ _ _ _ _ 160 168 _ _ _ C H).
(* lanes 21..24 *)
if.
 ecall (a_ilen_write_upto32_h buf offset dELTA _LEN t256_4).
 auto => |> &m H Hl0 Hl1 C [b1 d1 l1] /= H1.
 exact (asubwrite_sub_step _ _ _ _ _ _ 168 32 200 _ _ _ _ _ _ _ _ H (dump_avx2_w9 _st) H1).
auto => |> &m H Hl0 Hl1 C.
exact (asubwrite_sub_skip _ _ _ _ _ 168 200 _ _ _ C H).
qed.

phoare dumpstate_avx2_ph _buf _off _len _st:
 [ MM.__dumpstate_avx2
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 ==> res.`1 = A.fill (fun i=>(stbytes (stavx2_to_st25 _st)).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len
 ] = 1%r.
proof.
by conseq dumpstate_avx2_ll (dumpstate_avx2_h _buf _off _len _st).
qed.

lemma squeeze_avx2_ll: islossless MM.__squeeze_avx2.
proof.
proc.
seq 6: true => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_avx2_ll.
  call keccakf1600_avx2_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_avx2_ll.
call keccakf1600_avx2_ll.
by auto.
qed.

hoare squeeze_avx2_h _buf _st _r8:
 MM.__squeeze_avx2
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 /\ stavx2INV _st
 ==> res.`1 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_ASIZE-1) %/ _r8 + 1))
     /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (stavx2_to_st25 _st)).
proof.
proc.
seq 6: (0 < _r8 <= 200 /\ _RATE8 = _r8 /\ lO = _ASIZE %% _r8
        /\ st = stavx2_from_st25 (st_i (stavx2_to_st25 _st) (_ASIZE %/ _r8))
        /\ offset = _r8 * (_ASIZE %/ _r8)
        /\ asubwrite _buf buf 0 (squeezeblocks _r8 (stavx2_to_st25 _st) (_ASIZE %/ _r8))
                     0 _ASIZE offset (_ASIZE - offset)).
 while (0 <= i <= _ASIZE %/ _r8 /\ 0 < _r8 <= 200 /\ _RATE8 = _r8
        /\ iTERS = _ASIZE %/ _r8 /\ lO = _ASIZE %% _r8
        /\ st = stavx2_from_st25 (st_i (stavx2_to_st25 _st) i) /\ offset = _r8 * i
        /\ asubwrite _buf buf 0 (squeezeblocks _r8 (stavx2_to_st25 _st) i) 0 _ASIZE offset (_ASIZE - offset)).
  wp; ecall (dumpstate_avx2_h buf offset _RATE8 st).
  ecall (keccakf1600_avx2_h (st_i (stavx2_to_st25 _st) i)).
  auto => |> &m Hi0 Hi1 Hr0 Hr1 Hsw Hi.
  have Est: keccak_f1600_op (st_i (stavx2_to_st25 _st) i{m}) = st_i (stavx2_to_st25 _st) (i{m}+1).
   by rewrite /st_i iterS 1:/#.
  rewrite Est stavx2_from_st25K; split; first smt().
  move=> _ _ [buf2 off2] /= Hbuf2 Hoff2.
  rewrite Hoff2 Hbuf2 /=; do 2!(split; first smt()).
  rewrite squeezeblocks_step 1:/# 1:/#.
  apply (asubwrite_app_dump _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsw); 2..5: smt().
  rewrite size_squeezeblocks 1,2:/#.
  by have := mul_divz_le _r8 _ASIZE (i{m}+1) _ _; smt().
 auto => |> Hr0 Hr1 Hinv; split.
  split; first smt(divz_ge0 _ASIZE_ge0).
  split; first by rewrite /st_i iter0 // stavx2_to_st25K.
  rewrite /squeezeblocks iota0 //= flatten_nil /asubwrite /=; split; last smt().
  by rewrite tP => i Hi; rewrite filliE // /#.
 move=> buf i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _ASIZE %/ _r8 by smt().
if => //.
 ecall (dumpstate_avx2_h buf offset lO st).
 ecall (keccakf1600_avx2_h (st_i (stavx2_to_st25 _st) (_ASIZE %/ _r8))).
 auto => |> &m Hr0 Hr1 Hsw C.
 have Est: keccak_f1600_op (st_i (stavx2_to_st25 _st) (_ASIZE %/ _r8))
           = st_i (stavx2_to_st25 _st) (_ASIZE %/ _r8 + 1).
  by rewrite /st_i iterS 1:divz_ge0 1:/# 1:_ASIZE_ge0.
 rewrite Est stavx2_from_st25K; split; first smt().
 move=> _ _ [buf2 off2] /= Hbuf2 _; split; first by rewrite divz_pred_pos 1,2:/#.
 have Hr: 0 < _r8 <= 200 by done.
 have HL := asubwrite_squeeze_last _ _ _ _ _ _ _ Hr C (eq_refl _) Hsw.
 by rewrite Hbuf2 -HL to_listK.
auto => |> &m Hr0 Hr1 Hsw C.
split; first by rewrite divz_pred_zero 1,2:/#.
have Hr: 0 < _r8 <= 200 by done.
by rewrite -(asubwrite_squeeze_fin _ _ _ _ _ _ Hr C Hsw) to_listK.
qed.

phoare squeeze_avx2_ph _buf _st _r8:
 [ MM.__squeeze_avx2
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 /\ stavx2INV _st
 ==> res.`1 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_ASIZE-1) %/ _r8 + 1))
     /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (stavx2_to_st25 _st))
 ] = 1%r.
proof.
by conseq squeeze_avx2_ll (squeeze_avx2_h _buf _st _r8).
qed.

end KeccakArrayAvx2.
