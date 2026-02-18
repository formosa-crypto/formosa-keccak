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


require import Keccak1600_avx2 Keccakf1600_avx2.
require import Keccak1600_subreadwrite.

import IntOrder.


op addstate_avx2 (s1: W256.t Array7.t, s2:state): W256.t Array7.t =
 stavx2_from_st25 (addstate (stavx2_to_st25 s1) s2).

op absorb_state_avx2 (st: W256.t Array7.t, l: W8.t list): W256.t Array7.t =
 addstate_avx2 st (bytes2state l).

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
rewrite /bytes2state /Wpack /w64L_from_bytes /chunkify.
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


lemma stavx2INV_pabsorb r8 l st:
 pabsorb_spec_avx2 r8 l st => stavx2INV st.
proof.
smt(stavx2INV_from_st25).
qed.


require import BitEncoding.
import BitChunking.

lemma chunk_take_eq' ['a] (n n': int) (l : 'a list):
  0 < n => 
  size l %/ n * n <= n' =>
  chunk n l = chunk n (take n' l).
proof.
move => Hn Hn'; rewrite /chunk.
have ->: size (take n' l) %/ n = size l %/ n.
 rewrite size_take; first smt(size_ge0).
 case: (n' < size l) => C //.
 rewrite eqz_leq; split; last smt().
 by apply leq_div2r; smt().
apply eq_in_mkseq => i Hi /=.
rewrite drop_take 1:/# take_take ifT //.
have ?: i*n < size l by smt().
have H1: n+i*n <= n'.
 move: Hn'; rewrite -lez_divRL 1:/# => Hn'.
 have H2: 1+i <= n' %/ n by smt(). 
 apply (lez_trans (n' %/ n * n)); last smt().
 by rewrite (:n+i*n=(1+i)*n) 1:/# ler_pmul2r /#.
smt().
qed.


lemma drop_cat' ['a] (n : int) (s1 s2 : 'a list):
 drop n (s1 ++ s2)
 = if n <= size s1 then drop n s1 ++ s2 else drop (n - size s1) s2.
proof.
case: (n=size s1) => [->//=|C].
 by rewrite drop_cat /= drop0 drop_size.
by rewrite drop_cat /#.
qed.

lemma chunkremains_cat ['a] (l1 l2 : 'a list) (r : int):
 0 < r =>
 chunkremains r (l1++l2) = chunkremains r (chunkremains r l1 ++ l2).
proof.
move=> Hr.
rewrite /chunkremains size_cat eq_sym.
rewrite drop_cat size_cat size_drop. smt(size_ge0).
have ->: max 0 (size l1 - size l1 %/ r * r) = size l1 %% r by smt().
rewrite drop_drop. smt(size_ge0). smt(size_ge0).
case: ((size l1 %% r + size l2) %/ r * r < size l1 %% r) => C.
 have E: (size l1 %% r + size l2) %/ r * r = 0 by smt(size_ge0).
 rewrite E /= drop_cat' ifT.
  by rewrite {1}(divz_eq (size l1) r) -addzA divzMDl 1:/# mulzDl E /= /#.
 rewrite {2}(divz_eq (size l1) r) -addzA divzMDl 1:/# mulzDl E /= /#.
rewrite drop_cat ifF.
move: C; apply contra.
  rewrite {1 2}(divz_eq (size l1) r) -addzA divzMDl 1:/#. smt().

congr.
rewrite eq_sym.
rewrite {1}(divz_eq (size l1) r) -addzA divzMDl 1:/# mulzDl.
rewrite {3}(divz_eq (size l1) r). ring.
qed.

lemma chunkremains_nil ['a] r (l: 'a list):
 0 < r =>
 r %| size l =>
 chunkremains r l = [].
proof.
by move=> Hr0 Hr; rewrite -size_eq0 size_chunkremains /#.
qed.

lemma bytes2state_cat l1 l2:
 bytes2state (l1++l2)
 = addstate (bytes2state l1) (bytes2state (u8zeros (size l1)++l2)).
proof.
rewrite -bytes2stbytesP.
have: bytes2stbytes (l1 ++ l2)
      = stbytes (addstate (bytes2state l1) (bytes2state (u8zeros (size l1) ++ l2))).
 rewrite tP stbytes_addstate => i Hi.
 rewrite /addstbytes map2iE // -!bytes2stbytesP !stwordsK !get_of_list // !nth_cat size_nseq ler_maxr.
  smt(size_ge0).
 case: (i < size l1) => C.
  by rewrite nth_u8zeros.
 by rewrite (nth_out _ l1) 1:/#.
by move => ->; rewrite stbytesK.
qed.
 
lemma addstateC s1 s2:
 addstate s1 s2 = addstate s2 s1.
proof.
rewrite tP => i Hi.
by rewrite /addstate !initiE //= xorwC.
qed.

lemma chunk1 ['a] r (l: 'a list):
 r <> 0 =>
 size l = r =>
 chunk r l = [l].
proof.
move=> Hr Hsz.
by rewrite /chunk Hsz divzz Hr b2i1 mkseq1 /= drop0 -Hsz take_size.
qed.

lemma stateabsorb_iblocks_rcons l x st:
 stateabsorb_iblocks (rcons l x) st
 = keccak_f1600_op (stateabsorb (stateabsorb_iblocks l st) x).
proof. by rewrite /stateabsorb_iblocks foldl_rcons /=. qed.





(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ======================================
*)

lemma addstate_m_avx2_ll: islossless M.__addstate_m_avx2
 by islossless.

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
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ memread _mem _buf _len) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ memread _mem _buf _len) res.`1
          /\ res.`2 = (size _l + _len) %% _r8.
proof.
proc => /=.
admitted.

phoare absorb_m_avx2_ph _mem _l _buf _len _r8 _tb:
 [ M.__absorb_m_avx2
 : Glob.mem=_mem /\ aT = size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ memread _mem _buf _len) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ memread _mem _buf _len) res.`1
          /\ res.`2 = (size _l + _len) %% _r8
 ] = 1%r.
proof.
by conseq absorb_m_avx2_ll (absorb_m_avx2_h _mem _l _buf _len _r8 _tb).
qed.

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
admitted.

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
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st))
  /\ res = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1)).
proof.
proc.
admitted.

phoare squeeze_m_avx2_ph _mem _buf _len _st _r8:
 [ M.__squeeze_m_avx2
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
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


(* TODO: move/refactor this to somewhere else *)

lemma take_to_list (buf: W8.t A.t) sz:
 sz <= _ASIZE =>
 take sz (A.to_list buf) = sub buf 0 sz.
proof.
move=> Hsz; case: (0 <= sz) => C.
 by rewrite take_mkseq //.
by rewrite take_le0 1:/# /sub mkseq0_le /#.
qed.

lemma drop_to_list (buf: W8.t A.t) sz:
 0 <= sz =>
 drop sz (A.to_list buf) = sub buf sz (_ASIZE-sz).
proof.
move=> Hsz; case: (sz < _ASIZE) => C.
 rewrite drop_mkseq 1:/#.
 apply eq_mkseq => x.
 by rewrite /(\o) /=.
by rewrite drop_oversize ?size_to_list 1:/# /sub mkseq0_le 1:/#.
qed.

lemma chunk_cat_buf r8 l (buf: W8.t A.t):
 let at = size l %% r8 in
 let lastpos = (at + _ASIZE) %/ r8 * r8 - at in
 0 < r8 =>
 chunk r8 (l ++ to_list buf)
 = chunk r8 (l ++ sub buf 0 lastpos).
proof.
move=> /= H.
rewrite !(chunk_cat' l) /= 1..2:/# /=; congr.
rewrite chunk_take_eq 1:/# size_cat size_chunkremains size_to_list.
rewrite take_cat' !size_chunkremains.
case: (r8 <= size l %% r8 + _ASIZE) => C.
 rewrite ifF 1:/#; congr; congr.
 by rewrite take_to_list /#.
rewrite divz_small /=; first smt(size_ge0 _ASIZE_ge0).
rewrite ifT; first smt(size_ge0).
rewrite take0 /sub mkseq0_le 1:/# cats0.
by rewrite eq_sym chunk_take_eq 1:/# size_chunkremains divz_small 1:/# take0.
qed.

lemma sub0' (buf: W8.t A.t) off len:
 len <= 0 =>
 sub buf off len = [].
proof. by move=> ?; rewrite /sub mkseq0_le. qed.

lemma chunkremains_cat_buf r8 l (buf: W8.t A.t) tb:
 let at = size l %% r8 in
 let lastpos = (at + _ASIZE) %/ r8 * r8 - at in
 let lastlen = if r8 <= at + _ASIZE then (at + _ASIZE) %% r8 else _ASIZE in
 0 < r8 =>
 bytes2state (chunkremains r8 (l ++ to_list buf) ++ [tb])
 = addstate
    (bytes2state (chunkremains r8 (l ++ sub buf 0 lastpos)))
    (bytes2state (u8zeros (if r8 <= size l %% r8 + _ASIZE then 0 else size l %% r8)
                 ++ sub buf (_ASIZE - lastlen) lastlen ++ [tb])).
proof.
move=> at lastpos lastlen H.
case: (r8 <= at + _ASIZE) => C.
 rewrite eq_sym chunkremains_cat 1:/# eq_sym chunkremains_cat 1:/#.
 rewrite /chunkremains !drop_cat !size_cat !size_to_list !size_sub 1:/#.
 rewrite !size_drop; first smt(size_ge0).
 rewrite ifF 1:/# ifF 1:/#.
 have ->: (size l - size l %/ r8 * r8) = size l %% r8 by smt().
 rewrite eq_sym drop_oversize 1:size_sub 1..2:/#.
 rewrite nseq0_le 1:/# /=.
 rewrite drop_to_list 1:/# bytes2state0 addstate_st0; congr; congr.
 by rewrite /lastlen C /= ler_maxr /#. 
rewrite {1}/A.sub mkseq0_le 1:/# cats0.
rewrite chunkremains_cat 1:// chunkremains_small.
 by rewrite size_cat size_chunkremains size_to_list /#.
rewrite -!catA bytes2state_cat; congr; congr; congr.
 by rewrite size_chunkremains /#. 
rewrite /to_list /sub /=; congr; smt().
qed.

lemma sub_split len' (buf: W8.t A.t) off len:
 0 <= len' <= len =>
 sub buf off len = sub buf off len' ++ sub buf (off+len') (len-len').
proof.
move=> Hlen.
rewrite (:len=len'+(len-len')) 1:/# /sub mkseq_add 1..2:/#; congr.
rewrite (:len' + (len - len') - len'=len-len') 1:/#.
by apply eq_mkseq => i /= /#.
qed.

(* end TODO *)


module MM = {
  proc __addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
                        offset:int, _LEN:int, _TRAILB:int) : W256.t Array7.t *
                                                             int * int = {
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
      t128_1 <- (zeroextu128 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ RW.MM.__a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (zeroextu128 t64_3);
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
      t128_0 <- (truncateu128 st.[2]);
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t <- (truncateu64 t128_1);
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
          t <- (truncateu64 t128_0);
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
          t <- (truncateu64 t128_1);
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
          t <- (truncateu64 t128_0);
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

    t128_0 <- (zeroextu128 t64_1);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    st.[0] <- (st.[0] `^` r0);

    st.[1] <- (st.[1] `^` r1);

    st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);

    t128_1 <- (zeroextu128 t64_2);
    t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
    t128_2 <- (zeroextu128 t64_3);
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
        /\ subread_pre 0 _at _len _tb
        /\ subread_spec 8 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT (u64bytes t64_1)).
  case: (aT < 8).
   rcondt 3; first by auto.
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 0 aT).
   by auto => &m /#.
  rcondf 3; first by auto.
  auto => |> *; split; first smt().
  by apply subread_spec_ahead8 => /#.
 seq 2: ( #[/:-2]pre
        /\ subread_spec 40 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT (u64bytes t64_1++u256bytes r1)).
  case: (aT < 40 /\ (0 < _LEN \/ _TRAILB <> 0)).
   rcondt 2; first by auto.
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 8 aT).
   auto => |> &m ?????? H0 ? Hsz [dlt' len' tb' at' w'] /= H1.
   by apply (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  rcondf 2; first by auto.
  auto => |> &m ?????? H0 /negb_and [Hat|Hsz].
   have H1:= subread_spec_ahead32 _buf _off dELTA{m} _LEN{m} _TRAILB{m} 8 aT{m} _; first by smt().
   by apply (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  have H1:= subread_spec_empty32 _buf _off dELTA{m} _LEN{m} _TRAILB{m} 8 aT{m} _; first by smt().
  by apply (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
 case: (0 < _LEN \/ _TRAILB <> 0).
  rcondt 9; first by auto.
  swap [2..8] 1.
  seq 2: ( #[/:-3]pre
         /\ subread_spec 48 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT
             (u64bytes t64_1++u256bytes r1++u64bytes t64_2)).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 40 aT).
   auto => |> &m ?????? H0 Hsz [dlt' len' tb' at' w'] /= H1.
   by apply (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
  sp; if => //=.
   wp; ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 168 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 160 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 128 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 120 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 88 aT).
   ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB 80 aT).
   ecall (a_ilen_read_upto32_at_h buf offset dELTA _LEN _TRAILB 48 aT).
   auto => |> &m ????? Hpre H Hc.
   move=> [] /= dlt3 len3 tb3 at3 r3 H3.
   move=> [] /= dlt2b len2b tb2b at2b t64_3 H2b.
   move=> [] /= dlt4 len4 tb4 at4 r4 H4.
   move=> [] /= dlt2c len2c tb2c at2c t64_4 H2c.
   move=> [] /= dlt5 len5 tb5 at5 r5 H5.
   move=> [] /= dlt2d len2d tb2d at2d t64_5 H2d.
   move=> [] /= dlt6 len6 tb6 at6 r6 H6.
   have {H H3} H3:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H3) => //.
   have {H3 H2b} H2b:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H2b) => //.
   have {H2b H4} H4:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2b H4) => //.
   have {H4 H2c} H2c:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H2c) => //.
   have {H2c H5} H5:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2c H5) => //.
   have {H5 H2d} H2d:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H2d) => //.
   have {H2d H6} /= H6:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2d H6) => //.
   have := subread_full _ _ _ _ _ _ _ _ _ _ _ H6 _; first 2 smt().
   by rewrite /= => />.
  auto => |> &m ?????? H6 /negb_or [Hlen Htb].
  have := subread_finished 48 _ _ _ _ _ _ _ _ _ _ _ _ H6 _ _; first 4 smt().
  move=> [? [? ->]]; split; last smt().
  rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA.
  by rewrite bytes2state_zext.
 rcondf 9; first by auto.
 auto => |> &m ?????? H6 ?.
  split; last smt().
  have := subread_finished 40 _ _ _ _ _ _ _ _ _ _ _ _ H6 _ _; first 4 smt().
  move=> [? [? ->]]. 
  rewrite /stavx2bytes_pack -!catA !u256bytes0 !u64bytes0 !cat_nseq //= !catA.
  by rewrite bytes2state_zext.
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
proc => /=.
have ?:= _ASIZE_u64.
have ?:= _ASIZE_ge0.
pose _at := size _l %% _r8.
pose niters := (_at + _ASIZE) %/ _r8.
pose lastlen := if _r8 <= _at + _ASIZE then (_at + _ASIZE) %% _r8 else _ASIZE.
pose lastpos := niters * _r8 - _at.

seq 3: (buf=_buf /\ _RATE8=_r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 
       /\ pabsorb_spec_avx2 _r8 (_l ++ sub _buf 0 lastpos) st
       /\ offset = _ASIZE - lastlen /\ _LEN = lastlen 
       /\ aT = if _RATE8 <= _at + _ASIZE then 0 else _at).
 sp; if => //; last first.
  auto => |> *.
  rewrite sub0' ?cats0.
   by rewrite /lastpos /niters divz_small 1:/# /= /#.
  smt().
 wp; while ( buf=_buf /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 
             iTERS= (size _l %% _r8 + _ASIZE) %/ _r8 - 1 /\
             offset = (i+1)*_r8 - size _l %% _r8 /\
             0 <= i <= iTERS /\
             pabsorb_spec_avx2 _r8 (_l ++ sub _buf 0 ((i+1)*_r8-size _l %% _r8)) st
           ).
  wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)).
  ecall (addstate_avx2_h st buf offset _RATE8 0 0).
  auto => |> &m Htb0 Htb1 Hi0 Hi1.
  rewrite {1}/pabsorb_spec_avx2 => [[Hr8]].
  rewrite {1}/PABSORB1600 chunkremains_nil 1:/#.
   rewrite size_cat size_sub 1:/# addzA (addzC (size _l)) -addzA.
   rewrite {1}(divz_eq (size _l) _r8) -addzA /= -mulzDl dvdzP.
   by exists (i{m} + 1 + size _l %/ _r8).
  rewrite /stateabsorb bytes2state0 addstateC addstate_st0 => Est Hb.
  rewrite !b2i0 /=; split.
   split; first smt().
   split; first smt().
   split.
    rewrite (:(i{m} + 1) * _r8 - size _l %% _r8 + _r8 <= _ASIZE
             =(i{m}+2)*_r8<=size _l%%_r8+_ASIZE) 1:/#.
    have Hb': i{m}+2 <= (size _l %% _r8 + _ASIZE) %/ _r8 by smt().
    apply (ler_trans ((size _l %% _r8 + _ASIZE) %/ _r8 * _r8)).
     by apply ler_wpmul2r; smt().
    by apply lez_floor; smt().
   by rewrite Est stavx2INV_from_st25.
  move => Hr80 Hr81 He0 He1 Hst [st' at' len'] /= Est' _ Elen'; split.
   by rewrite stavx2_to_st25K // Est' stavx2INV_from_st25.
  move => _; split; first smt().
  split; first smt().
  split; first smt().
  congr; rewrite /PABSORB1600 chunkremains_nil 1:/#.
   rewrite size_cat size_sub 1:/# addzA (addzC (size _l)) -addzA.
   rewrite {1}(divz_eq (size _l) _r8) -addzA /= -mulzDl dvdzP.
   by exists (i{m} + 2 + size _l %/ _r8).
  rewrite /stateabsorb bytes2state0 addstateC addstate_st0.
  rewrite (sub_split ((i{m} + 1) * _r8 - size _l %% _r8)) 1:/# catA chunk_cat /=.
   rewrite size_cat size_sub 1:/# addzA (addzC (size _l)) -addzA.
   rewrite {1}(divz_eq (size _l) _r8) -addzA /= -mulzDl dvdzP.
   by exists (i{m} + 1 + size _l %/ _r8).
  rewrite (chunk1 _ (sub _buf _ _)) 1:/#.
   by rewrite size_sub /#.
  rewrite cats1 stateabsorb_iblocks_rcons Est' stavx2_from_st25K /stateabsorb; congr; congr.
   by rewrite Est stavx2_from_st25K.
  by rewrite nseq0 /= -(nseq1 W8.zero) bytes2state_zext; congr; congr; smt().
 wp; ecall (keccakf1600_avx2_h (stavx2_to_st25 st)).
 wp; ecall (addstate_avx2_h st buf offset (_RATE8 - aT) 0 aT).
 auto => |> &m.
 rewrite /pabsorb_spec_avx2 /PABSORB1600 /stateabsorb => [[Hr8]] Est ?? Hc.
 split.
  split; first smt().
  split; first smt().
  by rewrite Est stavx2INV_from_st25.
 move=> |> ????? [st' at' len'] /=.
 rewrite !b2i0 /= => Est' _ _; split.
  by rewrite stavx2_to_st25K Est' // /addstate_avx2; apply stavx2INV_from_st25.
 move=> _; split.
  split.
   by rewrite (:_ASIZE - (_r8 - size _l %% _r8) = size _l %% _r8 + _ASIZE + (-1)*_r8) 1:/# divzMDr /#.
  split; first smt().
  rewrite chunkremains_nil 1:/#.
   rewrite size_cat size_sub 1:/# addzA (addzC (size _l)) -addzA.
   rewrite {1}(divz_eq (size _l) _r8) -addzA /= -{2}(mul1z _r8) -mulzDl dvdzP.
   by exists (1 + size _l %/ _r8).
  rewrite /stateabsorb bytes2state0 addstateC addstate_st0; congr.
  rewrite chunk_cat' 1:/# (chunk1 _ (_++_)) 1:/#.
   by rewrite size_cat size_chunkremains size_sub /#.
  rewrite cats1 stateabsorb_iblocks_rcons Est' Est !stavx2_from_st25K /stateabsorb. 
  rewrite -addstateA; congr; congr.
  rewrite -(nseq1 W8.zero) bytes2state_zext eq_sym bytes2state_cat; congr; congr.
  by rewrite size_chunkremains.
 move => i ??????.
 have ->: i=(_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 by smt().
 have E: (_ASIZE - (_r8 - size _l %% _r8))%/_r8 = (size _l %% _r8 + _ASIZE)%/_r8 - 1.
  have ->: _ASIZE - (_r8 - size _l %% _r8) = (size _l %% _r8 + _ASIZE + (-1)*_r8) by smt().
  by rewrite divzMDr /#.
 split.
  congr; congr; congr; congr; congr; congr.
   by rewrite /lastpos /niters /_at E /=.
  by rewrite /lastpos /niters /_at E /=.
 split.
  by rewrite /lastlen ifT 1:/# /_at E /= /#. 
 split.
  rewrite /lastlen ifT 1:/# /_at.
  by rewrite (:_ASIZE - (_r8 - size _l %% _r8) = _ASIZE + size _l %% _r8 + (-1)*_r8) 1:/# modzMDr /#.
 by rewrite ifT /#.

case: (_TRAILB<>0).
 rcondt 2; first by call (:true ==> true) => //.
 ecall (addratebit_avx2_h _RATE8 st).
 ecall (addstate_avx2_h st buf offset _LEN _TRAILB aT).
 auto => |> &m ?? H *.
 split.
  split; first smt(). 
  split; rewrite /lastlen.
   case: (_r8 <= _at + _ASIZE) => C; last smt().
   have ?: 0 <= _at < _r8 by smt().
   have: lastlen <= _ASIZE; last smt().
   rewrite /lastlen C /=; case: (_ASIZE < _r8) => ?; last smt().
   have ->: _at + _ASIZE = _r8 + _ASIZE + _at - _r8 by ring.
   by rewrite -!addzA modzDl !addzA modz_small /#.
  split; first smt().
  by apply (stavx2INV_pabsorb _ _ _ H).
 move => ?????? [st' at' off'] /= Est' Eat' Eoff'.
 move: H; rewrite /pabsorb_spec_avx2 /absorb_spec_avx2 => [[? H]].
 rewrite Est' H /addstate_avx2 !stavx2_from_st25K.
 rewrite /lastpos /niters /lastlen /ABSORB1600 /PABSORB1600 /stateabsorb_last /stateabsorb -cats1; congr; congr.
 rewrite -addstateA; congr.
  by congr; rewrite chunk_cat_buf 1:// /#.
 by rewrite chunkremains_cat_buf /#.
rcondf 2.
 by call (:true ==> true) => //.
ecall (addstate_avx2_h st buf offset _LEN _TRAILB aT).
auto => |> &m H.
split.
 split; first smt(). 
 split; rewrite /lastlen.
  case: (_r8 <= _at + _ASIZE) => C; last smt().
  have ?: 0 <= _at < _r8 by smt().
  have: lastlen <= _ASIZE; last smt().
  rewrite /lastlen C /=; case: (_ASIZE < _r8) => ?; last smt().
  have ->: _at + _ASIZE = _r8 + _ASIZE + _at - _r8 by ring.
  by rewrite -!addzA modzDl !addzA modz_small /#.
 split; first smt().
 by apply (stavx2INV_pabsorb _ _ _ H).
move => ????? [st' at' off'] /= Est' Eat' Eoff'.
split.
 move: H; rewrite /pabsorb_spec_avx2 => [[? H]]; split; first smt().
 rewrite Est' H /addstate_avx2 stavx2_from_st25K; congr.
 rewrite /PABSORB1600 /stateabsorb -addstateA; congr.
  by rewrite chunk_cat_buf /#.
 rewrite -chunkremains_cat_buf 1:/#.
 by rewrite -nseq1 bytes2state_zext.
rewrite Eat' b2i0 /lastlen /_at /=.
case: ( _r8 <= size _l %% _r8 + _ASIZE ) => C /=.
 by rewrite /_at modzDml.
by rewrite eq_sym -modzDml modz_small /#.
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
proc => /=.
admitted.

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
 ==> res.`1 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_ASIZE-1) %/ _r8 + 1))
     /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (stavx2_to_st25 _st)).
proof.
proc.
admitted.

phoare squeeze_avx2_ph _buf _st _r8:
 [ MM.__squeeze_avx2
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_ASIZE-1) %/ _r8 + 1))
     /\ res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (stavx2_to_st25 _st))
 ] = 1%r.
proof.
by conseq squeeze_avx2_ll (squeeze_avx2_h _buf _st _r8).
qed.

end KeccakArrayAvx2.
