(******************************************************************************
   Keccak1600_imem_avx2.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  4-way AVX2 implementation



******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.

from JazzEC require import WArray200 WArray800.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccak1600_Spec.


require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Keccak1600_subreadwrite.

(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_m_bcast_avx2x4_ll: islossless M.__addstate_m_bcast_avx2x4.
proof.
proc.
seq 5: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.

lemma addstate_m_avx2x4_ll: islossless M.__addstate_m_avx2x4.
proof.
proc.
seq 5: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
by auto => /#.
qed.

lemma absorb_m_bcast_avx2x4_ll: islossless M.__addstate_m_bcast_avx2x4.
proof.
proc.
seq 7: true => //.
 wp; while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move => z; auto => /#.
 sp; if => //.
  by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
if => //.
by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.

lemma absorb_m_avx2x4_ll: islossless M.__addstate_m_avx2x4.
proof.
proc.
seq 7: true => //.
 wp; while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move => z; auto => /#.
 sp; if => //.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
if => //.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
by auto => /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_m_avx2x4_ll: islossless M.__dumpstate_m_avx2x4.
proof.
proc.
seq 7: true => //.
 wp; while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
by auto => /#.
qed.

lemma squeeze_m_avx2x4_ll: islossless M.__squeeze_m_avx2x4.
proof.
proc.
seq 3: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_m_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_m_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.






abstract theory KeccakArrayAvx2x4.

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

module MM = {
  proc __addstate_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                buf:W8.t A.t, offset:int, _LEN:int,
                                _TRAILB:int) : W256.t Array25.t * int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ RW.MM.__a_ilen_read_bcast_upto8_at (
      buf, offset, dELTA, _LEN, _TRAILB, aT, aT8);
      w <- (w `^` st.[(aT %/ 8)]);
      st.[(aT %/ 8)] <- w;
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (32 * (aT %/ 8));
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      w <-
      (VPBROADCAST_4u64
      (get64_direct (WA.init8 (fun i => buf.[i])) offset));
      offset <- (offset + 8);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      at <- (at + 32);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_bcast_upto8_at (
      buf, offset, 0, _LEN, _TRAILB, aT, aT);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                              buf:W8.t A.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
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
      (st,  _0, offset) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ M._keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_bcast_avx2x4 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ M._keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __addstate_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t A.t,
                          buf1:W8.t A.t, buf2:W8.t A.t,
                          buf3:W8.t A.t, offset:int, _LEN:int,
                          _TRAILB:int) : W256.t Array25.t * int * int = {
    var dELTA:int;
    var aT8:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var at:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    var  _8:int;
    var  _9:int;
    var  _10:int;
    var  _11:int;
    var  _12:int;
    var  _13:int;
    var  _14:int;
    var  _15:int;
    var  _16:int;
    var  _17:int;
    var  _18:int;
    var  _19:int;
    var  _20:int;
    var  _21:int;
    var  _22:int;
    var  _23:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      ( _0,  _1,  _2,  _3, t0) <@ RW.MM.__a_ilen_read_upto8_at (buf0, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 0)) `^`
      t0))));
      ( _4,  _5,  _6,  _7, t1) <@ RW.MM.__a_ilen_read_upto8_at (buf1, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 1)) `^`
      t1))));
      ( _8,  _9,  _10,  _11, t2) <@ RW.MM.__a_ilen_read_upto8_at (buf2, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 2)) `^`
      t2))));
      (dELTA, _LEN, _TRAILB, aT8, t3) <@ RW.MM.__a_ilen_read_upto8_at (buf3,
      offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 3)) `^`
      t3))));
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (4 * (aT %/ 8));
    while ((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))))) {
      t0 <- (get64_direct (WA.init8 (fun i => buf0.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      t1 <- (get64_direct (WA.init8 (fun i => buf1.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      t2 <- (get64_direct (WA.init8 (fun i => buf2.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      t3 <- (get64_direct (WA.init8 (fun i => buf3.[i])) offset);
      offset <- (offset + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      at <- (at + 4);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      ( _12,  _13,  _14,  _15, t0) <@ RW.MM.__a_ilen_read_upto8_at (buf0, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      ( _16,  _17,  _18,  _19, t1) <@ RW.MM.__a_ilen_read_upto8_at (buf1, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      ( _20,  _21,  _22,  _23, t2) <@ RW.MM.__a_ilen_read_upto8_at (buf2, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      (dELTA, _LEN, _TRAILB, aT, t3) <@ RW.MM.__a_ilen_read_upto8_at (buf3, 
      offset, 0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t A.t,
                        buf1:W8.t A.t, buf2:W8.t A.t,
                        buf3:W8.t A.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
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
      (st,  _0, offset) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, 
      buf3, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ M._keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_avx2x4 (st, 0, buf0, buf1, buf2,
        buf3, offset, _RATE8, 0);
        st <@ M._keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, buf3,
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                           buf2:W8.t A.t, buf3:W8.t A.t,
                           offset:int, _LEN:int, st:W256.t Array25.t) : 
  W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t * int = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    i <- 0;
    while ((i < (32 * (_LEN %/ 32)))) {
      x0 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 32)));
      x1 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 32)));
      x2 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 32)));
      x3 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 32)));
      i <- (i + 32);
      (x0, x1, x2, x3) <@ M.__4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      offset x0)));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      offset x1)));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      offset x2)));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      offset x3)));
      offset <- (offset + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      buf0 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      offset t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      offset t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      offset t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      offset t3)));
      i <- (i + 8);
      offset <- (offset + 8);
    }
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0,  _1) <@ RW.MM.__a_ilen_write_upto8 (buf0, offset, 0, (_LEN %% 8),
      t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _2,  _3) <@ RW.MM.__a_ilen_write_upto8 (buf1, offset, 0, (_LEN %% 8),
      t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _4,  _5) <@ RW.MM.__a_ilen_write_upto8 (buf2, offset, 0, (_LEN %% 8),
      t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _6,  _7) <@ RW.MM.__a_ilen_write_upto8 (buf3, offset, 0, (_LEN %% 8),
      t3);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc __squeeze_avx2x4 (st:W256.t Array25.t, buf0:W8.t A.t,
                         buf1:W8.t A.t, buf2:W8.t A.t,
                         buf3:W8.t A.t, _RATE8:int) : W256.t Array25.t *
                                                             W8.t A.t *
                                                             W8.t A.t *
                                                             W8.t A.t *
                                                             W8.t A.t = {
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    offset <- 0;
    _LEN <- _ASIZE;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    if ((0 < iTERS)) {
      i <- 0;
      while ((i < iTERS)) {
        st <@ M._keccakf1600_avx2x4 (st);
        (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, 
        buf1, buf2, buf3, offset, _RATE8, st);
        i <- (i + 1);
      }
    } else {
      
    }
    if ((0 < lO)) {
      st <@ M._keccakf1600_avx2x4 (st);
      (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, buf1,
      buf2, buf3, offset, lO, st);
    } else {
      
    }
    return (st, buf0, buf1, buf2, buf3);
  }
}.


(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_bcast_avx2x4_ll: islossless MM.__addstate_bcast_avx2x4.
proof.
proc.
seq 7: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.

lemma addstate_avx2x4_ll: islossless MM.__addstate_avx2x4.
proof.
proc.
seq 7: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
by auto => /#.
qed.

lemma absorb_bcast_avx2x4_ll: islossless MM.__absorb_bcast_avx2x4.
proof.
proc.
seq 4: true => //.
 call addstate_bcast_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_bcast_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 wp; call addstate_bcast_avx2x4_ll.
 by auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

hoare absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _r8 _tb:
 MM.__absorb_bcast_avx2x4
 : st=_st /\ buf=_buf /\ _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8.
proof.
proc.
admitted.

phoare absorb_bcast_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf _r8 _tb:
 [ MM.__absorb_bcast_avx2x4
 : st=_st /\ buf=_buf /\ _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf)
            (_l1 ++ to_list _buf)
            (_l2 ++ to_list _buf)
            (_l3 ++ to_list _buf)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8
  ] = 1%r.
proof.
by conseq absorb_bcast_avx2x4_ll (absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _r8 _tb).
qed.

lemma absorb_avx2x4_ll: islossless MM.__absorb_avx2x4.
proof.
proc.
seq 4: true => //.
 call addstate_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  call addstate_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 by wp; call addstate_avx2x4_ll; auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.

hoare absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _r8 _tb:
 MM.__absorb_avx2x4
 : st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
 _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8.
admitted.

phoare absorb_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _r8 _tb:
 [ MM.__absorb_avx2x4
 : st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
 _RATE8 = _r8 /\ _TRAILB=_tb
 /\ aT = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ size _l3 = size _l0
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ to_list _buf0)
            (_l1 ++ to_list _buf1)
            (_l2 ++ to_list _buf2)
            (_l3 ++ to_list _buf3)
            res.`1
           /\ res.`2 = (size _l0 + _ASIZE) %% _r8
  ] = 1%r.
proof.
by conseq absorb_avx2x4_ll (absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _r8 _tb).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_avx2x4_ll: islossless MM.__dumpstate_avx2x4.
proof.
proc.
seq 3: true => //.
 while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
by auto => /#.
qed.

hoare dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st:
 MM.__dumpstate_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`2 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3
  /\ res.`5 = _off + _len.
admitted.

phoare dumpstate_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _off _len _st:
 [ MM.__dumpstate_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`2 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3
  /\ res.`5 = _off + _len
  ] = 1%r.
proof.
by conseq dumpstate_avx2x4_ll (dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st).
qed.

lemma squeeze_avx2x4_ll: islossless MM.__squeeze_avx2x4.
proof.
proc.
seq 5: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.

hoare squeeze_avx2x4_h _buf0 _buf1 _buf2 _buf3 _st _r8:
 MM.__squeeze_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==>
    res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ to_list res.`2 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0)
 /\ to_list res.`3 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1)
 /\ to_list res.`4 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2)
 /\ to_list res.`5 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3).
admitted.

phoare squeeze_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _st _r8:
 [ MM.__squeeze_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==>
    res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ to_list res.`2 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0)
 /\ to_list res.`3 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1)
 /\ to_list res.`4 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2)
 /\ to_list res.`5 = SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3)
 ] = 1%r.
proof.
by conseq squeeze_avx2x4_ll (squeeze_avx2x4_h _buf0 _buf1 _buf2 _buf3 _st _r8).
qed.

end KeccakArrayAvx2x4.


