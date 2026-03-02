require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.
from CryptoSpecs require import Keccak1600_Spec.
from JazzEC require import Keccak1600_Jazz.

import SLH64.
import IntOrder.

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


lemma m_ilen_read_upto8_at_ll: islossless M.__m_ilen_read_upto8_at
by islossless.

lemma m_ilen_read_upto16_at_ll: islossless M.__m_ilen_read_upto16_at
by islossless.

lemma m_ilen_read_upto32_at_ll: islossless M.__m_ilen_read_upto32_at
by islossless.

lemma m_ilen_read_bcast_upto8_at_ll: islossless M.__m_ilen_read_bcast_upto8_at
by islossless.

lemma m_ilen_write_upto8_ll: islossless M.__m_ilen_write_upto8
by islossless.

lemma m_ilen_write_upto16_ll: islossless M.__m_ilen_write_upto8
by islossless.

lemma m_ilen_write_upto32_ll: islossless M.__m_ilen_write_upto32
by islossless.

lemma m_rlen_read_upto8_ll: islossless M.__m_rlen_read_upto8
by islossless.

lemma m_rlen_write_upto8_ll: islossless M.__m_rlen_write_upto8
by islossless.



abstract theory ReadWriteArray.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import PolyArray as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import WArray as WA
 with op size <- _ASIZE.

module MM = {
  proc __a_ilen_read_upto8_at (buf:W8.t A.t, offset:int, dELTA:int,
                               lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var aT8:int;
    var t16:W64.t;
    var t8:W64.t;
    if ((((aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      aT8 <- (aT - cUR);
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ M.__SHLQ (w, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          w <@ M.__SHLQ (w, aT8);
          dELTA <- (dELTA + ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          lEN <- (lEN - ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          aT8 <- ((8 <= (4 + aT8)) ? 8 : (4 + aT8));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT8 < 8) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <- (dELTA + ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          lEN <- (lEN - ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          t16 <@ M.__SHLQ (t16, aT8);
          w <- (w `|` t16);
          aT8 <- ((8 <= (2 + aT8)) ? 8 : (2 + aT8));
        } else {
          
        }
        if ((aT8 < 8)) {
          if ((1 <= lEN)) {
            t8 <-
            (zeroextu64
            (get8_direct (WA.init8 (fun i => buf.[i]))
            (offset + dELTA)));
            t8 <- (t8 `|` (W64.of_int (256 * (tRAIL %% 256))));
            dELTA <- (dELTA + 1);
            lEN <- (lEN - 1);
            t8 <@ M.__SHLQ (t8, aT8);
            w <- (w `|` t8);
            aT8 <- (aT8 + 1);
            if (((aT8 < 8) /\ ((tRAIL %% 256) <> 0))) {
              aT8 <- (aT8 + 1);
              tRAIL <- 0;
            } else {
              
            }
          } else {
            if (((tRAIL %% 256) <> 0)) {
              t8 <- (W64.of_int (tRAIL %% 256));
              t8 <@ M.__SHLQ (t8, aT8);
              w <- (w `|` t8);
              tRAIL <- 0;
              aT8 <- (aT8 + 1);
            } else {
              
            }
          }
        } else {
          
        }
      }
      aT <- (cUR + aT8);
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto16_at (buf:W8.t A.t, offset:int, dELTA:int,
                                lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var aT16:int;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if ((((aT < cUR) \/ ((cUR + 16) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      aT16 <- (aT - cUR);
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        w <@ M.__SHLDQ (w, aT16);
        dELTA <- (dELTA + (16 - aT16));
        lEN <- (lEN - (16 - aT16));
        aT16 <- 16;
      } else {
        if ((8 <= aT16)) {
          w <- (set0_128);
          (dELTA, lEN, tRAIL, aT16, t64_1) <@ __a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, 8, aT16);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT16, t64_0) <@ __a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, 0, aT16);
          w <- (zeroextu128 t64_0);
          (dELTA, lEN, tRAIL, aT16, t64_1) <@ __a_ilen_read_upto8_at (
          buf, offset, dELTA, lEN, tRAIL, 8, aT16);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
      aT <- (cUR + aT16);
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto32_at (buf:W8.t A.t, offset:int, dELTA:int,
                                lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var aT32:int;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if ((((aT < cUR) \/ ((cUR + 32) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      aT32 <- (aT - cUR);
      if (((aT32 = 0) /\ (32 <= lEN))) {
        w <-
        (get256_direct (WA.init8 (fun i => buf.[i])) (offset + dELTA));
        aT32 <- (aT32 + 32);
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= aT32)) {
          w <- (set0_256);
          (dELTA, lEN, tRAIL, aT32, t128_1) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, 16, aT32);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, aT32, t128_0) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, 0, aT32);
          (dELTA, lEN, tRAIL, aT32, t128_1) <@ __a_ilen_read_upto16_at (
          buf, offset, dELTA, lEN, tRAIL, 16, aT32);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        }
      }
      aT <- (cUR + aT32);
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
    if ((((aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
        w256 <@ M.__SHLQ_256 (w256, aT8);
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

lemma a_ilen_read_upto16_at_ll: islossless MM.__a_ilen_read_upto16_at
by islossless.

lemma a_ilen_read_upto32_at_ll: islossless MM.__a_ilen_read_upto32_at
by islossless.

lemma a_ilen_read_bcast_upto8_at_ll: islossless MM.__a_ilen_read_bcast_upto8_at
by islossless.

lemma a_ilen_write_upto8_ll: islossless MM.__a_ilen_write_upto8
by islossless.

lemma a_ilen_write_upto16_ll: islossless MM.__a_ilen_write_upto8
by islossless.

lemma a_ilen_write_upto32_ll: islossless MM.__a_ilen_write_upto32
by islossless.

lemma a_rlen_read_upto8_ll: islossless MM.__a_rlen_read_upto8
by islossless.

lemma a_rlen_write_upto8_ll: islossless MM.__a_rlen_write_upto8
by islossless.



op subread_pre cur at len tb =
 0 <= cur && 0 <= at && 0 <= len && 0 <= tb < 256
 && at+len+b2i (tb<>0) <= 200
 && (cur<=at || len=0 && tb=0).

op bytes_at size cur at l=
 take size (drop cur (nseq at W8.zero++l)++nseq size W8.zero).

lemma size_bytes_at sz cur at l:
 0 <= sz =>
 size (bytes_at sz cur at l) = sz.
proof.
move=> Hsz; rewrite size_take // size_cat size_nseq.
smt(size_ge0).
qed.

lemma sub0 (buf: W8.t A.t) off:
 sub buf off 0 = [].
proof. by rewrite -size_eq0 size_sub /#. qed.

lemma nth_bytes_at sz cur at buf off len tb i:
 0 <= sz =>
 subread_pre cur at len tb =>
 nth W8.zero (bytes_at sz cur at (A.sub buf off len++[W8.of_int tb])) i
 = if 0 <= at-cur <= i < sz
   then nth W8.zero (sub buf off len++[W8.of_int tb]) (cur+i-at)
   else W8.zero.
proof.
move=> /> ???????[H|H].
+ case: (0 <= i < sz) => C; last first.
   by rewrite nth_out 1:size_bytes_at // ifF /#.
  case: (i < at-cur) => C1.
   rewrite ifF 1:/# nth_take 1..2:/# nth_cat ifT.
    by rewrite size_drop // !size_cat size_sub //= size_nseq /#.
   rewrite nth_drop 1..2:/# nth_cat ifT 1:size_nseq 1:/#.
   by rewrite nth_nseq 1:/#.
  rewrite ifT 1:/# nth_take 1..2:/# nth_cat.
  rewrite size_drop 1:/# !size_cat size_sub //= size_nseq //=.
  case: (i < at + (len + 1) - cur) => C2.
   by rewrite ifT 1:/# nth_drop 1..2:/# nth_cat size_nseq ifF /#.
  rewrite ifF 1:/# nth_nseq 1:/# nth_out //.
  by rewrite size_cat size_sub /#.
move=> []->->; rewrite sub0 /= /bytes_at.
case: (0 <= i < sz) => C; last first.
 rewrite nth_out // size_take // size_cat.
 by rewrite size_drop // size_cat !size_nseq /#.
rewrite nth_take 1..2:/# nth_cat nth_drop 1..2:/#.
rewrite nth_cat !size_drop // !size_cat !size_nseq /=.
case: (cur+i<at) => C1.
 by rewrite !nth_nseq /#.
rewrite nth_out 1:size_nseq 1:/#.
by rewrite nth_nseq /#.
qed.

op subread_spec
 (size: int)
 (buf: W8.t A.t) (off dlt len tb cur at: int)
 (dlt' len' tb' at': int) (w: W8.t list)
 : bool =
 0 <= size =>
 subread_pre cur at len tb =>
 subread_pre (cur+size) at' len' tb'
 /\ w = bytes_at size cur at (sub buf (off+dlt) len ++ [W8.of_int tb])
 /\ at+len+b2i(tb<>0)=at'+len'+b2i(tb'<>0)
 /\ (tb'=tb || len'=0 && tb'=0)
 /\ dlt+len = dlt'+len'
 /\ at' = max at
              (min (cur+size)
                   (at+len+b2i (tb<>0)))
 /\ len' = max 0 (len - (max 0 (cur+size-at)))
 .

lemma subread_specP N buf off dlt len trail cur at dlt' at' w':
 0 <= N =>
 cur <= at =>
 subread_pre cur at len trail =>
 subread_spec N buf off dlt len trail cur at dlt' 0 0 at' w' =>
 at' = at + len + b2i (trail%%256<>0)
 /\
 dlt' = dlt + len
 /\
 bytes2state (nseq at W8.zero ++ sub buf (off+dlt) len ++ [W8.of_int trail])
 = bytes2state (nseq cur W8.zero++w').
proof.
move=> Hn Hcur Hpre Hspec.
move: (Hpre) (Hspec Hn Hpre) => {Hspec} /> ???? H1 H2 H3 H4 H5.
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
move=> i Hi; rewrite nth_bytes_at 1..2:/# !W8u8.get_zero /=.
case: (0 <= _at - _cur <= i < 8) => C//.
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
move=> i Hi; rewrite nth_bytes_at 1..2:/# !W32u8.get_zero /=.
case: (0 <= _at - _cur <= i < 32) => C//.
by rewrite nth_cat ?size_sub 1:/# sub0 /=.
qed.

(*
lemma subread_spec_finished N buf off dlt cur at:
 at < cur =>
 subread_spec N buf 
*)

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


lemma subread_full buf off len tb at dlt' len' tb' at' wl:
 subread_pre 0 at len tb => 
 subread_spec 200 buf off 0 len tb 0 at dlt' len' tb' at' wl =>
 at+len+b2i (tb<>0) <= 200 =>
 len' = 0 /\ tb' = 0
 /\ at'=at+len+b2i(tb<>0) /\ dlt'=len
 /\ bytes2state (u8zeros at ++ sub buf off len ++ [W8.of_int tb])
    = bytes2state wl.
proof.
move=> Hpre Hspec.
move: (Hspec _ Hpre) => //.
move: Hpre => /= Hpre [#] Hpre' -> /= *.
do (split; first smt()).
by rewrite bytes_at_absorb 1..2:/#.
qed.


lemma subread_finished size buf off len tb at dlt' len' tb' at' wl:
 0 <= size =>
 subread_pre 0 at len tb => 
 subread_spec size buf off 0 len tb 0 at dlt' len' tb' at' wl =>
 len' = 0 =>
 tb' = 0 =>
 at'= max at (at+len+b2i(tb<>0)) /\ dlt'=len
 /\ bytes2state (u8zeros at ++ sub buf off len ++ [W8.of_int tb])
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

(*
lemma subread_finish R size buf off dlt len tb cur at dlt' len' tb' at' wl:
 0 <= size =>
 subread_pre cur at len tb => 
 subread_spec size buf off dlt len tb cur at dlt' len' tb' at' wl =>
 at+len+b2i (tb<>0) <= R =>
 R <= cur+size =>
 len' = 0 /\ tb' = 0
 /\ at'=at+len+b2i(tb<>0) /\ dlt'=dlt+len.
proof.
move=> Hsize Hpre Hspec.
move: (Hspec Hsize Hpre).
move: {Hspec} Hpre => /> ??? Hinv Hend _ _ ?? Hat HH.
by move=> H1 H2 /#.
qed.
*)

require import StdOrder.
import IntOrder.

lemma subread_spec_cat N1 N2 buf off dlt dlt' dlt'' len len' len'' tb tb' tb'' cur at at' at'' w' w'':
 0 <= N1 => 0 <= N2 =>
 subread_spec N1 buf off dlt len tb cur at dlt' len' tb' at' w' =>
 subread_spec N2 buf off dlt' len' tb' (cur+N1) at' dlt'' len'' tb'' at'' w'' =>
 subread_spec (N1+N2) buf off dlt len tb cur at dlt'' len'' tb'' at'' (w'++w'').
proof.
move=> HN1 HN2 H1 H2 _ Hpre1.
move: (H1 HN1 Hpre1) => []Hpre2 {H1} [#]->*.
move: (H2 HN2 Hpre2) => []Hpre3 {H2} [#]->*.
split; first smt().
split; last smt().
apply (eq_from_nth W8.zero).
 by rewrite size_cat !size_bytes_at /#.
rewrite size_cat !size_bytes_at 1..2:/# => i Hi.
rewrite nth_cat size_bytes_at 1:/#.
case: (i<N1) => Ci.
 by rewrite !nth_bytes_at /#.
case: (at<cur) => Hcur.
 by rewrite !nth_bytes_at /#.
rewrite !nth_bytes_at 1..4:/#.
rewrite (:cur+N1+(i-N1)-at'=cur+i-at') 1:/#.
case: (at'<cur+N1) => Cat'.
 have ->: len'=0 by smt().
 have ->: tb'=0 by smt().
 have ?: len < N1 by smt().
 rewrite ifF 1:/# ifT 1:/#.
 by rewrite nth_out // size_cat size_sub /#.
case: (at<=cur+N1) => Cat.
 rewrite ifT 1:/# ifT 1:/#.
 have : at'=cur+N1 by smt().
 move => />.
 case: (tb'=tb) => Ctb.
  rewrite nth_cat ?size_sub 1:/#.
  case: (cur + i - (cur + N1) < len - (cur + N1 - at)) => CC.
   by rewrite nth_sub 1:/# nth_cat ?size_sub 1:/# ifT 1:/# nth_sub 1:/# /#.
  case: (tb=0) => Etb.
   by rewrite nth_cat ?size_sub 1:/# ifF 1:/# /#.
  rewrite nth_cat ?size_sub 1:/#.
  case: (cur + i - at < len) => ?.
   by rewrite nth_sub /#.
  smt().
 have ->: len'=0 by smt().
 have ->: tb'=0 by smt().
 rewrite sub0 /= nth_cat size_sub 1:/#.
 by rewrite ifF 1:/# nth_out /#.
smt().
qed.

lemma bytes_at8_zero cur at:
 0 <= cur =>
 bytes_at 8 cur at [W8.zero] = u64bytes W64.zero.
proof.
move=> *.
rewrite /bytes_at; apply (eq_from_nth W8.zero).
 by rewrite size_to_list size_take 1:/# !size_cat size_drop 1:/# size_cat !size_nseq /= /#.
rewrite size_take 1:/# !size_cat size_drop 1:/# size_cat !size_nseq /=.
move=> i Hi.
rewrite nth_take 1..2:/# nth_cat ?size_drop 1:/# u64bytes0 nth_drop 1..2:/# nth_cat !nth_u8zeros /#.
qed.

hoare a_ilen_read_upto8_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5).
proof.
proc; simplify.
if => //.
 auto => /> [[H|H]|H].
 + move=> _; rewrite /subread_pre => /> ??????.
   rewrite (:!_cur<=_at) 1:/# /= => [[Elen Etb]].
   rewrite !Elen !Etb; split; first smt().
   split.
    rewrite sub0 bytes_at8_zero /#. 
   smt().
  + apply subread_spec_ahead8; smt().
  apply subread_spec_empty8; smt().
sp; if => //.
 (* 8 <= lEN *)
 wp; ecall (SHLQ_h w aT8); auto => /> *.
 split; first smt().
 move=> *; split; first smt().
 split.
  admit.
 smt().
(* subread *)
if => //=.
 (* 4 <= lEN *)
 admit.
(* lEN < 4 *)
admit.
qed.



phoare a_ilen_read_upto8_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto8_at_ll
          (a_ilen_read_upto8_at_h _buf _off _dlt _len _trail _cur _at).
qed.

hoare a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5).
admitted.

phoare a_ilen_read_upto16_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto16_at_ll
          (a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at).
qed.

hoare a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5).
admitted.

phoare a_ilen_read_upto32_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto32_at_ll
          (a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at).
qed.

require import Keccak_bindings.

lemma trunc_zext_u64_u128 w:
 truncateu64 (W2u64.zeroextu128 w) = w.
proof.
rewrite zeroextu128E /truncateu64.
admitted.

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
 inline*; auto => /> &m *; split => *.
 + rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr; congr=> />.
   by (do split); rewrite /W64.(`<<`) trunc_zext_u64_u128 of_uintK modz_small 1:/# of_uintK modz_small /#.
 + by rewrite /W64.(`<<`) trunc_zext_u64_u128; congr; congr.
inline *.
rcondf {1} 9; first by auto.
rcondf {1} 10; first by auto.
admitted.

end ReadWriteArray.
