require import AllCore IntDiv List StdOrder.

require import BitEncoding.
import BS2Int.

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
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA))));
        w <@ M.__SHLQ (w, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
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
          (get16_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
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
            (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
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
        (get128_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA))));
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
        aT8 <- 8;
      } else {
        aT8 <- (aT - cUR);
        (dELTA, lEN, tRAIL, aT, w) <@ __a_ilen_read_upto8_at (buf, offset,
        dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (zeroextu128 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
        w256 <@ M.__SHLQ_256 (w256, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      }
      aT <- (cUR + aT8);
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

lemma buf4_expand buf base:
  0 <= base =>
  base + 8 < _ASIZE =>
  (map (fun (j : int) => (WA.init8 (ReadWriteArray.A."_.[_]" buf)).[base + j]) (iota_ 0 4)) =
  [buf.[base]; buf.[base + 1]; buf.[base + 2]; buf.[base + 3]].
proof.
  move => H0 H1.
  rewrite (eq_from_nth W8.zero _ ([buf.[base]; buf.[base + 1];
                                   buf.[base + 2]; buf.[base + 3]])).
     + rewrite size_map size_iota /#.
     + rewrite size_map size_iota lez_maxr 1:/# => i0 i0_bnd.
       rewrite (nth_map 0 W8.zero); first by smt(size_iota).
       rewrite nth_iota 1:/# add0r /WA.init8 /=.
       rewrite initE ifT. by rewrite (ltr_trans (base + 8)) /#.  
  smt(). smt().
qed.


lemma posu64_0s x i _buf pos:
  0 <= x =>
  0 <= i < min 8 x =>
  (get64_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x
  \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1.
  rewrite /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  case(8 < x) => x_max.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota).
  have->: 0 <= nth witness (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota). smt().
qed.


lemma preu32_0s x i _buf pos:
  0 <= x =>
  4 + x <= i < 8 =>
  zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x
  \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1.
  pose a:= (get32_direct (WA.init8 ("_.[_]" _buf)) pos).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 32) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 32 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb.
  have aux: 32 <= nth 0 (iota_ 0 8) i * 8 + x0 - 8 * x < 64. smt(nth_iota).
  rewrite get_bits2w 1:/# get_w2bits get_out /#. smt().
qed.


lemma posu32_0s x i _buf pos:
  0 <= x =>
  0 <= i < min 8 x =>
  zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x
  \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1.
  pose a:= (get32_direct (WA.init8 ("_.[_]" _buf)) pos).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 32) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 32 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  case(8 < x) => x_max.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota).
  have->: 0 <= nth witness (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota). smt().
qed.


lemma u32_word x i _buf pos:
  0 <= x =>
  min 8 x <= i < min 8 (4 + x) =>
  zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x
  \bits8 nth witness (iota_ 0 8) i =
  (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
  \bits8 nth 0 (iota_ 0 (min 4 (8-x))) (i-x).
proof.
  move => H0 H1.
  pose a:= (get32_direct (WA.init8 ("_.[_]" _buf)) pos).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 32) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W32.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 32 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ (a \bits8 nth 0 (iota_ 0 (min 4 (8-x))) (i-x))).
  move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  case(8 <= x) => x_max.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota).
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/# get_bits2w. smt(nth_iota).  
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_w2bits /(\bits8) initE ifT 1:/# /=.
  smt(nth_iota). 
  rewrite /(\bits8) /#.
qed.

lemma preu16_0s x y i _buf pos:
  0 <= y =>
  0 <= x =>
  y + 2 + x <= i < 8 =>
  zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos+y))
   `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1 H2.
  pose a:= (get16_direct (WA.init8 ("_.[_]" _buf)) (pos+y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 16) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 16 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb.
  have aux: 16 <= nth 0 (iota_ 0 8) i * 8 + x0 - 8 * (y + x) < 64. smt(nth_iota).
  rewrite get_bits2w 1:/# get_w2bits get_out /#.
  smt().
qed.

lemma posu16_0s x y i _buf pos:
  0 <= y =>
  0 <= x =>
  0 <= i < min 8 (y + x) =>
  zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + y))
    `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1 H2.
  pose a:= (get16_direct (WA.init8 ("_.[_]" _buf)) (pos + y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 16) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 16 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota).
  smt().
qed.

lemma u16_word x y i _buf pos:
  0 <= y =>
  0 <= x =>
  min 8 (y+x) <= i < min 8 (y + 2 + x) =>
  zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + y))
    `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i =
  (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + y))
  \bits8 nth 0 (iota_ 0 2) (i-y-x).
proof.
  move => H0 H1 H2.
  pose a:= (get16_direct (WA.init8 ("_.[_]" _buf)) (pos + y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 16) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W16.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 16 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ (a \bits8 nth 0 (iota_ 0 2) (i-y-x))).
  move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb.
  case(8 <= y + x) => *.
  + rewrite !get_out /#.
  + rewrite /(\bits8)initE ifT 1:/# /= get_bits2w. smt(nth_iota).
    rewrite get_w2bits !nth_iota /#. smt().
qed.

lemma preu8_0s x y i _buf pos:
  0 <= y =>
  0 <= x =>
  y + 1 + x <= i < 8 =>
  zeroextu64 (get8_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos+y))
   `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1 H2.
  pose a:= (get8_direct (WA.init8 ("_.[_]" _buf)) (pos+y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 8) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 8 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb.
  have aux: 8 <= nth 0 (iota_ 0 8) i * 8 + x0 - 8 * (y + x) < 64. smt(nth_iota).
  rewrite get_bits2w 1:/# get_w2bits get_out /#.
  smt().
qed.

lemma posu8_0s x y i _buf pos:
  0 <= y =>
  0 <= x =>
  0 <= i < min 8 (y + x) =>
  zeroextu64 (get8_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + y))
    `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1 H2.
  pose a:= (get8_direct (WA.init8 ("_.[_]" _buf)) (pos + y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 8) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 8 = size (w2bits a) by rewrite size_w2bits.
  rewrite bs2intK /(\bits8) (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  case(8 < x) => x_max.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota).
  have->: 0 <= nth witness (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb get_out; smt(nth_iota). smt().
qed.

lemma u8_word x y i _buf pos:
  0 <= y =>
  0 <= x =>
  min 8 (y + x) <= i < min 8 (y + 1 + x) =>
  zeroextu64 (get8_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + y))
    `<<<` 8 * (y + x) \bits8 nth witness (iota_ 0 8) i =
  [get8 (WA.init8 ("_.[_]" _buf)) (pos + y)].[i - y - x].
proof.
  move => H0 H1 H2.
  pose a:= (get8_direct (WA.init8 ("_.[_]" _buf)) (pos + y)).
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small. 
  + split. smt(bs2int_ge0). move =>*.
  + rewrite (ltr_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite (int2bs_cat 8) 1:/# pdiv_small.
  + split. smt(bs2int_ge0). move =>*. 
  + rewrite (ltr_le_trans (2^size (W8.w2bits a))). rewrite bs2int_le2Xs. smt().
  rewrite int2bs0 W64_bits2w_cat_nseq0. 
  have->: 8 = size (w2bits a) by rewrite size_w2bits.
  rewrite /(\bits8) bs2intK.
  rewrite (W8.ext_eq _ ([get8 (WA.init8 ("_.[_]" _buf)) (pos+y)].[i-y-x])).
  move => x0 x0_bnd.
  rewrite initE ifT 1:/# /=.
  rewrite (nth_change_dfl 0 witness) 1:size_iota 1:/#.
  have->: 0 <= nth 0 (iota_ 0 8) i * 8 + x0 < 64 by smt(nth_iota).
  rewrite andaE andTb nth_iota 1:/# /=.
  case(i - y - x = 0) => u8_eq.
  + rewrite get_bits2w 1:/# get_w2bits /#.
  + smt().
  smt().
qed.

lemma preTrail_0s x off i _trail:
  0 <= x =>
  0 <= off =>
  0 <= _trail =>
  _trail < 256 =>
  off + 1 + x <= i < 8 =>
  W64.of_int _trail `<<<` 8 * (off + x) \bits8 nth witness (iota_ 0 8) i =
  W8.zero.
proof.
  move => H0 H1 H2 H3 H4.
  rewrite nth_iota 1:/# /(\bits8) /= (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
    rewrite initE ifT 1:/# /= andaE. have->: 0 <= i * 8 + x0 < 64 by smt().
    rewrite andTb /of_int get_bits2w 1:/# pmod_small 1:/#.
    rewrite (int2bs_cat 8) 1:/# pdiv_small 1:/# nth_cat size_int2bs ifF 1:/# int2bs0.
    rewrite nth_nseq /#. smt().
qed.

lemma posTrail_0s x i off _trail:
  0 <= x =>
  0 <= off =>
  0 <= i < min 8 (off + x) =>
  0 <= _trail =>
  _trail < 256 =>
  W64.of_int _trail `<<<` 8 * (off + x) \bits8 nth witness (iota_ 0 8) i = W8.zero.
proof.
  move => H0 H1 H2 H3 H4.
  rewrite /zeroextu64 {1}/W64.of_int /to_uint pmod_small 1:/#.
  rewrite nth_iota 1:/# /(\bits8) /= (W8.ext_eq _ W8.zero). move => x0 x0_bnd.
    rewrite initE ifT 1:/# /=. have->: 0 <= i * 8 + x0 < 64 by smt().
    rewrite andaE andTb get_out; smt(nth_iota).
  smt().
qed.

lemma trail_word x i off _trail:
  0 <= x =>
  0 <= off =>
  0 <= _trail =>
  _trail < 256 =>
  min 8 (off+x) <= i < min 8 (off + 1 + x) =>
  W64.of_int _trail `<<<` 8 * (off + x) \bits8 nth witness (iota_ 0 8) i =
  W8.of_int _trail.
proof.
  move => H0 H1 H2 H3 H4.
  rewrite /W64.of_int !pmod_small 1:/#.
  rewrite nth_iota 1:/# /(\bits8) /= (W8.ext_eq _ (W8.of_int _trail)). move => x0 x0_bnd.
    rewrite initE ifT 1:/# /=. have->: 0 <= i * 8 + x0 < 64 by smt().
    rewrite andaE andTb /W8.of_int pmod_small 1:/# !get_bits2w ..2:/#.
    rewrite (int2bs_cat 8) 1:/# pdiv_small 1:/# nth_cat size_int2bs ifT /#.
  smt().
qed.

lemma trail_simplify y x a:
    0 <= x =>
    0 <= a =>
    W64.of_int (256 * y) `<<<` 8 * (a + x) = W64.of_int y `<<<` 8 * (a + 1 + x).
proof.
  move => H0 H1. have->: 256 = 2^8 by smt(). rewrite mulrC -shlMP 1:/# shlw_add /#.
qed.


lemma compose2u8 _buf pos x _cur _at _len _trail:
  8 <= _len + x =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 8 =>
  6 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x)
 = bytes_at 8 _cur _at (sub _buf pos _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8.
  pose w0:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose l1:= u64bytes w0.
  pose l2:= bytes_at 8 _cur _at (sub _buf pos _len ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(2 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# H3 /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_mkseq.
        rewrite size_nseq !lez_maxr ..4:/# ifT 1:/# nth_cat size_drop 1:/# size_nseq.
        rewrite ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# H3 /=.
        rewrite (posu16_0s x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_nseq.
        rewrite size_mkseq ifT 1:/# nth_cat size_drop 1:/# size_nseq ifT 1:/#.
        rewrite nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# H3 /=.
        rewrite (u16_word x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_nseq.
        rewrite size_mkseq ifT 1:/# nth_cat size_drop 1:/# size_nseq ifF 1:/#.
        rewrite nth_cat nth_mkseq 1:/# size_mkseq ifT 1:/# !lez_maxr ..3:/# /(\bits8) /=.
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      smt().
qed.


lemma compose4u8 _buf _off _dlt _at _cur _len _trail:
  4 <= _len =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur < 8 =>
  4 <= _at - _cur =>
  0 <= _off + _dlt =>
  _off + _dlt + 8 < _ASIZE =>
u64bytes (zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (_off + _dlt)) `<<<` 8 * (_at - _cur)) =
bytes_at 8 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7.
  pose l1:= u64bytes (zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)) `<<<` 8 * (_at - _cur)).
  pose l2:= bytes_at 8 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat size_mkseq /=.
    rewrite !size_nseq !lez_maxr /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list_in 1:/# get32E /WA.init8 W4u8.Pack.init_of_list. 
    rewrite (buf4_expand) ..2:/# W64.wlslE /(\bits8).
    pose b:= (W4u8.Pack.of_list ([_buf.[_off + _dlt]; _buf.[_off + _dlt + 1]; _buf.[_off + _dlt + 2]; _buf.[_off + _dlt + 3]])).
    rewrite /zeroextu64 /W64.of_int /W32.to_uint pmod_small.
    rewrite bs2int_ge0 andaE andTb.
    rewrite (ltr_trans (2^(size (JWord.W32.w2bits(pack4_t b))))).
    + by rewrite bs2int_le2Xs.
    + by rewrite size_w2bits.
    rewrite (int2bs_cat 32 64) 1:/# divz_small.
    rewrite bs2int_ge0 andaE andTb.
    rewrite (ltr_le_trans (2^(size (w2bits (pack4_t b))))).
    + by rewrite bs2int_le2Xs.
    + by rewrite size_w2bits.
    have{1}->: 32 = size (w2bits (pack4_t b)); first by rewrite size_w2bits.
    rewrite bs2intK /W64.bits2w /=.
    rewrite (W8.init_ext (fun j => (W64.init (fun j0 => (W64.init (nth false (w2bits (pack4_t b) ++ int2bs 32 0))).[j0-8*(_at-_cur)])).[i*8+j]) (fun j => (W64.init (nth false (w2bits (pack4_t b) ++ int2bs 32 0))).[i * 8 + j - 8 * (_at - _cur)])).
    + move => x x_bnd /=.
      rewrite W64.initE /= (W64.initE (nth false (w2bits (pack4_t b) ++ int2bs 32 0))) /#.
    rewrite /l2 /bytes_at /sub nth_take ..2:/# drop_cat_le size_nseq ifT 1:/#.
    rewrite !nth_cat !size_cat size_drop 1:/# size_nseq size_mkseq /=.
    case(i < _at - _cur) => i_min.
    + rewrite !ifT ..2:/# nth_drop ..2:/# nth_nseq 1:/#.
      rewrite (W8.ext_eq _ W8.zero). move => x x_bnd.
      rewrite W8.initE ifT 1:/# /= W64.initE /#. smt().
    + rewrite ifT 1:/# ifF 1:/# ifT 1:/# nth_mkseq 1:/# !lez_maxr ..3:/# /=.
      rewrite (W8.ext_eq _ (_buf.[_off + _dlt + (i - (_at - _cur))])). move => x x_bnd.
      rewrite W8.initE ifT 1:/# /= W64.initE ifT 1:/# nth_cat size_w2bits ifT 1:/#.
      rewrite get_w2bits /b /pack4_t W32.initE ifT 1:/# /= W4u8.Pack.get_of_list /#.
      smt().
    smt().
qed.

lemma compose6u8 _buf pos x _cur _at _len _trail:
  6 <= _len =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 4 =>
  2 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8*x) `|`
   (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 4))
    `<<<` 8 * (4 + x))) = bytes_at 8 _cur _at (sub _buf pos _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8*x.
  pose w1:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) (pos + 4)) `<<<` 8*(4+x).
  pose l1:= u64bytes (w0 `|` w1).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos _len ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(6 + x <= i) => i_max.
        rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..4:/#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# posu16_0s ..3:/# ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq /sub size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + x) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posu16_0s ..3:/# ifT ifT 1:/# 1:size_cat.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => u16. 
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# u16_word ..3:/# ifT ifT 1:/# 1:size_cat.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      smt().
qed.

lemma compose8u8 _buf _off _dlt _at _cur _len _trail:
  8 <= _len =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur < 8 =>
  0 <= _at - _cur =>
  0 <= _off + _dlt =>
  _off + _dlt + 8 < _ASIZE =>
  u64bytes (get64_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf))
                         (_off + _dlt) `<<<` 8 * (_at - _cur)) =
bytes_at 8 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7.
  pose l1:= u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)
            `<<<` 8*(_at - _cur)).
  pose l2:= bytes_at 8 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(i < _at - _cur) => i_min.
        rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu64_0s ..2:/# ifT ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq.
        rewrite size_nseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + rewrite ifT ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite nth_to_list /get64_direct /pack8_t nth_cat size_drop 1:/# size_nseq.
        rewrite ifF 1:/# !nth_cat size_mkseq ifT 1:/# nth_mkseq 1:/# /=.
        rewrite (W8.ext_eq _ (_buf.[_off + _dlt + (i - max 0 (max 0 _at - _cur))])).
        move => x x_bnd. rewrite /(\bits8) initE ifT 1:/# /=.
        have->: 0 <= i * 8 + x < 64 by smt(). rewrite andaE andTb initE ifT 1:/# /=.
        rewrite initE ifT 1:/# /= initE ifT /#. smt().
      smt().
qed.

lemma compose_trail (_buf: W8.t A.t) pos _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur < 8 =>
  0 <= _at - _cur =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
 u64bytes (W64.of_int _trail `<<<` 8 * (_at - _cur)) =
 bytes_at 8 _cur _at (sub _buf pos 0 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8.
  pose w0:= W64.of_int _trail `<<<` 8 * (_at - _cur).
  pose l1:= u64bytes w0.
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 0 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(1 + (_at - _cur) <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preTrail_0s (_at-_cur) 0 i) ..5:/# ifF ifT 1:/#.
        rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /= nth_nseq /#.
      case(i < (_at-_cur)) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (posTrail_0s (_at-_cur) i 0)..5:/# ifT ifT 1:/# 1:size_cat ?size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (trail_word (_at-_cur) i 0) ..5:/# !ifT 1:/#.
        rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifF 1:/# /#.
      smt().
qed.

lemma compose1u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 8 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  (zeroextu64 (get8 (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
    `|` W64.of_int (256 * _trail) `<<<` 8 * x)
 = bytes_at 8 _cur _at (sub _buf pos 1 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. rewrite -shlw_or (trail_simplify _ x 0) ..2:/# /=.
  pose w0:= zeroextu64 (get8 (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= W64.of_int (_trail) `<<<` 8 * (1 + x).
  pose l1:= u64bytes (w0 `|` w1).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 1 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(2 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu8_0s x 0 _ _ pos) ..3:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /= nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (posu8_0s x 0 _ _ pos) ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 1 + x) => u8.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (u8_word x 0 _ _ pos) ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#.
        smt(). rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8) ifT 1:/# /get8 initE /#.
      move: u8. rewrite -lezNgt => over_u8.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu8_0s x 0 _ _ pos) ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifF 1:/# !or0w /#.
      smt().
qed.

lemma compose2u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 8 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
    `<<<` 8 * x) `|` (W64.of_int (_trail) `<<<` 8 * (2 + x)))
 = bytes_at 8 _cur _at (sub _buf pos 2 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  pose w0:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= W64.of_int (_trail) `<<<` 8 * (2 + x).
  pose l1:= u64bytes (w0 `|` w1).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 2 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(3 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /= nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (posu16_0s x 0 _ _ pos) ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 2 + x) => u16.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (u16_word x 0 _ _ pos) ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#.
        smt(). rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u16. rewrite -lezNgt => over_u16.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifF 1:/# !or0w /#.
      smt().
qed.

lemma compose3u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x <= 5 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
    `<<<` 8 * x) `|`
   (zeroextu64 (get8 (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 2)) `|`
   W64.of_int (256 * _trail) `<<<` 8 * (2 + x)))
 = bytes_at 8 _cur _at (sub _buf pos 3 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. rewrite -shlw_or trail_simplify ..2:/# /=.
  pose w0:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= zeroextu64 (get8 (WA.init8 ("_.[_]" _buf)) (pos + 2)) `<<<` 8 * (2 + x).
  pose w2:= W64.of_int (_trail) `<<<` 8 * (3 + x).
  pose l1:= u64bytes (w0 `|` (w1 `|` w2)).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 3 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(4 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# preu8_0s ..3:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /= nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (posu16_0s x 0 _ _ pos) ..3:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 2 + x) => u16.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (u16_word x 0 _ _ pos) ..3:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#.
        smt(). rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u16. rewrite -lezNgt => over_u16.
      case(i < 3 + (_at - _cur)) => u8.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# u8_word ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8) ifT 1:/#.
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite /get8 initE ifT /#. smt().
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# preu8_0s ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifF 1:/# !or0w /#.
      smt().
qed.

lemma compose4u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 4 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
  u64bytes
    ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x)
    `|`
   (W64.of_int _trail `<<<` 8 * (4 + x))) =
bytes_at 8 _cur _at (sub _buf pos 4 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= W64.of_int _trail `<<<` 8 * (4 + x).
  pose l1:= u64bytes (w0 `|` w1).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 4 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(5 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite nth_nseq. rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /#.
        smt().
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s..2:/# posTrail_0s..5:/# ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + x) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posTrail_0s ..5:/# !ifT 1:/#.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#.
        smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=. 
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => over_u32.
      case(i < 5 + x) => trail.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# trail_word ..5:/# !ifT 1:/#.
        rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq size_mkseq !ifF /#. smt().
      smt().
qed.


lemma compose5u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 4 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
  u64bytes
    ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
      `<<<` 8 * x) `|`
     ((zeroextu64 (get8 (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 4))
       `<<<` 8 * (4+x)) `|` (W64.of_int _trail `<<<` 8 * (5 + x)))) =
  bytes_at 8 _cur _at (sub _buf pos 5 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= zeroextu64 (get8_direct (WA.init8 ("_.[_]" _buf)) (pos + 4)) `<<<` 8 * (4 + x).
  pose w2:= W64.of_int _trail `<<<` 8 * (5 + x).
  pose l1:= u64bytes (w0 `|` (w1 `|` w2)).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 5 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(6 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu8_0s ..3:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite nth_nseq. rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /#.
        smt().
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + (_at - _cur)) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#.
        smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=. 
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => over_u32.
      case(i < 5 + (_at - _cur)) => u8.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# u8_word ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8) ifT 1:/#.
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite /get8 initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /#. smt().
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu8_0s ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq size_mkseq !ifF /#.
      smt().
qed.


lemma compose6u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  0 <= x =>
  x < 2 =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8*x) `|`
   (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 4))
    `<<<` 8 * (4 + x)) `|`
   (W64.of_int (_trail) `<<<` 8 * (6 + x)))
 = bytes_at 8 _cur _at (sub _buf pos 6 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H3 H4 H5 H6 H7 H8 H9 H10.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) (pos+ 4)) `<<<` 8 * (4 + x).
  pose w2:= W64.of_int _trail `<<<` 8 * (6 + x).
  pose l1:= u64bytes (w0 `|` w1 `|` w2).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 6 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(7 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..3:/# preTrail_0s ..5:/#.
        rewrite ifF ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#.
        smt(). rewrite nth_nseq. rewrite !size_cat size_drop 1:/# size_nseq size_mkseq /#.
        smt().
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# posu16_0s ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + x) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posu16_0s ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => over_u32.
      case(i < 6 + x) => u16.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# u16_word ..3:/#  posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq size_mkseq ifF 1:/# !or0w /#.
      smt().
qed.

lemma compose7u8_trail _buf pos x _cur _at _trail:
  0 <= _cur =>
  0 <= _at =>
  0 <= _trail =>
  _trail < 256 =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 4 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8*x) `|`
   (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 4))
    `<<<` 8 * (4 + x)) `|`
   (zeroextu64 (get8 (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 6)) `|`
   W64.of_int (256 * _trail) `<<<` 8 * (6 + x)))
 = bytes_at 8 _cur _at (sub _buf pos 7 ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. rewrite -shlw_or trail_simplify ..2:/# /=.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose w1:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) (pos+ 4)) `<<<` 8 * (4 + x).
  pose w2:= zeroextu64 (get8 (WA.init8 ("_.[_]" _buf)) (pos + 6)) `<<<` 8 * (6 + x).
  pose w3:= W64.of_int (_trail) `<<<` 8 * (7 + x).
  pose l1:= u64bytes (w0 `|` w1 `|` (w2 `|` w3)).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 7 ++ [W8.of_int _trail]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(7 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..3:/# preu8_0s ..3:/# trail_word ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq /#. smt().
        rewrite nth_cat nth_drop ..2:/# nth_cat size_mkseq size_drop 1:/# size_nseq.
        rewrite !ifF /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# posu16_0s ..3:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + (_at - _cur)) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posu16_0s ..3:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# /sub size_mkseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => over_u32.
      case(i < 6 + (_at - _cur)) => u16.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# u16_word ..3:/# posu8_0s ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..3:/# u8_word ..3:/# posTrail_0s ..5:/#.
        rewrite !ifT 1:/#. rewrite !size_cat size_drop 1:/# size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite ifT 1:/# /get8 initE ifT /#. smt().
      smt().
qed.

lemma compose2u8_trail0 _buf pos x _cur _at:
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 8 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8 * x)
 = bytes_at 8 _cur _at (sub _buf pos 2 ++ [W8.zero]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7.
  pose w0:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8 * x.
  pose l1:= u64bytes w0.
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 2 ++ [W8.zero]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#H2/=.
      case(2 + x <= i) => i_max.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (preu16_0s x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_mkseq.
        rewrite size_nseq !lez_maxr ..4:/# /=.
        case(i < _at - _cur + 3) =>*.
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifF /#.
        rewrite nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (posu16_0s x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_nseq.
        rewrite size_mkseq ifT 1:/# nth_cat size_drop 1:/# size_nseq ifT 1:/#.
        rewrite nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite (u16_word x 0 _ _ pos) ..3:/# !size_cat size_drop 1:/# size_nseq.
        rewrite size_mkseq ifT 1:/# nth_cat size_drop 1:/# size_nseq ifF 1:/#.
        rewrite nth_cat nth_mkseq 1:/# size_mkseq ifT 1:/# !lez_maxr ..3:/# /(\bits8) /=.
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      smt().
qed.

lemma compose4u8_trail0 _buf pos x _cur _at:
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 4 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
  u64bytes (zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos)
            `<<<` 8*x) = bytes_at 8 _cur _at (sub _buf pos 4 ++ [W8.zero]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8*x.
  pose l1:= u64bytes w0.
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 4 ++ [W8.zero]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(4 + x <= i) => i_max.
        rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# drop_cat_le size_mkseq H2 /=.
        rewrite !size_cat !nth_cat size_drop 1:/# size_mkseq size_nseq !lez_maxr ..4:/# /=.
        case(i < _at - _cur + 5) =>*; rewrite ?nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq /sub size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# ifT ifT 1:/# 1:size_cat.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      smt().
qed.


lemma compose6u8_trail0 _buf pos x _cur _at:
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur = x =>
  x < 2 =>
  0 <= x =>
  0 <= pos =>
  pos + 8 < _ASIZE =>
u64bytes
  ((zeroextu64 (get32_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) pos) `<<<` 8*x) `|`
   (zeroextu64 (get16_direct (WA.init8 (ReadWriteArray.A."_.[_]" _buf)) (pos + 4))
    `<<<` 8 * (4 + x))) = bytes_at 8 _cur _at (sub _buf pos 6 ++ [W8.zero]).
proof.
  move => H0 H1 H2 H3 H4 H5 H6 H7.
  pose w0:= zeroextu64 (get32_direct (WA.init8 ("_.[_]" _buf)) pos) `<<<` 8*x.
  pose w1:= zeroextu64 (get16_direct (WA.init8 ("_.[_]" _buf)) (pos + 4)) `<<<` 8*(4+x).
  pose l1:= u64bytes (w0 `|` w1).
  pose l2:= bytes_at 8 _cur _at (sub _buf pos 6 ++ [W8.zero]).
    rewrite (eq_from_nth W8.zero l1 l2).
    + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# size_nseq /#.
    + rewrite size_to_list /l1 => i i_bnd.
      rewrite /l2 /bytes_at nth_take ..2:/# drop_cat_le nth_cat size_nseq lez_maxr 1:/#.
      case(6 + x <= i) => i_max.
        rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# preu16_0s ..3:/# drop_cat_le size_mkseq H2 /=.
        rewrite !size_cat !nth_cat size_drop 1:/# size_mkseq size_nseq !lez_maxr ..4:/# /=.
        case(i < _at - _cur + 7) =>*; rewrite ?nth_nseq /#.
      case(i < x) => i_min.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite posu32_0s ..2:/# posu16_0s ..3:/# ifT ifT 1:/# 1:size_cat 1:size_drop 1:/#.
        rewrite !size_cat size_nseq /sub size_mkseq /#. smt().
        rewrite nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/# nth_nseq /#.
      + move: i_max i_min. rewrite -lezNgt lezNgt /= => i_max i_min.
      case(i < 4 + (_at - _cur)) => u32.
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite u32_word ..2:/# posu16_0s ..3:/# ifT ifT 1:/# 1:size_cat.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# orw0 /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get32_direct /pack4_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      move: u32. rewrite -lezNgt => u16. 
      + rewrite /u64bytes (nth_map witness W8.zero) /iotared 1:size_iota 1:/# /=.
        rewrite preu32_0s ..2:/# u16_word ..3:/# ifT ifT 1:/# 1:size_cat.
        rewrite !size_cat size_drop 1:/# /sub size_mkseq size_nseq /#. smt().
        rewrite !nth_cat size_drop 1:/# size_nseq ifF 1:/# size_mkseq ifT 1:/#.
        rewrite nth_mkseq 1:/# or0w /= !lez_maxr ..3:/# /(\bits8).
        rewrite (W8.ext_eq _ (_buf.[pos + (i - x)])). move => x0 x0_bnd.
          rewrite initE ifT 1:/# /WA.init8 /get16_direct /pack2_t /=.
          rewrite initE ifT 1:nth_iota ..2:/# /= initE ifT 1:nth_iota ..2:/# /=.
          rewrite !nth_iota 1:/# initE ifT /#. smt().
      smt().
qed.

hoare a_ilen_read_upto8_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off + _dlt /\ _off + _dlt + _len <= _ASIZE
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5).
proof.
admit.
(*
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
 wp; ecall (SHLQ_h w aT8); auto => />.
 rewrite !negb_or negb_and -!lezNgt andb_orr. move =>*.
 split; first smt().
  move => ???. rewrite /subread_pre oraE andaE => [#] *.
 do split; 1..2: smt(); 2..5: smt().
   have->: to_uint (W64.of_int (_off + _dlt)) = _off + _dlt. admit.
   have min_pos: 0 <= _off + _dlt. admit.
   have max_pos: _off + _dlt + 8 < _ASIZE. admit.
   apply compose8u8; smt().
 (* 4 <= lEN < 8 *)
if => //.
 case(4 <= aT8).
   rcondf 6. wp; ecall (SHLQ_h w aT8); auto => /#.
   rcondf 6. wp; ecall (SHLQ_h w aT8); auto => /#.
   wp; ecall (SHLQ_h w aT8); auto => />.
   rewrite !negb_or negb_and -!lezNgt andb_orr. move => [#] *.
   split; first smt().
   move=> ???. rewrite /subread_pre oraE andaE => [#] *.
   do split; 1..2: smt(); 2..5: smt().
   + (* Need info regarding _off and _dlt bounds *)
     have->: to_uint (W64.of_int (_off + _dlt)) = _off + _dlt. admit.
     have min_pos: 0 <= _off + _dlt. admit.
     have max_pos: _off + _dlt + 8 < _ASIZE. admit.
     apply compose4u8; smt().
     case(6 <= lEN).
     + rcondt 6. wp; ecall (SHLQ_h w aT8); auto => /#.
       case(2 <= aT8). 
       + rcondf 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
         wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => />.
         rewrite !negb_or negb_and -!lezNgt andb_orr. move => [#] H H1 H2 H3 H4 H5.
         split; first smt(). move => [#] H6 H7.
         split; first smt().
        rewrite ifF 1:/# ifF 1:/# !ifT ..2:/#=> H8 H9 H10. rewrite /subread_pre oraE andaE.
        move => [#] H11 H12 H13 H14 H15 H16 H17.
        do split; 1..2: smt(); 2..5: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small.
            split; 1: by smt(). move=> _. rewrite (ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; 1: by smt(). move=> _. rewrite (ltr_trans _ASIZE); 1:smt(). rewrite aux.
        rewrite -(compose6u8 _ _ (_at - _cur)) /#.
   + rcondt 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
     case(lEN = 7).
     + rcondt 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8).
        auto => />.
        rewrite !negb_or negb_and -!lezNgt. move => [#] H0 H1 H2 H3 H4.
        split; first smt(). move => [#] H6 H7.
        split; first smt().
        rewrite !ifF ..4:/# => H8 H9.
        split; first smt(). move => H10 H11.
        (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        split. move =>  ???. rewrite /subread_pre !andaE oraE. move => [#] *.
        do split; 1..3: smt(); 2..4: smt().
        + rewrite !of_uintK !pmod_small.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            smt().
          rewrite -(compose7u8_trail _ _ (_at - _cur)) /#.
        move =>  ??. rewrite /subread_pre !andaE oraE. move => [#]*.
        do split; 1..6: smt(); 2..4: smt().
        + rewrite !of_uintK !pmod_small.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; 1: by smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            smt().
          rewrite -(compose7u8_trail _ _ (_at - _cur)) /#.
        move =>*.
    + rcondf 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
      case(tRAIL %% 256 <> 0).
      + rcondt 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8).
        auto => />.
        rewrite !negb_or negb_and -!lezNgt andb_orr.
        move => [#] H H1 H2 H3 H4 H5 H6 H7. have->: _len = 6 by smt().
        split; first smt(). move => [#] H8 H9.
        split; first smt().
        rewrite !ifF ..4:/# /subread_spec /subread_pre !andaE oraE => H10 H11.
        split;first smt(). move=> H12 H13 H14 [#] H15 H16 H17 H18 H19 H20 H21.
        do split; 1..3: smt(); 2..4: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small.
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            smt().
          rewrite !addrA /= -(compose6u8_trail _ _ (_at - _cur)) /#.
      + rcondf 12. wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8); auto => /#.
        wp; ecall (SHLQ_h t16 aT8); wp; ecall (SHLQ_h w aT8). auto => />.
        rewrite !negb_or negb_and -!lezNgt andb_orr.
        move => [#] H H1 H2 H3 H4 H5 H6 H7. have->: _len = 6 by smt().
        split; first smt(). move => [#] H8 H9.
        split; first smt().
        rewrite !ifF ..4:/# /subread_spec /subread_pre !andaE oraE.
        move => H10 H11 H12 [#] H13 H14 H15 H16 H17 H18 H19.
        do split; 1..6: smt(); 2..4: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small.
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          rewrite -of_int_mod H7.
          rewrite !addrA /= -(compose6u8_trail0 _ _ (_at - _cur)) /#.
  + rcondf 6. wp; ecall (SHLQ_h w aT8); auto => /#.
    rcondt 6. wp; ecall (SHLQ_h w aT8); auto => /#.
    case(lEN = 5).
    + rcondt 6. wp; ecall (SHLQ_h w aT8); auto => /#.
      wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h w aT8); auto => />.
      rewrite !negb_or negb_and -!lezNgt.
      move => *. split; first smt().
      move => *. split; first smt().
      rewrite !ifF ..2:/# /subread_spec /subread_pre !andaE oraE => *.
      (* Need info regarding _off and _dlt bounds *)
      have aux: _ASIZE < W64.modulus. admit.
      have min_pos: 0 <= _off + _dlt. admit.
      have max_pos: _off + _dlt + 8 < _ASIZE. admit.
      split. move => ??? [#] H10 H11 H12 H13 H14 H15 H16.
      do split; 1..3:smt(); 2..4:smt().
        rewrite !of_uintK !pmod_small.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          smt().
        rewrite -shlw_or trail_simplify ..2:/# addrA -(compose5u8_trail _ _ (_at-_cur)) /#.
      move => ?? [#] H10 H11 H12 H13 H14 H15 H16.
      do split; 1..6:smt(); 2..4:smt().
        rewrite !of_uintK !pmod_small.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          smt().
        rewrite -shlw_or trail_simplify ..2:/# addrA -(compose5u8_trail _ _ (_at-_cur)) /#.
  + rcondf 6. wp; ecall (SHLQ_h w aT8); auto => /#.
    case(tRAIL %% 256 <> 0).
    + rcondt 6. wp; ecall (SHLQ_h w aT8); auto => /#.
      wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h w aT8); auto => />.
      rewrite !negb_or negb_and -!lezNgt andb_orr.
      move => H H0 H1 H2 H3 H4 H5. have->: _len = 4 by smt().
      split; first smt(). move => H6 H7.
      rewrite !ifF ..2:/# /subread_spec /subread_pre !andaE oraE.
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
      split; first smt(). move => ??? [#] *.
      do split; 1..3:smt(); 2..4:smt().
        rewrite of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          smt().
        rewrite -(compose4u8_trail _ _ (_at - _cur)) /#.
   + rcondf 6. wp; ecall (SHLQ_h w aT8); auto => /#.
      wp; ecall (SHLQ_h w aT8); auto => />.
      rewrite !negb_or negb_and -!lezNgt andb_orr.
      move => ?????? H5. have->: _len = 4 by smt().
      split; first smt(). move => *.
      rewrite !ifF ..2:/# /subread_spec /subread_pre !andaE oraE. move => *.
      do split; 1..6:smt(); 2..4:smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        rewrite -of_int_mod H5.
        rewrite -(compose4u8_trail0 _ _ (_at - _cur)) /#.
(* lEN < 4 *)
case(2 <= lEN).
+ rcondt 2. auto => /#.
  case(aT8 < 5).
  + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
    case(lEN = 3).
    + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
      case(tRAIL %% 256 <> 0).
      + rcondt 15. wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite negb_or lezNgt -lezNgt /= => H0 H1 H2.
        split; first by smt(). move => H3 H4.
        rewrite !ifF ..2:/#. split; first by smt().
        rewrite /subread_spec /subread_pre !andaE oraE => *.
        do split; 1..3: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose3u8_trail _ _ (_at - _cur)) /#.
    + rcondf 15. wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite negb_or lezNgt -lezNgt /= => *.
        split; first by smt(). move => *.
        rewrite !ifF ..2:/#. split; first by smt().
        rewrite /subread_spec /subread_pre !andaE oraE => *.
        do split; 1..6: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose3u8_trail _ _ (_at - _cur)) /#.
    + rcondf 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
      case(tRAIL %% 256 <> 0).
      + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite !negb_or lezNgt -lezNgt /= => *.
        split; first by smt(). move => H7 H8.
        rewrite !ifF ..2:/#. split; first by smt().
        rewrite /subread_spec /subread_pre !andaE oraE => *. have->: _len = 2 by smt().
        do split; 1..3: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose2u8_trail _ _ (_at - _cur)) /#.
    + rcondf 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite !negb_or lezNgt -lezNgt /= => ??????H6.
        split; first by smt(). move => *. have->: _len = 2 by smt().
        rewrite !ifF ..2:/# /subread_spec /subread_pre !andaE oraE =>*.
        do split; 1..6: smt(); 2..4: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small. 
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          rewrite -of_int_mod H6.
          rewrite -(compose2u8_trail0 _ _ (_at - _cur)) /#.
  case(aT8 = 5).
  + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
    case(lEN = 3).
    + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
      rcondf 15. wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite negb_or lezNgt -lezNgt /= => *.
        split; first by smt(). move => *.
        rewrite !ifF ..2:/#. split; first by smt().
        rewrite /subread_spec /subread_pre !andaE oraE =>*.
        do split; 1..6: smt(); 2..4: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small. 
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
            split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          smt().
          rewrite !addrA /= -(compose3u8_trail _ _ (_at - _cur)) /#.
    + rcondf 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
      case(tRAIL %% 256 <> 0).
      + rcondt 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t8 aT8); wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite !negb_or lezNgt -lezNgt /= => *.
        split; first by smt(). move => *.
        rewrite !ifF ..2:/#. split; first by smt().
        rewrite /subread_spec /subread_pre !andaE oraE => *. have->: _len = 2 by smt().
        do split; 1..3: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose2u8_trail _ _ (_at - _cur)) /#.
    + rcondf 8. wp; ecall (SHLQ_h t16 aT8); auto => /#.
        wp; ecall (SHLQ_h t16 aT8); auto => />.
        rewrite !negb_or lezNgt -lezNgt /= => ???????H.
        split; first by smt(). move => *. have->: _len = 2 by smt().
        rewrite !ifF ..2:/# /subread_spec /subread_pre !andaE oraE => *.
        do split; 1..6: smt(); 2..4: smt().
        + (* Need info regarding _off and _dlt bounds *)
          have aux: _ASIZE < W64.modulus. admit.
          have min_pos: 0 <= _off + _dlt. admit.
          have max_pos: _off + _dlt + 8 < _ASIZE. admit.
          rewrite !of_uintK !pmod_small. 
           split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
          rewrite -of_int_mod H.
          rewrite -(compose2u8_trail0 _ _ (_at - _cur)) /#.
  + rcondf 8. wp; ecall (SHLQ_h t16 aT8); auto => /#. 
    wp; ecall (SHLQ_h t16 aT8); auto => />.
    rewrite !negb_or !negb_and lezNgt -lezNgt /= => *.
    split; first by smt(). move => H7 H8.
    rewrite !ifT ..2:/# /subread_spec /subread_pre !andaE oraE => *.
    do split; 1..6: smt(); 2..5: smt().
    + (* Need info regarding _off and _dlt bounds *)
      have aux: _ASIZE < W64.modulus. admit.
      have min_pos: 0 <= _off + _dlt. admit.
      have max_pos: _off + _dlt + 8 < _ASIZE. admit.
      rewrite !of_uintK !pmod_small. 
        split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1: smt(). rewrite aux.
        rewrite -(compose2u8 _ _ (_at - _cur)) /#.
(* 0 <= lEN < 2 *)
rcondf 2. auto => /#.
case(aT8 < 7).
+ rcondt 2. auto => /#.
  case(lEN = 1). 
  + rcondt 2. auto => /#.
    case(tRAIL %% 256 <> 0).
    + rcondt 9. wp; ecall (SHLQ_h t8 aT8); auto => /#.
       wp; ecall (SHLQ_h t8 aT8); auto => />.
      rewrite !negb_or lezNgt -lezNgt /= => *.
      split; first by smt(). move => *.
      rewrite /subread_spec /subread_pre !andaE oraE => *.
      do split; 1..3: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose1u8_trail _ _ (_at - _cur)) /#.
    + rcondf 9. wp; ecall (SHLQ_h t8 aT8); auto => /#.
       wp; ecall (SHLQ_h t8 aT8); auto => />.
      rewrite !negb_or lezNgt -lezNgt /= => *.
      split; first by smt(). move => H7 H8.
      rewrite /subread_spec /subread_pre !andaE oraE => *.
      do split; 1..6: smt(); 2..4: smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
        smt().
        rewrite -(compose1u8_trail _ _ (_at - _cur)) /#.
  + rcondf 2. auto => /#.
    case(tRAIL %% 256 <> 0).
    + rcondt 2. auto => /#.
      wp; ecall (SHLQ_h t8 aT8); auto => />.
      rewrite !negb_or lezNgt -lezNgt /= => *.
      split; first by smt(). move => *.
      rewrite /subread_spec /subread_pre !andaE oraE => *.
      do split; 1..5: smt(); 2..5: smt(). have->: _len = 0 by smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !pmod_small 1:/# -compose_trail /#.
    + rcondf 2. auto => /#.
      by auto => /#.
case(aT8 = 7).
  rcondt 2. auto => /#.
  case(lEN = 1). 
  + rcondt 2. auto => /#.
    rcondf 9. wp; ecall (SHLQ_h t8 aT8); auto => /#.
    wp; ecall (SHLQ_h t8 aT8); auto => />.
    rewrite !negb_or lezNgt -lezNgt /= => *.
    split; first by smt(). move => *.
    rewrite /subread_spec /subread_pre !andaE oraE => *.
    do split; 1..6: smt(); 2..4: smt().
    + (* Need info regarding _off and _dlt bounds *)
      have aux: _ASIZE < W64.modulus. admit.
      have min_pos: 0 <= _off + _dlt. admit.
      have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !of_uintK !pmod_small. 
          split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
      smt().
      rewrite -(compose1u8_trail _ _ (_at - _cur)) /#.
  + rcondf 2. auto => /#.
    case(tRAIL %% 256 <> 0).
    + rcondt 2. auto => /#.
      wp; ecall (SHLQ_h t8 aT8); auto => />.
      rewrite !negb_or lezNgt -lezNgt /= => *.
      split; first by smt(). move => *.
      rewrite /subread_spec /subread_pre !andaE oraE => *.
      do split; 1..5: smt(); 2..5: smt(). have->: _len = 0 by smt().
      + (* Need info regarding _off and _dlt bounds *)
        have aux: _ASIZE < W64.modulus. admit.
        have min_pos: 0 <= _off + _dlt. admit.
        have max_pos: _off + _dlt + 8 < _ASIZE. admit.
        rewrite !pmod_small 1:/# -compose_trail /#.
    + rcondf 2. auto => /#.
      by auto => /#.
+ rcondf 2. auto => /#.
  auto => /#.
*)
qed.

phoare a_ilen_read_upto8_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off + _dlt /\ _off + _dlt + _len <= _ASIZE
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto8_at_ll
          (a_ilen_read_upto8_at_h _buf _off _dlt _len _trail _cur _at).
qed.

lemma nseq_ext (x: W8.t) y:
  0 <= y =>
  nseq y x ++ [x] = nseq (y+1) x.
proof. move => H. rewrite -nseq1 (cat_nseq y 1 x) /#. qed.

lemma u8init0:
W8.init (fun (_ : int) => false) = W8.zero.
proof.
  rewrite (W8.ext_eq _ W8.zero). move => x x_bnd.
  by rewrite initE ifT /#.
  smt().
qed.

lemma u64init0:
W64.init (fun (_ : int) => false) = W64.zero.
proof.
  rewrite (W64.ext_eq _ W64.zero). move => x x_bnd.
  by rewrite initE ifT /#.
  smt().
qed.

lemma u128init0:
W128.init (fun (_ : int) => false) = W128.zero.
proof.
  rewrite (W128.ext_eq _ W128.zero). move => x x_bnd.
  by rewrite initE ifT /#.
  smt().
qed.

lemma u128_0s_v0 (_buf: W8.t A.t) _off _dlt _len _trail _cur _at:
   0 <= _cur =>
   0 <= _at =>
   _at < _cur =>
   0 <= _len =>
   _len = 0 /\ _trail = 0 =>
  u128bytes W128.zero = bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => ? ? ? ? H.
  pose l1:= u128bytes W128.zero.
  pose l2:=  bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]). 
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# !size_cat size_drop 1:/# !size_cat !size_mkseq.
    rewrite !size_nseq ifF /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat.
    rewrite !H size_mkseq size_nseq /= ifF 1:/#.  rewrite u8init0 nth_nseq /#.
    smt().
qed.

lemma u128_0s_v1 (_buf: W8.t A.t) _off _dlt _len _trail _cur _at:
   0 <= _cur =>
   0 <= _at =>
   _cur <= _at =>
   0 <= _len =>
   _len = 0 /\ _trail = 0 =>
  u128bytes W128.zero = bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => ???? H.
  pose l1:= u128bytes W128.zero.
  pose l2:=  bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]). 
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# !size_cat size_drop 1:/# !size_cat !size_mkseq.
    rewrite !size_nseq ifT /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat.
    rewrite size_mkseq size_nseq !lez_maxr ..5:/# !H /sub mkseq0 cat0s nseq_ext 1:/#/=.
    case(i < _at + 1 - _cur) =>*.
    + rewrite nth_drop ..2:/# nth_nseq 1:/# u8init0 /#.
    + rewrite nth_nseq 1:/# u8init0 /#.
    smt().
qed.

lemma u128_0s_v2 (_buf: W8.t A.t) _off _dlt _len _trail _cur _at:
   0 <= _cur =>
   0 <= _at =>
   0 <= _len =>
   _cur + 16 <= _at =>
  u128bytes W128.zero = bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => ??? H.
  pose l1:= u128bytes W128.zero.
  pose l2:=  bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]). 
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# !size_cat size_drop 1:/# !size_cat !size_mkseq.
    rewrite !size_nseq ifT /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat.
    rewrite size_mkseq size_nseq !lez_maxr ..5:/# /sub ifT 1:/# drop_cat size_nseq.
    rewrite ifT 1:/# nth_cat size_drop 1:/# size_nseq ifT 1:/# nth_drop ..2:/#.
    rewrite nth_nseq 1:/# u8init0 /#.
    smt().
qed.

lemma full_u128_0s (_buf: W8.t A.t) _off _dlt _len _trail _cur _at:
  0 <= _cur =>
  0 <= _at =>
  0 <= _len =>
  ((_len = 0 /\ _trail = 0 /\ (_at < _cur \/ _cur <= _at)) \/ _cur + 16 <= _at) =>
  u128bytes W128.zero = bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 [[? [? [H | H]]] | H].
    rewrite (u128_0s_v0 _buf _off _dlt _len _trail _cur _at) /#.
    rewrite (u128_0s_v1 _buf _off _dlt _len _trail _cur _at) /#.
    rewrite (u128_0s_v2 _buf _off _dlt _len _trail _cur _at) /#.
qed.

lemma compose16u8 (buf: W8.t A.t) pos at cur len trail:
  16 <= len =>
  0 <= cur =>
  0 <= at =>
  0 <= pos =>
  pos + len <= _ASIZE =>
  cur <= at =>
  u128bytes (get128_direct (WA.init8 ("_.[_]" buf)) pos `<<<` 8 * (at - cur)) =
  bytes_at 16 cur at (sub buf pos len ++ [W8.of_int trail]).
proof.
  move => H0 H1 H2 H3 H4 H5.
  pose l1:= u128bytes (get128_direct (WA.init8 ("_.[_]" buf)) pos `<<<` 8 * (at - cur)).
  pose l2:= bytes_at 16 cur at (sub buf pos len ++ [W8.of_int trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat size_mkseq.
    rewrite !size_nseq ifT /#.
  + rewrite size_to_list. move => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# nth_cat nth_drop ..2:/# size_drop 1:/#.
    rewrite !size_cat size_mkseq size_nseq !lez_maxr ..5:/# ifT 1:/# /=.
    rewrite nth_cat size_nseq lez_maxr 1:/#.
    case(i < at - cur) => cT.
    + rewrite ifT 1:/# nth_nseq 1:/# (W8.ext_eq _ W8.zero). move => x x_bnd.
      + rewrite initE ifT 1:/# /=. have->: 0 <= i * 8 + x < 128 by smt().
        rewrite andaE andTb get_out /#.
      smt().
    + rewrite ifF 1:/# nth_cat size_mkseq ifT 1:/#.
      rewrite (W8.ext_eq _ ((sub buf pos len).[cur + i - at])). move => x x_bnd.
      + rewrite initE ifT 1:/# /=. have->: 0 <= i * 8 + x < 128 by smt().
        rewrite andaE andTb /get128_direct /pack16_t initE ifT 1:/# /=.
        rewrite initiE 1:/# /= initE ifT 1:/# /sub nth_mkseq /#.
      smt().
    smt().
qed.

lemma u128_to_1u64 x:
    u128bytes (VPINSR_2u64 W128.zero x W8.one) =
    u64bytes (W64.zero) ++ (u64bytes x).
proof.
  pose l1:= u128bytes (VPINSR_2u64 W128.zero x W8.one).
  pose l2:= u64bytes W64.zero ++ u64bytes x.
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_cat !size_to_list /#. 
  + rewrite size_to_list => i i_bnd.
    case(i < 8) => i_small.
    + rewrite nth_cat !nth_to_list /VPINSR_2u64 /(\bits8) !size_to_list.
      rewrite to_uint1 pmod_small 1:/# ifT 1:/# u8init0 (W8.ext_eq _ W8.zero).
      + move => x0 x0_bnd. rewrite initE ifT 1:/# /pack2_t /= initE ifT 1:/# /= initE.
        rewrite ifT 1:/# /= ifF 1:/# /(\bits64) u64init0 /#.
        smt().
    + rewrite nth_cat !nth_to_list /VPINSR_2u64 /(\bits8) !size_to_list.
      rewrite to_uint1 pmod_small 1:/# ifF 1:/#.
      rewrite (W8.ext_eq _ (W8.init (fun j => x.[(i - 8) * 8 + j]))).
      +  move => x0 x0_bnd. rewrite initE ifT 1:/# /pack2_t /= initE ifT 1:/# /= initE.
        rewrite ifT 1:/# /= ifT 1:/# /(\bits64) initE ifT /#.
      smt().
    smt().
qed.

lemma u128_to_2u64 x y:
  u128bytes (VPINSR_2u64 (zeroextu128 x) y W8.one) =
  u64bytes x ++ u64bytes y.
proof.
  pose l1:= u128bytes (VPINSR_2u64 (zeroextu128 x) y W8.one).
  pose l2:= u64bytes x ++ u64bytes y.
  rewrite (eq_from_nth W8.zero l1 l2). 
  + rewrite size_cat !size_to_list /#.
  + rewrite size_to_list => i i_bnd.
    rewrite !nth_to_list /(\bits8) (W8.ext_eq _ l2.[i]). move => x0 x0_bnd.
    + rewrite initE ifT 1:/# /VPINSR_2u64 /pack2_t /= initE nth_cat size_to_list.
      case(i < 8) => i_small.
      + have->: 0 <= i * 8 + x0 < 128 by smt().
        rewrite andaE andTb initE ifT 1:/# /= ifF 1:/# /(\bits64) initE ifT 1:/#.
        rewrite /= /zeroextu128 /W128.of_int pmod_small.
        (*****************************************************************************
         * This needs to be fixed:                                                   *
         * 1) smt() can't solve have using W64.to_uint_cmp                           *
         * 2) smt() can't solve ltr_trans/ltr_le_trans despite having b in context   *
         *****************************************************************************)
           have [a b]:0 <= W64.to_uint x < W64.modulus 
             by rewrite W64.to_uint_cmp.
           split. smt(). rewrite (ltr_trans W64.modulus) 1:b /#.
         rewrite get_bits2w 1:/# (int2bs_cat 64) 1:/# pdiv_small.
           have [a b]:0 <= W64.to_uint x < W64.modulus 
            by rewrite W64.to_uint_cmp.
           split. smt(). rewrite (ltr_le_trans W64.modulus) 1:b /#.
         rewrite nth_cat size_int2bs ifT 1:/# /to_uint.
         have{1}->: 64 = size (w2bits x) by rewrite size_w2bits.
         rewrite bs2intK /u64bytes nth_to_list /(\bits8) get_w2bits initE /#.
      + have->: 0 <= i * 8 + x0 < 128 by smt().
        rewrite andaE andTb initE ifT 1:/# /= ifT 1:/# /u64bytes nth_to_list /(\bits8).
        rewrite initE ifT /#.
      smt().
    smt().
qed.


lemma u128_compose8u8_trail (_buf: W8.t A.t) x _off _dlt _len _trail _cur _at:
  0 <= _len =>
  _len < 16 =>
  0 <= _cur =>
  0 <= _at =>
  8 <= _at - _cur =>
  u64bytes x =
    bytes_at 8 8 (_at - _cur) (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]) =>
  u64bytes W64.zero ++ u64bytes x =
  bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5.
  pose l1:= u64bytes W64.zero ++ u64bytes x.
  pose l2:= bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite !size_cat !size_to_list !size_take ..1:/# !size_cat !size_drop ..1:/#.
    rewrite !size_cat !size_mkseq !size_nseq !lez_maxr ..6:/# ifT /#.
  + rewrite size_cat !size_to_list /= => i i_bnd.
    rewrite /l1 H5 /l2.
    rewrite !nth_cat size_to_list !nth_take ..4:/# !nth_cat !size_drop ..2:/# !size_cat.
    rewrite !size_mkseq !size_nseq !lez_maxr..8:/# /=.
    case(i < 8) => i_small.
    + rewrite nth_to_list /(\bits8) u8init0 nth_drop ..2:/# !nth_cat size_mkseq !size_nseq.
      rewrite ifT 1:/# nth_nseq /#.
    + case(i < _at - _cur + _len) => i_mid0.
      + rewrite ifT 1:/# !nth_drop ..4:/# !nth_cat !size_nseq !lez_maxr ..2:/# !size_mkseq.
        case(i < _at - _cur) => i_pre.
        + rewrite !ifT ..3:/# !nth_nseq /#.
        + rewrite ifF 1:/# ifT 1:/# ifT 1:/# ifF 1:/# ifT /#.
      + case(i < _at - _cur + _len + 1) => i_mid1.
        + rewrite ifT 1:/# !nth_drop..4:/# !nth_cat !size_nseq !lez_maxr..2:/# !size_mkseq.
          rewrite ifF 1:/# ifF 1:/# ifT 1:/# ifF 1:/# ifF /#.
    + rewrite !ifF ..2:/# !nth_nseq /#.
    smt().
qed.

lemma u128_compose16u8_trail (_buf: W8.t A.t) x0 x1 y1 y2 y3 y4 _off _dlt _len _trail _cur _at:
  0 <= _len =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur < 8 =>
  y1 =  _dlt + _len - y2 =>
  y2 = max 0 (_len - max 0 (8 - (_at - _cur))) =>
  y4 = max (_at - _cur) (min 8 (_at - _cur + _len + b2i (_trail <> 0))) =>
  (8 <= _len + (_at - _cur) /\ y3 = _trail \/ _len + (_at - _cur) < 8 /\ y3 = 0) =>
  u64bytes x0 =
    bytes_at 8 0 (_at - _cur) (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]) =>
  u64bytes x1 =
    bytes_at 8 8 y4 (sub _buf (_off + y1) y2 ++ [W8.of_int y3]) =>
  u64bytes x0 ++ u64bytes x1 = bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => ?????h0 h1 h2 ? H0 H1.
  pose l1:= u64bytes x0 ++ u64bytes x1.
  pose l2:= bytes_at 16 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_take /l2 /bytes_at 1:/# !size_cat size_drop 1:/# !size_to_list.
    rewrite !size_cat size_mkseq !size_nseq /#.
  + rewrite size_cat !size_to_list /= => i i_bnd.
    rewrite nth_take ..2:/# !nth_cat H0 H1 !size_take 1:/# !nth_drop 1..2:/# !size_cat.
    rewrite !size_drop ..2:/# !size_cat !size_mkseq !size_nseq !lez_maxr ..9:/# /=.
    have->: 8 < _at-_cur+(_len+1)+8 by smt().
    rewrite /=. case(i < 8) => i_small.
    + case(i < _at - _cur) => pre_0s.
      + rewrite nth_take ..2:/# drop0 !nth_cat !size_cat !size_mkseq !size_nseq !ifT..4:/#.
        rewrite !nth_nseq /#.
      + rewrite nth_take ..2:/# drop0 !nth_cat !size_cat !size_mkseq !size_nseq.
        case(i < _at - _cur + _len) => *.
        + rewrite ifT 1:/# ifF 1:/# ifT 1:/# ifT 1:/# ifF 1:/# ifT /#. 
        + case(i < _at - _cur + _len + 1) => *.
          + rewrite ifT 1:/# ifF 1:/# ifF 1:/# ifT 1:/# ifT 1:/# ifF /#.
          + rewrite ifF 1:/# ifF 1:/# !nth_nseq /#.
    + case(i < _at - _cur) => pre_0s.
      + rewrite nth_take ..2:/# !nth_cat nth_drop ..2:/# !size_drop 1:/# !size_mkseq.
        rewrite !size_nseq !ifT..4:/# nth_nseq /#.
      + rewrite nth_take ..2:/# !nth_cat nth_drop ..2:/# !size_drop 1:/# !size_mkseq.
        rewrite !size_cat !size_nseq !size_mkseq !nth_cat !size_mkseq !size_nseq.
        case(i < _at - _cur + _len) => *.
        + rewrite ifT 1:/# ifF 1:/# ifT 1:/# ifT 1:/# ifF 1:/# ifT 1:/# !nth_mkseq /#.
        + case(i < _at - _cur + _len + 1) => *.
          + rewrite ifT 1:/# ifF 1:/# ifF 1:/# ifT 1:/# ifT 1:/# ifF 1:/# ifF 1:/# ifT /#.
          + rewrite h0 h1 h2. case(_trail <> 0) => *.
            + case(8 < _at - _cur + _len + b2i true) => *.
              + rewrite lez_minl 1:/# !ifF ..2:/# !nth_nseq /#.
              + rewrite lez_minr 1:/#. case(0 <= _len + (_at - _cur) - 8) => *.
                + rewrite !ifF ..2:/# !nth_nseq /#.
                + case(i < _at - _cur + _len + 2) =>*.
                  + rewrite ifT 1:/# ifF 1:/# ifF 1:/# ifT 1:/# ifF 1:/# !nth_nseq /#.
                  + rewrite !ifF ..2:/# !nth_nseq /#.
            + rewrite !ifF ..2:/# !nth_nseq /#.
    smt().
qed.

hoare a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off+ _dlt /\ _off + _dlt + _len <= _ASIZE 
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5).
proc.
(* ((aT < cUR \/ cUR + 16 <= aT) \/ lEN = 0 /\ tRAIL = 0) *)
if => //.
+ auto => /> H h1 h2. rewrite /subread_spec /subread_pre !andaE !oraE. 
  move => H0 [#]H1 H2 H3 H4 H5 H6 H7.
  do split; 1..7: smt(); 2..3: smt().
  rewrite (full_u128_0s _buf _off _dlt _len _trail _cur _at) /#.
(* 16 <= lEN *)
sp. wp. if => //.
+ wp; ecall (SHLDQ_h w aT16); auto => />.
  rewrite !negb_or negb_and. move => [#] H0 H1 H2 H3.
  split; first by smt(). move => H5 H6 H7.
  rewrite /subread_pre !andaE oraE. move => [#] H8 H9 H10 H11 H12 H13 H14.
  do split; ..6: smt(); 2..: smt().
  + have aux: _ASIZE < W64.modulus. admit.
    have min_pos: 0 <= _off + _dlt. admit.
    have max_pos: _off + _dlt + 16 < _ASIZE. admit.
    rewrite of_uintK pmod_small.
      split; first smt(). move=> _. rewrite(ltr_trans _ASIZE); 1:smt(). rewrite aux.
    apply compose16u8; smt().
(* lEN < 16 *)
if => //.
+ wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL 8 aT16); auto => />.
  rewrite !negb_or negb_and /subread_spec /subread_pre => [#] H0 H1 H2 H3 H4.
  rewrite !andaE !oraE. move => result H6 H7 [#] H8 H9 H10 H11 H12 H13 H14.
  move: H6. rewrite H10 H11 H12 !andaE !oraE /=.
  have->: 0 <= _at - _cur by smt().
  have->: _at - _cur + _len + b2i (_trail <> 0) <= 200 by smt().
  have->: (8 <= _at - _cur \/ _len = 0 /\ _trail = 0) by smt().
  rewrite implyTb. move =>  [#] h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.
  do split; 1..7:smt(); 2..:smt().
  + rewrite u128_to_1u64.
    rewrite (u128_compose8u8_trail _buf result.`5 _off _dlt _len _trail _cur _at) /#.
+ wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL 8 aT16).
  wp; ecall(a_ilen_read_upto8_at_h buf offset dELTA lEN tRAIL 0 aT16). auto => />.
  rewrite !negb_or negb_and /subread_spec /subread_pre => [#]  H0 H1.
  rewrite -lezNgt -lezNgt => H2 H3 H4.
  rewrite !andaE !oraE. move => result /= H5.
  have aux0: 0 <= _len. by admit.
  have aux1: (0 <= _trail /\ _trail < 256). pose a:= _trail. by admit (*add pre condition*).
  move: (H5 _). by smt().
  move =>*.
  split. smt().
  move =>?? result0 ?*.
  do split; ..2: smt(); 2..: smt().
  rewrite u128_to_2u64 (u128_compose16u8_trail _buf result.`5 result0.`5 result.`1
                         result.`2 result.`3 result.`4 _off _dlt _len _trail _cur _at) /#.
qed.

phoare a_ilen_read_upto16_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto16_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off+ _dlt /\ _off + _dlt + _len <= _ASIZE 
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u128bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto16_at_ll
          (a_ilen_read_upto16_at_h _buf _off _dlt _len _trail _cur _at).
qed.


lemma u256_to_1u128 x:
    u256bytes (VINSERTI128 W256.zero x W8.one) =
    u128bytes (W128.zero) ++ (u128bytes x).
proof.
  pose l1:= u256bytes (VINSERTI128 W256.zero x W8.one).
  pose l2:= u128bytes W128.zero ++ u128bytes x.
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_cat !size_to_list /#. 
  + rewrite size_to_list => i i_bnd.
    case(i < 16) => i_small.
    + rewrite nth_cat !nth_to_list /VINSERTI128 /(\bits8) !size_to_list.
      rewrite to_uint1 pmod_small 1:/# ifT 1:/# u8init0 (W8.ext_eq _ W8.zero).
      + move => x0 x0_bnd. rewrite initE ifT 1:/# /pack2_t /= initE ifT 1:/# /of_list /=.
        rewrite initE ifT 1:/# /= ifT 1:/# /(\bits128) /= u128init0 /#.
        smt().
    + rewrite nth_cat !nth_to_list /VINSERTI128 /(\bits8) !size_to_list.
      rewrite to_uint1 pmod_small 1:/# ifF 1:/#.
      rewrite (W8.ext_eq _ (W8.init (fun j => x.[(i - 16) * 8 + j]))).
      +  move => x0 x0_bnd. rewrite initE ifT 1:/# /pack2_t /= initE ifT 1:/# /= initE.
        rewrite ifT 1:/# /= /of_list initE ifT 1:/# /(\bits64) /= ifF 1:/# ifT /#.
      smt().
    smt().
qed.

lemma u256_to_2u128 x y:
u256bytes (W256.of_int (to_uint x %% W128.modulus + W128.modulus * to_uint y)) =
u128bytes x ++ u128bytes y.
proof.
  have [a b]: 0 <= W128.to_uint x < W128.modulus by rewrite W128.to_uint_cmp.
  have [c d]: 0 <= W128.to_uint y < W128.modulus by rewrite W128.to_uint_cmp.
  rewrite pmod_small. rewrite b /#.
  rewrite /of_int (int2bs_cat 128) 1:/# !pmod_small.
  + split. smt(). move =>*.
    have->: W256.modulus = 2^128 + 2^128 * (2^128-1) by smt().
    rewrite ltr_le_add.
    + rewrite 1:b /#.
    + rewrite ler_pmul2l 1:/# -ltzS d /#.
  rewrite mulrC divzMDr 1:/# pdiv_small 1:b 1:/# addr0 -int2bs_mod dvdz_modzDr 1:/#.
  rewrite pmod_small 1:b 1:/#.
  have->: u256bytes (W256.bits2w (int2bs 128 (to_uint x) ++ int2bs (256-128) (to_uint y)))
        = u128bytes (x) ++ u128bytes (y).
    rewrite (eq_from_nth W8.zero _ (u128bytes x ++ u128bytes y)).
    + rewrite size_cat !size_to_list /#.
    + rewrite size_to_list => i i_bnd.
      rewrite nth_cat size_to_list nth_to_list /(\bits8). case(i < 16) => i_small.
      + rewrite (W8.ext_eq _ (u128bytes x).[i]). move => x0 x0_bnd.
        + rewrite initE ifT 1:/# /= get_bits2w 1:/# nth_cat size_int2bs ifT 1:/#.
          rewrite /to_uint. have->: 128 = size (w2bits x) by rewrite size_w2bits /#.
          rewrite bs2intK get_w2bits nth_to_list /(\bits8) initE ifT /#. smt().
      + rewrite (W8.ext_eq _ (u128bytes y).[i-16]). move => x0 x0_bnd.
        + rewrite initE ifT 1:/# /= get_bits2w 1:/# nth_cat size_int2bs ifF 1:/#.
          rewrite /to_uint. have->: 128 = size (w2bits y) by rewrite size_w2bits /#.
          rewrite bs2intK get_w2bits nth_to_list /(\bits8) initE ifT /#. smt().
     smt().
   smt().
qed.

lemma u256_full_0s (_buf : W8.t A.t) _off _dlt _len _trail _cur _at:
 0 <= _cur =>
 0 <= _at =>
 0 <= _len =>
 _cur + 32 <= _at \/ _len = 0 /\ _trail = 0 =>
 u256bytes W256.zero =
 bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3.
  pose l2:= bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero (u256bytes W256.zero) l2).
  + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat size_mkseq.
    rewrite !size_nseq /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# nth_cat size_drop 1:/# !size_cat.
    rewrite size_mkseq size_nseq u8init0.
    move: H3. move => [H3 | H3].
    + case(i < _len + _at - _cur) => *.
      + rewrite ifT 1:/# nth_drop ..2:/# !nth_cat size_nseq ifT 1:/# nth_nseq /#.
      + rewrite ifF 1:/# nth_nseq /#.
    + rewrite !H3 /=.
      case(i < _at - _cur + 1) => *.
      + rewrite ifT 1:/# nth_drop ..2:/# nth_cat size_nseq.
        case(i<_at-_cur)=>*.
        + rewrite ifT 1:/# nth_nseq /#.
        + rewrite ifF 1:/# nth_cat size_mkseq ifF /#.
      + rewrite ifF 1:/# !nth_nseq /#.
    smt().
qed.

lemma u256compose32u8 (_buf : W8.t A.t) _off _dlt _len _trail _cur _at:
 0 <= _cur =>
 0 <= _at =>
 32 <= _len =>
 0 = _at - _cur =>
 0 <= _off + _dlt =>
 _off + _dlt + _len <= _ASIZE =>
 u256bytes (get256_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)) =
 bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => H0 H1 H2 H3 H4 H5.
  pose l1:= u256bytes (get256_direct (WA.init8 ("_.[_]" _buf)) (_off + _dlt)).
  pose l2:= bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat size_mkseq.
    rewrite !size_nseq /#.
  + rewrite size_to_list => i i_bnd.
    rewrite nth_to_list /(\bits8) nth_take ..2:/# nth_cat nth_drop ..2:/# size_drop 1:/#.
    rewrite !size_cat size_mkseq !size_nseq ifT 1:/# !nth_cat size_nseq.
    rewrite ifF 1:/# size_mkseq ifT 1:/#.
    rewrite (W8.ext_eq _ (sub _buf (_off + _dlt) _len).[_cur + i - max 0 _at]).
    + move => x x_bnd.
      rewrite initE ifT 1:/# /= /get256_direct /pack32_t initE ifT 1:/# /= initE ifT 1:/#.
      rewrite /= initE ifT 1:/# nth_mkseq /#.
      smt().
    smt().
qed.


lemma u256compose16u8 (_buf : W8.t A.t) x _off _dlt _len _trail _cur _at:
 0 <= _cur =>
 0 <= _at =>
 0 <= _len =>
 16 <= _at - _cur =>
 0 <= _off + _dlt =>
 _off + _dlt + _len <= _ASIZE =>
 _cur <= _at \/ _len = 0 /\ _trail = 0 =>
 u128bytes x =
 bytes_at 16 16 (_at - _cur) (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]) =>
u256bytes (VINSERTI128 W256.zero x W8.one) =
bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move =>??????? H0.
  pose l1:= u256bytes (VINSERTI128 W256.zero x W8.one).
  pose l2:= bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero l1 l2).
  + rewrite size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat size_mkseq.
    rewrite !size_nseq /#.
  + rewrite size_to_list => i i_bnd.
    rewrite /l1 u256_to_1u128 nth_cat size_to_list nth_take ..2:/# nth_cat nth_drop ..2:/#.
    rewrite size_drop 1:/# !size_cat size_mkseq !size_nseq.
    case(i < 16) => i_small.
    + rewrite ifT 1:/# nth_to_list /(\bits8) /= u8init0 nth_cat size_nseq.
      case(i < _at - _cur) => *.
      + rewrite ifT 1:/# nth_nseq /#.
        rewrite ifF 1:/# nth_cat size_mkseq /#.
    + case(i < _at - _cur) => *.
      + rewrite ifT 1:/# nth_cat size_nseq ifT 1:/# H0 nth_take ..2:/# nth_cat.
        rewrite size_drop 1:/# !size_cat size_mkseq !size_nseq ifT 1:/# nth_drop ..2:/#.
        rewrite !nth_cat size_nseq ifT 1:/# !nth_nseq /#.
      + case(i < _at - _cur + _len) => *.
        + rewrite H0 nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat size_mkseq.
          rewrite !size_nseq ifT 1:/# ifT 1:/# ifF 1:/# ifT 1:/# nth_drop ..2:/# !nth_cat.
          rewrite size_mkseq size_nseq ifF 1:/# ifT /#.
        + case(i < _at - _cur + _len + 1) => *.
          + rewrite H0 nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat size_mkseq.
            rewrite size_nseq ifT 1:/# ifT 1:/# size_nseq ifF 1:/# ifF 1:/# nth_drop..2:/#.
            rewrite !nth_cat size_nseq ifF 1:/# size_mkseq ifF /#.
          + rewrite H0 nth_take ..2:/# !nth_cat size_drop 1:/# !size_cat size_mkseq.
            rewrite size_nseq !ifF ..2:/# !nth_nseq /#.
        smt().
qed.

lemma u256_compose32u8 (_buf: W8.t A.t) x0 x1 y1 y2 y3 y4 _off _dlt _len _trail _cur _at:
  0 <= _len =>
  0 <= _cur =>
  0 <= _at =>
  _cur <= _at =>
  _at - _cur < 32 =>
  y1 =  _dlt + _len - y2 =>
  y2 = max 0 (_len - max 0 (16 - (_at - _cur))) =>
  y4 = max (_at - _cur) (min 16 (_at - _cur + _len + b2i (_trail <> 0))) =>
  (16 <= _len + (_at - _cur) /\ y3 = _trail \/ _len + (_at - _cur) < 16 /\ y3 = 0) =>
  u128bytes x0 =
    bytes_at 16 0 (_at - _cur) (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]) =>
  u128bytes x1 =
    bytes_at 16 16 y4 (sub _buf (_off + y1) y2 ++ [W8.of_int y3]) =>
  u128bytes x0 ++ u128bytes x1 =
  bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
proof.
  move => ??????y_2 y_4? H0 H1.
  pose l2:= bytes_at 32 _cur _at (sub _buf (_off + _dlt) _len ++ [W8.of_int _trail]).
  rewrite (eq_from_nth W8.zero (u128bytes x0 ++ u128bytes x1) l2).
  + rewrite size_cat !size_to_list size_take 1:/# size_cat size_drop 1:/# !size_cat.
    rewrite size_mkseq !size_nseq /#.
  + rewrite size_cat !size_to_list => i i_bnd.
    case(i < 16) => i_small.
    + rewrite H0 H1 nth_cat size_take 1:/# drop0 !size_cat !size_mkseq !size_nseq.
      + rewrite ifT 1:/# (W8.ext_eq _ l2.[i]). move => _x _X_bnd.
        rewrite !nth_take ..4:/# drop0 !nth_cat !size_cat !size_mkseq !size_nseq.
        rewrite size_drop 1:/# !size_cat !size_mkseq !size_nseq nth_drop ..2:/# !nth_cat.
        case(i < _at - _cur) => *.
        + rewrite size_nseq !ifT ..4:/# !nth_nseq /#.
        + case(i < _at - _cur + _len) => *.
          + rewrite size_mkseq size_nseq ifT 1:/# ifF 1:/# ifT 1:/# ifT 1:/# ifF 1:/#.
            rewrite !ifT /#.
          + case(i < _at - _cur + _len + 1) => *.
            + rewrite size_mkseq size_nseq ifT 1:/# ifF 1:/# ifF 1:/# ifT 1:/# ifT 1:/#.
              rewrite ifF 1:/# ifF 1:/# ifT /#.
            + rewrite !ifF ..2:/# !nth_nseq /#. 
      smt().
    + rewrite nth_cat size_to_list ifF 1:/# H1 !nth_take ..4:/# !nth_cat !size_drop ..2:/#.
      rewrite !size_cat !size_mkseq !size_nseq.
      case(i < _at - _cur) => *.
      + rewrite ifT 1:/# nth_drop ..2:/# !nth_cat !size_mkseq !size_nseq !ifT ..2:/#.
        rewrite nth_drop ..2:/# nth_cat size_nseq ifT 1:/# !nth_nseq /#.
      + case(i < _at - _cur + _len) => *.
        + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq ifF 1:/#.
          rewrite ifT 1:/# ifF 1:/# ifT 1:/# !nth_mkseq /#.
        + case(_trail = 0) =>*.
          + case(_len + _at - _cur < 16) =>*.
            + case(_at - _cur < 16) => *.
              + rewrite !ifF ..2:/# !nth_nseq /#.
              + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                rewrite !ifF /#.
            + case(_at - _cur < 16) => *.
              + case(i < _len + (_at - _cur) + 1) => *.
                + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                  rewrite !ifF /#.
                + rewrite !ifF ..2:/# !nth_nseq /#.
              + case(i < _len + (_at - _cur) + 1) => *.
                + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                  rewrite !ifF /#.
                + rewrite !ifF ..2:/# !nth_nseq /#.
          + case(_len + _at - _cur + 1 < 16) =>*.
            + case(_at - _cur < 16) => *.
              + rewrite !ifF ..2:/# !nth_nseq /#.
              + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                rewrite !ifF /#.
            + case(_at - _cur < 16) => *.
              + case(i < _len + (_at - _cur) + 1) => *.
                + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                  rewrite !ifF /#.
                + case(_len + _at - _cur < 16) => *.
                  + case(i < 17) => *.
                    + rewrite ifT 1:/# ifF 1:/# nth_drop ..2:/# nth_cat size_nseq ifF 1:/#.
                      rewrite nth_cat size_mkseq ifF 1:/# nth_nseq /#.
                    + rewrite !ifF ..2:/# !nth_nseq /#.
                  + rewrite !ifF ..2:/# !nth_nseq /#.
              + case(i < _len + _at - _cur + 1) => *.
                + rewrite !ifT ..2:/# !nth_drop ..4:/# !nth_cat !size_mkseq !size_nseq.
                  rewrite !ifF /#.
                + rewrite !ifF ..2:/# !nth_nseq /#.
          smt().
qed.

hoare a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\
(* added info*)
    0 <= _off+ _dlt /\ _off + _dlt + _len <= _ASIZE /\
    0 <= _len /\ 0 <= _trail /\ _trail < 256 /\ _at - _cur + _len + b2i (_trail <> 0) <= 200
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5).
proof.
proc. if => //. auto => /> H. rewrite /subread_spec /subread_pre !andaE !oraE.
  move => H0 H1 H2 H3 H4 H5 H6 [#]H7 *.
  do split; 1..7: smt(); 2..3: smt().
  rewrite (u256_full_0s _buf _off _dlt _len _trail _cur _at) /#.
(* aT32 = 0 /\ 32 <= lEN *)
sp. wp. if => //. auto => />. rewrite !negb_or -!lezNgt negb_and => H0 H1 H2 H3 H4 H5 H6 *.
  rewrite /subread_spec /subread_pre !andaE !oraE.
  do split; ..7: smt(); 2..: smt().
  rewrite (u256compose32u8 _buf _off _dlt _len _trail _cur _at) /#.
if => //. 
  wp; ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL 16 aT32); auto => />.
  rewrite !negb_or -!lezNgt negb_and => H0 H1 H2 H3.
  rewrite /subread_spec /subread_pre !andaE !oraE.
  move => H4 H5 H6 H7 H8 H9 H10 H11 [#]H12 H13 H14 H15 H16 *. move: H10.
  rewrite  H11 H14 H15 H16 /=.
  have->: 0 <= _at - _cur by smt().
  have->: _at - _cur + _len + b2i (_trail <> 0) <= 200 by smt().
  have->: 16 <= _at - _cur \/ _len = 0 /\ _trail = 0 by smt().
  rewrite implyTb. move => [#]H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 h27 H28.
  do split; ..2: smt(); 2..: smt().
  rewrite (u256compose16u8 _buf H9.`5 _off _dlt _len _trail _cur _at) /#.
wp. ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL 16 aT32).
wp. ecall(a_ilen_read_upto16_at_h buf offset dELTA lEN tRAIL 0 aT32); auto => />.
  rewrite !negb_or -!lezNgt !negb_and /= => H0. rewrite lezNgt /= => H1 H2 H3.
  rewrite /subread_spec /subread_pre !andaE !oraE.
  move => H4 H5 H6 H7 H8 H9. rewrite implyTb =>  H10. rewrite (H10 _). rewrite H2 H3 H4 H5 /#.
  split; first by smt(). move => ?? result.
  rewrite !implyTb. move => [#] H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 [#] h28 H29.
  move => H30 H31 H32 H33 H34*. rewrite !andaE !oraE /=.
  do split; ..7: smt(); 2..: smt().
  have->: 340282366920938463463374607431768211456 = W128.modulus by smt().
  rewrite u256_to_2u128 (u256_compose32u8 _buf H9.`5 result.`5 H9.`1 H9.`2 H9.`3 H9.`4
                                          _off _dlt _len _trail _cur _at) /#.
qed.

HERE!!!
phoare a_ilen_read_upto32_at_ph _buf _off _dlt _len _trail _cur _at:
 [ MM.__a_ilen_read_upto32_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off+ _dlt /\ _off + _dlt + _len <= _ASIZE 
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto32_at_ll
          (a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at).
qed.



hoare a_ilen_write_upto8_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off + _dlt /\ _off + _dlt + _len <= _ASIZE
 ==> subread_spec 8 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5).
proof.



hoare a_ilen_write_upto16_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off + _dlt /\ _off + _dlt + _len <= _ASIZE
 ==> subread_spec 16 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5).
proof.




hoare a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at:
 MM.__a_ilen_read_upto8_at
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at /\ 0 <= _off + _dlt /\ _off + _dlt + _len <= _ASIZE
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u64bytes res.`5).
proof.



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
  rewrite /VPSLL_4u64 /VPBROADCAST_4u64 /= -iotaredE /=; congr; congr=> />.
  (do split);
  (rewrite /W64.(`<<`) trunc_zext_u64_u128; congr;
   [ congr; admit
   | rewrite of_uintK modz_small 1:/# of_uintK modz_small /#]).
  rewrite /W64.(`<<`) trunc_zext_u64_u128; congr; congr; admit.
inline *.
rcondf {1} 9; first by auto.
rcondf {1} 10; first by auto.
admitted.

end ReadWriteArray.
