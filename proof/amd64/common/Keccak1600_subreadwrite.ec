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

op bytes_at size cur at l=
 take size (drop cur (nseq at W8.zero++l)++nseq size W8.zero).


lemma size_bytes_at sz cur at l:
 0 <= sz =>
 size (bytes_at sz cur at l) = sz.
proof.
move=> Hsz; rewrite size_take // size_cat size_nseq ler_maxr //.
smt(size_ge0).
qed.

lemma size_bytes_at' sz cur at l:
 size (bytes_at sz cur at l) = max 0 sz.
proof.
case: (0 <= sz) => ?.
 by rewrite size_bytes_at // ler_maxr.
by rewrite /bytes_at take_le0 /#.
qed.

lemma bytes_at_zeros n cur at:
 0 <= cur =>
 bytes_at n cur at [W8.zero] = u8zeros n.
proof.
move=> *.
apply (eq_from_nth W8.zero).
 by rewrite size_bytes_at' size_nseq /#.
move=> i; rewrite size_bytes_at' // => Hi.
by rewrite nth_take 1..2:/# nth_cat ?size_drop 1:/# nth_drop 1..2:/# nth_cat !nth_u8zeros /#.
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
 = u128bytes (VPINSR_2u64 (zeroextu128 w0) w1 W8.one).
proof.
by rewrite /VPINSR_2u64 to_uint1 /= /u64bytes /u128bytes /= zeroextu128E.
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

(* *)

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
    var t16:W64.t;
    var t8:W64.t;
    if ((((aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
    if ((((aT < cUR) \/ ((cUR + 16) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
    if ((((aT < cUR) \/ ((cUR + 32) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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



lemma sub0 (buf: W8.t A.t) off:
 sub buf off 0 = [].
proof. by rewrite -size_eq0 size_sub /#. qed.



op subread_pre cur at off dlt len tb =
 0 <= cur /\ 0 <= at /\ 0 <= off /\ 0 <= dlt /\ 0 <= len /\ 0 <= tb < 256 /\
 off + dlt + len <= _ASIZE /\
 at + len + b2i (tb<>0) <= 200 /\
 (cur <= at || len=0 /\ tb=0).


lemma nth_bytes_at sz cur at buf off dlt len tb i:
 0 <= sz =>
 subread_pre cur at off dlt len tb =>
 nth W8.zero (bytes_at sz cur at (A.sub buf (off+dlt) len++[W8.of_int tb])) i
 = if 0 <= at-cur <= i < sz
   then nth W8.zero (sub buf (off+dlt) len++[W8.of_int tb]) (cur+i-at)
   else W8.zero.
proof.
move=> /> ??????????[H|H].
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
 auto => |> [[H|H]|H]. 
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
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\ cUR=_cur /\ aT=_at
 ==> subread_spec 32 _buf _off _dlt _len _trail _cur _at res.`1 res.`2 res.`3 res.`4 (u256bytes res.`5)
 ] = 1%r.
proof.
by conseq a_ilen_read_upto32_at_ll
          (a_ilen_read_upto32_at_h _buf _off _dlt _len _trail _cur _at).
qed.



end ReadWriteArray.
