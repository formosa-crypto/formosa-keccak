(******************************************************************************
   avx2/Keccak1600_fixedsizes.ec:

   Correctness proof for the Keccak (fixed-sized) memory and array 
  absorb/squeeze AVX2 implementation

******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200.
from JazzEC require import Array7 Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.


require import Keccak1600_avx2 Keccakf1600_avx2.
require import Keccak1600_subreadwrite.

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

require BitEncoding.
import BitEncoding.BitChunking.

(*
op pabsorb_spec_avx2 (r8 : int) (l : W8.t list) (st : W256.t Array7.t) : bool =
  0 < r8 <= 200 /\
  st = stavx2_from_st25 
        (addstate
          (stateabsorb_iblocks (chunk r8 l) st0)
          (bytes2state (chunkremains r8 l))).
*)

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
      if (((aT = 0) /\ (8 <= _LEN))) {
        r0 <-
        (VPBROADCAST_4u64
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
        dELTA <- (dELTA + 8);
        _LEN <- (_LEN - 8);
        aT <- 8;
      } else {
        (dELTA, _LEN, _TRAILB, aT, t64_1) <@ RW.MM.__a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
        t128_0 <- (zeroextu128 t64_1);
        r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
      }
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
      r2 <-
      (W256.of_int
      (((W128.to_uint t128_2) %% (2 ^ 128)) +
      ((2 ^ 128) * (W128.to_uint t128_1))));
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


lemma addstate_avx2_ll: islossless MM.__addstate_avx2
 by islossless.

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
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ to_list _buf) res.`1
     else pabsorb_spec_avx2 _r8 (_l ++ to_list _buf) res.`1
          /\ res.`2 = (size _l + _ASIZE) %% _r8.
proof.
proc => /=.
admitted.

phoare absorb_avx2_ph _l _buf _tb _r8:
 [ MM.__absorb_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l st
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
