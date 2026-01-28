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




(* TODO: to be moved elsewhere... *)
op addstate_avx2 (st: W256.t Array7.t, l: W8.t list): W256.t Array7.t =
 stavx2_from_st25 (addstate (stavx2_to_st25 st) (bytes2state l)).




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
    t64_1 <- W64.zero;
    r0 <- W256.zero;
    r1 <- W256.zero;
    t64_2 <- W64.zero;
    t64_3 <- W64.zero;
    t64_4 <- W64.zero;
    t64_5 <- W64.zero;
    r2 <- W256.zero;
    r3 <- W256.zero;
    r4 <- W256.zero;
    r5 <- W256.zero;
    r6 <- W256.zero;
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
  proc __addstate_avx2_aux2 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
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
    t64_1 <- W64.zero;
    r0 <- W256.zero;
    r1 <- W256.zero;
    t64_2 <- W64.zero;
    t64_3 <- W64.zero;
    t64_4 <- W64.zero;
    t64_5 <- W64.zero;
    r2 <- W256.zero;
    r3 <- W256.zero;
    r4 <- W256.zero;
    r5 <- W256.zero;
    r6 <- W256.zero;
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
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ RW.MM.__a_ilen_read_upto32_at (buf, 
      offset, dELTA, _LEN, _TRAILB, 8, aT);
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
      } else {
        
      }
      r2 <-
      (W256.of_int
      (((W128.to_uint t128_2) %% (2 ^ 128)) +
      ((2 ^ 128) * (W128.to_uint t128_1))));
    } else {
      
    }
    st.[0] <- (st.[0] `^` r0);
    st.[1] <- (st.[1] `^` r1);
    st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);
    st.[2] <- (st.[2] `^` r2);
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc __addstate_avx2_aux3 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
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
    t64_1 <- W64.zero;
    r0 <- W256.zero;
    r1 <- W256.zero;
    t64_2 <- W64.zero;
    t64_3 <- W64.zero;
    t64_4 <- W64.zero;
    t64_5 <- W64.zero;
    r2 <- W256.zero;
    r3 <- W256.zero;
    r4 <- W256.zero;
    r5 <- W256.zero;
    r6 <- W256.zero;
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
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ RW.MM.__a_ilen_read_upto32_at (buf, 
      offset, dELTA, _LEN, _TRAILB, 8, aT);
    } else {
      
    }
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
      } else {
        
      }
    } else {
      
    }
    st.[0] <- (st.[0] `^` r0);
    st.[1] <- (st.[1] `^` r1);
    st <@ M.__addstate_r3456_avx2 (st, r3, r4, r5, r6);
    t128_1 <- (zeroextu128 t64_2);
    t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
    t128_2 <- (zeroextu128 t64_3);
    t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
    r2 <-
      (W256.of_int
      (((W128.to_uint t128_2) %% (2 ^ 128)) +
      ((2 ^ 128) * (W128.to_uint t128_1))));
    st.[2] <- (st.[2] `^` r2);
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc __addstate_avx2_aux4 (st:W256.t Array7.t, aT:int, buf:W8.t A.t,
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
move: (Hpre) (Hspec Hn Hpre) => {Hspec} /> ???? H1 H2 H3 H4 H5 *.
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
 by rewrite nth_nseq_if nth_wat /#.
have ->: max 0 at = at by smt().
have ->: max 0 cur = cur by smt().
case: (len=0) => C2.
 by rewrite C2 nth_wat 1..2:/# sub0 /#.
by rewrite nth_cat ifF 1:size_sub /#.
qed.



op addst_avx2 (st : W256.t Array7.t) (st25: W64.t Array25.t) =
 stavx2_from_st25 (addstate (stavx2_to_st25 st) st25).

(*
op stavx2_to_bits (stavx2: W256.t Array7.t) =
 flatten (map W256.w2bits (to_list stavx2)).

lemma size_stavx2_to_bits stavx2:
 size (stavx2_to_bits stavx2) = 1792.
admitted.
*)

(*
lemma stavx2_to_bitsE stavx2:
 stavx2_to_bits stavx2 = flatten (map W256.w2bits (to_list stavx2)).
proof.
rewrite /stavx2_to_bits map_mkseq /mkseq -iotaredE /(\o) /= !flatten_cons /= flatten_nil cats0 !catA.
rewrite /state2bits /w64L_to_bits map_mkseq  /mkseq -iotaredE /(\o) /= !flatten_cons /= flatten_nil cats0 !catA.
admitted.
*)

(*
op stavx2_from_bits bs =
 Array7.of_list W256.zero (map W256.bits2w (chunkify 256 bs)).

lemma stavx2_from_bitsK bs:
 size bs = 1792 =>
 stavx2_to_bits (stavx2_from_bits bs) = bs.
proof.
admitted.

lemma stavx2_to_bitsK st:
 stavx2_from_bits (stavx2_to_bits st) = st.
proof.
admitted.




lemma flatten_states_aux llbytes (stavx2: W256.t Array7.t) l:
 size (flatten llbytes) = 200 =>
 l = List.map bytes_to_bits llbytes =>
 flatten (stavx2_to_bits stavx2 :: l)
 = stavx2_to_bits stavx2
   ++ state2bits (bytes2state (flatten llbytes)).
proof.
move=> Hsz El.
rewrite El flatten_cons; congr.
rewrite -state2bytes2bits bytes2stateK //.
by rewrite bytes_to_bits_flatten; congr.
qed.

lemma w256_to_bytes_to_bits w:
 bytes_to_bits (W32u8.to_list w) = w2bits w.
admitted.

lemma flatten_states st w1 w2 w3 w4 w5 w6 w7 w8 w9 w10:
 flatten
  ( stavx2_to_bits st ::
   [ W64.w2bits w1; W256.w2bits w2
   ; W64.w2bits w3; W256.w2bits w4
   ; W64.w2bits w5; W256.w2bits w6
   ; W64.w2bits w7; W256.w2bits w8
   ; W64.w2bits w9; W256.w2bits w10
   ])
 = stavx2_to_bits st
   ++ state2bits
       (bytes2state (flatten [ u64_to_bytes w1; u256_to_bytes w2
                             ; u64_to_bytes w3; u256_to_bytes w4
                             ; u64_to_bytes w5; u256_to_bytes w6
                             ; u64_to_bytes w7; u256_to_bytes w8
                             ; u64_to_bytes w9; u256_to_bytes w10
                             ])).
proof.
pose L:= u64_to_bytes _::_.
rewrite (flatten_states_aux L); last done.
 rewrite /L !flatten_cons flatten_nil cats0 !size_cat.
 by rewrite !W8u8.size_to_list !W32u8.size_to_list.
by rewrite /L /= !w64_to_bytes_to_bits !w256_to_bytes_to_bits.
qed.

(*
stavx2_to_bits stavx2 = state2bits (stavx2_to_st25 stavx2)
*)
(* PARA INVOCAR LEMA
[ u64_to_bytes t64_1; u256_to_bytes r1
; u64_to_bytes t64_2; u256_to_bytes r3
; u64_to_bytes t64_3; u256_to_bytes r4
; u64_to_bytes t64_4; u256_to_bytes r5
; u64_to_bytes t64_5; u256_to_bytes r6
]
*)
*)



(*
clone import PolyArray as Array53 with
        op size = 53.

bind array Array53."_.[_]" Array53."_.[_<-_]" Array53.to_list Array53.of_list Array53.t 53.
realize tolistP by done.
realize get_setP by smt(Array53.get_setE). 
realize eqP by smt(Array53.tP).
realize get_out by smt(Array53.get_out).
realize gt0_size by done.

require import Avx2_extra.

op split_states (inp : W64.t Array53.t ): W256.t Array7.t * W64.t Array25.t =
 ( init_7_256 (fun ii => u256_pack4 inp.[4*ii+0] inp.[4*ii+1] inp.[4*ii+2] inp.[4*ii+3])
 , init_25_64 (fun ii => inp.[28+ii])
 ).

op F4 (inp : W64.t Array53.t ) : W256.t Array7.t =
 let (stavx2, st) = split_states inp in addst_avx2 stavx2 st.
op P4 (inp : W64.t Array53.t ) : bool =
 stavx2INV (split_states inp).`1.
*)
op st_pack (_at _sz:int) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 =
 bytes2state (flatten [ u64_to_bytes w1; u256_to_bytes w2
                      ; u64_to_bytes w3; u256_to_bytes w4
                      ; u64_to_bytes w5; u256_to_bytes w6
                      ; u64_to_bytes w7; u256_to_bytes w8
                      ; u64_to_bytes w9; u256_to_bytes w10
                      ]).

phoare addstate_r3456_avx2_0_ph _st:
 [ M.__addstate_r3456_avx2
 : st=_st /\ r3=W256.zero /\ r3=W256.zero /\ r3=W256.zero /\ r3=W256.zero
 ==> res=_st
 ] = 1%r.
admitted.

equiv addstate_aux_eq:
 MM.__addstate_avx2 ~ MMaux.__addstate_avx2_aux4
 : ={arg} ==> ={res}.
proc; simplify.
swap {2} [16..18] -12.
seq 2 6: (#pre /\ ={dELTA}).
 sp; if => //=.
  admit.
 auto => /> &m _.
 rewrite tP => i Hi; rewrite get_setE //.
 case: (i=0) => //.
 admit (* OK *).
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
 wp; ecall {2} (addstate_r3456_avx2_0_ph st{2}).
 auto => />.
 admit (* OK *).
wp; ecall {2} (addstate_r3456_avx2_0_ph st{2}).
auto => /> &m *.
rewrite tP => i Hi; rewrite get_setE //.
case: (i=2) => //.
admit (* OK *).
qed.


op stt_pack w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 =
 sliceset256_64_25 
  (sliceset256_64_25 
   (sliceset256_64_25 
    (sliceset256_64_25 
     (sliceset256_64_25 (init_25_64 (fun i=>W64.zero)).[0 <- w0] (8*8) w1).[2 <- w2]
     (8*48)
     w3).[4 <- w4]
    (8 * 88)
    w5).[6 <- w6]
   (8*128)
   w7).[8 <- w8]
  (8*168)
  w9.

print addst_avx2. 
op addst (st1 st2: W64.t Array25.t) = init_25_64 (fun i => st1.[i] `^` st2.[i]).
print addst_avx2.
op addst_avx2_ st st25 = stavx2_from_st25 (addst (stavx2_to_st25 st) st25).

hoare addstate_at_avx2_h _st _buf _off _len _tb _at:
 MM.__addstate_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb /\ aT=_at
 /\ 0 <= _at <= _at+_len <= 200 - b2i (_tb<>0) 
 /\ 0<= offset /\ offset + _len <= _ASIZE /\ 0 <= _tb < 256
 /\  stavx2INV _st
 ==> let l = nseq _at W8.zero ++ sub _buf _off _len ++ [W8.of_int _tb]
     in res.`1 = addst_avx2_ _st (bytes2state l)
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _off + _len.
proof.
bypr => &m' |> *.
have ->:
 Pr[MM.__addstate_avx2(st{m'}, aT{m'}, buf{m'}, offset{m'}, _LEN{m'},
                          _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addst_avx2_ st{m'}
        (bytes2state
           (nseq aT{m'} W8.zero ++ sub buf{m'} offset{m'} _LEN{m'} ++
            [W8.of_int _TRAILB{m'}])) /\
      res.`2 = aT{m'} + _LEN{m'} + b2i (_TRAILB{m'} <> 0) /\
      res.`3 = offset{m'} + _LEN{m'})]
 = Pr[MMaux.__addstate_avx2_aux4(st{m'}, aT{m'}, buf{m'}, offset{m'}, _LEN{m'},
                              _TRAILB{m'}) @ &m' :
   ! (res.`1 =
      addst_avx2_ st{m'}
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
pose _astate := (bytes2state (nseq _at W8.zero ++ sub _buf _off _len ++ [W8.of_int _tb])).
seq 15: ( st=_st /\ _astate = stt_pack t64_1 r1 t64_2 r3 t64_3 r4 t64_4 r5 t64_5 r6 /\ aT = _at + _len + b2i (_tb <> 0) /\ offset = _off + _len /\ stavx2INV _st).
 seq 3: ( #[1:3,8:]pre
        /\ subread_pre 0 _at _len _tb
        /\ subread_spec 8 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT (u64_to_bytes t64_1)).
  case: (aT < 8).
   rcondt 3; first by auto.
   admit.
  rcondf 3; first by auto.
  auto => |>.
  admit.
 seq 2: ( #[/:-2]pre
        /\ subread_spec 40 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT (u64_to_bytes t64_1++u256_to_bytes r1)).
  case: (aT < 40 /\ (0 < _LEN \/ _TRAILB <> 0)).
   rcondt 2; first by auto.
   admit.
  rcondf 2; first by auto.
  auto => |> &m.
  admit.
 case: (0 < _LEN \/ _TRAILB <> 0).
  rcondt 9; first by auto.
  swap [2..8] 1.
  seq 2: ( #[/:-3]pre
         /\ subread_spec 48 _buf _off 0 _len _tb 0 _at dELTA _LEN _TRAILB aT
             (u64_to_bytes t64_1++u256_to_bytes r1++u64_to_bytes t64_2)).
   admit.
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
   have {H2d H6} H6:= (subread_spec_cat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2d H6) => //.
   have H:= subread_finish 200 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H6 => //. 
   admit.
  auto => |> &m ????????.
  admit (* st_pack... *).
 rcondf 9; first by auto.
 auto => |> &m ????????.
 admit (* st_pack... *).
(* handling the permutation part with 'circuit' *)
conseq (: st = _st /\ _astate = stt_pack t64_1 r1 t64_2 r3 t64_3 r4 t64_4 r5 t64_5 r6 /\ stavx2INV _st ==> st = addst_avx2_ _st _astate) => //=.
inline *. 
move: _astate _st => _astate _st; clear. 
admit (* ??? anomaly: File "src/ecCircuits.ml", line 817, characters 2-8: Assertion failed
circuit.
*).
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
