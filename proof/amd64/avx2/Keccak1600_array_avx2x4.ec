(******************************************************************************
   Keccak1600_array_avx2x4.ec:

   Correctness proof for the Keccak (fixed-sized) array based
  absorb/squeeze 4-way AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv StdOrder Ring.

import IntID IntOrder.

from Jasmin require import JModel.
from Jasmin require import JArray.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600 FIPS202_SHA3 FIPS202_SHA3_Spec.
from CryptoSpecs require export Keccak1600_Spec Keccakf1600_Spec.

from JazzEC require Jazz_avx2.

from JazzEC require import WArray800.
from JazzEC require import Array25 WArray200.

require export Keccakf1600_avx2x4 Keccak1600_avx2x4.

abstract theory KeccakArrayAvx2x4.

op aSIZE: int.
axiom aSIZE_ge0: 0 <= aSIZE.
axiom aSIZE_u64: aSIZE < W64.modulus.

module type MParam = {
  proc keccakf1600_avx2x4 (st:W256.t Array25.t) : W256.t Array25.t
  proc state_init_avx2x4 (st: W256.t Array25.t) : W256.t Array25.t
  proc addratebit_avx2x4 (st:W256.t Array25.t, rATE8:int) : W256.t Array25.t
  proc _4u64x4_u256x4(y0 y1 y2 y3 : W256.t) :
    W256.t * W256.t * W256.t * W256.t
}.

clone import PolyArray as A
 with op size <- aSIZE
      proof ge0_size by exact aSIZE_ge0.

clone import WArray as WA
 with op size <- aSIZE.


module M(P: MParam) = {
  proc __aread_subu64 (buf:W8.t A.t, offset:W64.t, dELTA:int, lEN:int,
                       tRAIL:int) : int * int * int * W64.t = {
    var w:W64.t;
    var iLEN:int;
    var t16:W64.t;
    var t8:W64.t;
    iLEN <- lEN;
    if ((lEN <= 0)) {
      w <- (W64.of_int (tRAIL %% 256));
      tRAIL <- 0;
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64
          (get16_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          t16 <- (W64.of_int 0);
        }
        if (((1 <= lEN) \/ ((tRAIL %% 256) <> 0))) {
          if ((1 <= lEN)) {
            t8 <-
            (zeroextu64
            (get8_direct (WA.init8 (fun i => buf.[i]))
            (W64.to_uint (offset + (W64.of_int dELTA)))));
            if (((tRAIL %% 256) <> 0)) {
              t8 <- (t8 `|` (W64.of_int (256 * (tRAIL %% 256))));
            } else {
              
            }
            dELTA <- (dELTA + 1);
            lEN <- (lEN - 1);
          } else {
            t8 <- (W64.of_int (tRAIL %% 256));
          }
          tRAIL <- 0;
          t8 <- (t8 `<<` (W8.of_int (8 * (2 * ((iLEN %/ 2) %% 2)))));
          t16 <- (t16 `|` t8);
        } else {
          
        }
        t16 <- (t16 `<<` (W8.of_int (8 * (4 * ((iLEN %/ 4) %% 2)))));
        w <- (w `|` t16);
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __aread_bcast_4subu64 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                              lEN:int, tRAIL:int) : int * int * int * W256.t = {
    var w:W256.t;
    var t64:W64.t;
    var t128:W128.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w <-
        (VPBROADCAST_4u64
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA)))));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        (dELTA, lEN, tRAIL, t64) <@ __aread_subu64 (buf, offset, dELTA, 
        lEN, tRAIL);
        t128 <- (zeroextu128 t64);
        w <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __aread_subu128 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                        lEN:int, tRAIL:int) : int * int * int * W128.t = {
    var w:W128.t;
    var t64:W64.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          w <-
          (VMOV_64
          (get64_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          (dELTA, lEN, tRAIL, t64) <@ __aread_subu64 (buf, offset, dELTA,
          lEN, tRAIL);
          w <- (VPINSR_2u64 w t64 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, t64) <@ __aread_subu64 (buf, offset, dELTA,
          lEN, tRAIL);
          w <- (zeroextu128 t64);
        }
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __aread_subu256 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                        lEN:int, tRAIL:int) : int * int * int * W256.t = {
    var w:W256.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((32 <= lEN)) {
        w <-
        (get256_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          t128_0 <-
          (get128_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          (dELTA, lEN, tRAIL, t128_1) <@ __aread_subu128 (buf, offset, 
          dELTA, lEN, tRAIL);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        } else {
          t128_1 <- (set0_128);
          (dELTA, lEN, tRAIL, t128_0) <@ __aread_subu128 (buf, offset, 
          dELTA, lEN, tRAIL);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        }
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __awrite_subu64 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                        lEN:int, w:W64.t) : W8.t A.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set32_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu32 w))));
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
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu16 w))));
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
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __awrite_subu128 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                         lEN:int, w:W128.t) : W8.t A.t * int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set128_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set64_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))
          (MOVV_64 (truncateu64 w)))));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (truncateu64 w);
        (buf, dELTA, lEN) <@ __awrite_subu64 (buf, offset, dELTA, lEN, t64);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __awrite_subu256 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                         lEN:int, w:W256.t) : W8.t A.t * int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set256_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set128_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) t128)));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, dELTA, lEN) <@ __awrite_subu128 (buf, offset, dELTA, lEN,
        t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __addstate_bcast_array_avx2x4 (st:W256.t Array25.t, aT:int,
                                      buf:W8.t A.t, offset:W64.t,
                                      lEN:int, tRAILB:int) : W256.t Array25.t *
                                                             int * W64.t = {
    var aLL:int;
    var lO:int;
    var at:W64.t;
    var dELTA:int;
    var t256:W256.t;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    at <- (W64.of_int (32 * (aT %/ 8)));
    dELTA <- 0;
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        (dELTA,  _2, tRAILB, t256) <@ __aread_bcast_4subu64 (buf, offset,
        dELTA, lEN, tRAILB);
        t256 <- (VPSLL_4u64 t256 (W128.of_int (8 * lO)));
        t256 <-
        (t256 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i])) (W64.to_uint at)
        ));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint at) t256)));
        lO <- 0;
        aT <- 0;
        lEN <- 0;
      } else {
        if ((8 <= lEN)) {
          t256 <-
          (VPBROADCAST_4u64
          (get64_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + (8 - lO));
        } else {
          (dELTA,  _0,  _1, t256) <@ __aread_bcast_4subu64 (buf, offset,
          dELTA, (8 - lO), 0);
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t256 <- (VPSLL_4u64 t256 (W128.of_int (8 * lO)));
        t256 <-
        (t256 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i])) (W64.to_uint at)
        ));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint at) t256)));
        at <- (at + (W64.of_int 32));
      }
    } else {
      
    }
    offset <- (offset + (W64.of_int dELTA));
    dELTA <- 0;
    if ((8 <= lEN)) {
      while ((at \ult (W64.of_int ((32 * (aT %/ 8)) + (32 * (lEN %/ 8)))))) {
        t256 <-
        (VPBROADCAST_4u64
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint offset)));
        offset <- (offset + (W64.of_int 8));
        t256 <-
        (t256 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i])) (W64.to_uint at)
        ));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint at) t256)));
        at <- (at + (W64.of_int 32));
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
      } else {
        
      }
      (dELTA,  _3, tRAILB, t256) <@ __aread_bcast_4subu64 (buf, offset,
      dELTA, lO, tRAILB);
      offset <- (offset + (W64.of_int dELTA));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) (W64.to_uint at)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint at) t256)));
    } else {
      
    }
    return (st, aLL, offset);
  }
  proc __absorb_bcast_array_avx2x4 (st:W256.t Array25.t, aT:int,
                                    buf:W8.t A.t, offset:W64.t,
                                    lEN:int, rATE8:int, tRAILB:int) : 
  W256.t Array25.t * int * W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    var  _0:int;
    var  _1:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (st, aT, offset) <@ __addstate_bcast_array_avx2x4 (st, aT, buf, 
      offset, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_avx2x4 (st, rATE8);
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        (st,  _0, offset) <@ __addstate_bcast_array_avx2x4 (st, aT, buf,
        offset, (rATE8 - aT), 0);
        lEN <- (lEN - (rATE8 - aT));
        st <@ P.keccakf1600_avx2x4 (st);
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st,  _1, offset) <@ __addstate_bcast_array_avx2x4 (st, 0, buf,
        offset, rATE8, 0);
        st <@ P.keccakf1600_avx2x4 (st);
        i <- (i + (W64.of_int 1));
      }
      lEN <- (aLL %% rATE8);
      (st, aT, offset) <@ __addstate_bcast_array_avx2x4 (st, 0, buf, 
      offset, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_avx2x4 (st, rATE8);
      } else {
        
      }
    }
    return (st, aT, offset);
  }
  proc __addstate_array_avx2x4 (st:W256.t Array25.t, aT:int,
                                buf0:W8.t A.t, buf1:W8.t A.t,
                                buf2:W8.t A.t, buf3:W8.t A.t,
                                offset:W64.t, lEN:int, tRAILB:int) : 
  W256.t Array25.t * int * W64.t = {
    var aLL:int;
    var lO:int;
    var at:W64.t;
    var dELTA:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
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
    var  _24:int;
    var  _25:int;
    var  _26:int;
    var  _27:int;
    var  _28:int;
    var  _29:int;
    var  _30:int;
    var  _31:int;
    var  _32:int;
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    at <- (W64.of_int (4 * (aT %/ 8)));
    dELTA <- 0;
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        ( _11,  _12,  _13, t0) <@ __aread_subu64 (buf0, offset, dELTA, 
        lEN, tRAILB);
        ( _14,  _15,  _16, t1) <@ __aread_subu64 (buf1, offset, dELTA, 
        lEN, tRAILB);
        ( _17,  _18,  _19, t2) <@ __aread_subu64 (buf2, offset, dELTA, 
        lEN, tRAILB);
        (dELTA,  _20,  _21, t3) <@ __aread_subu64 (buf3, offset, dELTA, 
        lEN, tRAILB);
        t0 <- (t0 `<<` (W8.of_int (8 * lO)));
        t0 <-
        (t0 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0))) t0)));
        t1 <- (t1 `<<` (W8.of_int (8 * lO)));
        t1 <-
        (t1 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1))) t1)));
        t2 <- (t2 `<<` (W8.of_int (8 * lO)));
        t2 <-
        (t2 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2))) t2)));
        t3 <- (t3 `<<` (W8.of_int (8 * lO)));
        t3 <-
        (t3 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3))) t3)));
        lO <- 0;
        aT <- 0;
        lEN <- 0;
        tRAILB <- 0;
      } else {
        if ((8 <= lEN)) {
          t0 <-
          (get64_direct (WA.init8 (fun i => buf0.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          t1 <-
          (get64_direct (WA.init8 (fun i => buf1.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          t2 <-
          (get64_direct (WA.init8 (fun i => buf2.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          t3 <-
          (get64_direct (WA.init8 (fun i => buf3.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          offset <- (offset + (W64.of_int (8 - lO)));
        } else {
          ( _0,  _1,  _2, t0) <@ __aread_subu64 (buf0, offset, dELTA,
          (8 - lO), tRAILB);
          ( _3,  _4,  _5, t1) <@ __aread_subu64 (buf1, offset, dELTA,
          (8 - lO), tRAILB);
          ( _6,  _7,  _8, t2) <@ __aread_subu64 (buf2, offset, dELTA,
          (8 - lO), tRAILB);
          (dELTA,  _9,  _10, t3) <@ __aread_subu64 (buf3, offset, dELTA,
          (8 - lO), tRAILB);
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t0 <- (t0 `<<` (W8.of_int (8 * lO)));
        t0 <-
        (t0 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0))) t0)));
        t1 <- (t1 `<<` (W8.of_int (8 * lO)));
        t1 <-
        (t1 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1))) t1)));
        t2 <- (t2 `<<` (W8.of_int (8 * lO)));
        t2 <-
        (t2 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2))) t2)));
        t3 <- (t3 `<<` (W8.of_int (8 * lO)));
        t3 <-
        (t3 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3))) t3)));
        at <- (at + (W64.of_int 4));
      }
    } else {
      
    }
    offset <- (offset + (W64.of_int dELTA));
    dELTA <- 0;
    if ((8 <= lEN)) {
      while ((at \ult (W64.of_int ((4 * (aT %/ 8)) + (16 * (lEN %/ 32)))))) {
        t256_0 <-
        (get256_direct (WA.init8 (fun i => buf0.[i]))
        (W64.to_uint offset));
        t256_1 <-
        (get256_direct (WA.init8 (fun i => buf1.[i]))
        (W64.to_uint offset));
        t256_2 <-
        (get256_direct (WA.init8 (fun i => buf2.[i]))
        (W64.to_uint offset));
        t256_3 <-
        (get256_direct (WA.init8 (fun i => buf3.[i]))
        (W64.to_uint offset));
        offset <- (offset + (W64.of_int 32));
        (t256_0, t256_1, t256_2, t256_3) <@ P._4u64x4_u256x4 (t256_0, 
        t256_1, t256_2, t256_3);
        t256_0 <-
        (t256_0 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint ((W64.of_int 8) * at))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint ((W64.of_int 8) * at)) t256_0)));
        t256_1 <-
        (t256_1 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 32)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 32))) t256_1)));
        t256_2 <-
        (t256_2 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 64)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 64))) t256_2)));
        t256_3 <-
        (t256_3 `^`
        (get256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 96)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (((W64.of_int 8) * at) + (W64.of_int 96))) t256_3)));
        at <- (at + (W64.of_int 16));
      }
      while ((at \ult (W64.of_int ((4 * (aT %/ 8)) + (4 * (lEN %/ 8)))))) {
        t0 <-
        (get64_direct (WA.init8 (fun i => buf0.[i]))
        (W64.to_uint offset));
        t0 <-
        (t0 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 0))) t0)));
        t1 <-
        (get64_direct (WA.init8 (fun i => buf1.[i]))
        (W64.to_uint offset));
        t1 <-
        (t1 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 1))) t1)));
        t2 <-
        (get64_direct (WA.init8 (fun i => buf2.[i]))
        (W64.to_uint offset));
        t2 <-
        (t2 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 2))) t2)));
        t3 <-
        (get64_direct (WA.init8 (fun i => buf3.[i]))
        (W64.to_uint offset));
        offset <- (offset + (W64.of_int 8));
        t3 <-
        (t3 `^`
        (get64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3)))));
        st <-
        (Array25.init
        (WArray800.get256
        (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
        (W64.to_uint (at + (W64.of_int 3))) t3)));
        at <- (at + (W64.of_int 4));
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      ( _22,  _23,  _24, t0) <@ __aread_subu64 (buf0, offset, dELTA, 
      lO, tRAILB);
      ( _25,  _26,  _27, t1) <@ __aread_subu64 (buf1, offset, dELTA, 
      lO, tRAILB);
      ( _28,  _29,  _30, t2) <@ __aread_subu64 (buf2, offset, dELTA, 
      lO, tRAILB);
      (dELTA,  _31,  _32, t3) <@ __aread_subu64 (buf3, offset, dELTA, 
      lO, tRAILB);
      offset <- (offset + (W64.of_int dELTA));
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
        tRAILB <- 0;
      } else {
        
      }
      t0 <-
      (t0 `^`
      (get64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 0)))));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 0))) t0)));
      t1 <-
      (t1 `^`
      (get64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 1)))));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 1))) t1)));
      t2 <-
      (t2 `^`
      (get64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 2)))));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 2))) t2)));
      t3 <-
      (t3 `^`
      (get64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 3)))));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      (W64.to_uint (at + (W64.of_int 3))) t3)));
    } else {
      
    }
    return (st, aLL, offset);
  }
  proc __absorb_array_avx2x4 (st:W256.t Array25.t, aT:int,
                              buf0:W8.t A.t, buf1:W8.t A.t,
                              buf2:W8.t A.t, buf3:W8.t A.t,
                              offset:W64.t, lEN:int, rATE8:int, tRAILB:int) : 
  W256.t Array25.t * int * W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    var  _0:int;
    var  _1:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (st, aT, offset) <@ __addstate_array_avx2x4 (st, aT, buf0, buf1, 
      buf2, buf3, offset, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_avx2x4 (st, rATE8);
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        (st,  _0, offset) <@ __addstate_array_avx2x4 (st, aT, buf0, buf1,
        buf2, buf3, offset, (rATE8 - aT), 0);
        lEN <- (lEN - (rATE8 - aT));
        st <@ P.keccakf1600_avx2x4 (st);
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st,  _1, offset) <@ __addstate_array_avx2x4 (st, 0, buf0, buf1,
        buf2, buf3, offset, rATE8, 0);
        st <@ P.keccakf1600_avx2x4 (st);
        i <- (i + (W64.of_int 1));
      }
      lEN <- (aLL %% rATE8);
      (st, aT, offset) <@ __addstate_array_avx2x4 (st, 0, buf0, buf1, 
      buf2, buf3, offset, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_avx2x4 (st, rATE8);
      } else {
        
      }
    }
    return (st, aT, offset);
  }
  proc __dumpstate_array_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                                 buf2:W8.t A.t, buf3:W8.t A.t,
                                 offset:W64.t, lEN:int, st:W256.t Array25.t) : 
  W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t *
  W64.t = {
    var i:W64.t;
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    var  _6:int;
    var  _7:int;
    i <- (W64.of_int 0);
    while ((i \slt (W64.of_int (32 * (lEN %/ 32))))) {
      x0 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (0 * 32)))));
      x1 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (1 * 32)))));
      x2 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (2 * 32)))));
      x3 <-
      (get256_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (3 * 32)))));
      i <- (i + (W64.of_int 32));
      (x0, x1, x2, x3) <@ P._4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      (W64.to_uint offset) x0)));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      (W64.to_uint offset) x1)));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      (W64.to_uint offset) x2)));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      (W64.to_uint offset) x3)));
      offset <- (offset + (W64.of_int 32));
    }
    while ((i \slt (W64.of_int (8 * (lEN %/ 8))))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (0 * 8)))));
      buf0 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf0.[i_0]))
      (W64.to_uint offset) t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (1 * 8)))));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf1.[i_0]))
      (W64.to_uint offset) t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (2 * 8)))));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf2.[i_0]))
      (W64.to_uint offset) t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (3 * 8)))));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf3.[i_0]))
      (W64.to_uint offset) t3)));
      i <- (i + (W64.of_int 8));
      offset <- (offset + (W64.of_int 8));
    }
    if ((0 < (lEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (0 * 8)))));
      (buf0,  _0,  _1) <@ __awrite_subu64 (buf0, offset, 0, (lEN %% 8), t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (1 * 8)))));
      (buf1,  _2,  _3) <@ __awrite_subu64 (buf1, offset, 0, (lEN %% 8), t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (2 * 8)))));
      (buf2,  _4,  _5) <@ __awrite_subu64 (buf2, offset, 0, (lEN %% 8), t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      (W64.to_uint (((W64.of_int 4) * i) + (W64.of_int (3 * 8)))));
      (buf3,  _6,  _7) <@ __awrite_subu64 (buf3, offset, 0, (lEN %% 8), t3);
      offset <- (offset + (W64.of_int (lEN %% 8)));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc __squeeze_array_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                               buf2:W8.t A.t, buf3:W8.t A.t,
                               offset:W64.t, lEN:int, st:W256.t Array25.t,
                               rATE8:int) : W8.t A.t *
                                            W8.t A.t *
                                            W8.t A.t *
                                            W8.t A.t * W64.t *
                                            W256.t Array25.t = {
    var iTERS:int;
    var lO:int;
    var i:W64.t;
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- (W64.of_int 0);
        while ((i \ult (W64.of_int iTERS))) {
          st <@ P.keccakf1600_avx2x4 (st);
          (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_array_avx2x4 (
          buf0, buf1, buf2, buf3, offset, rATE8, st);
          i <- (i + (W64.of_int 1));
        }
      } else {
        
      }
      if ((0 < lO)) {
        st <@ P.keccakf1600_avx2x4 (st);
        (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_array_avx2x4 (
        buf0, buf1, buf2, buf3, offset, lO, st);
      } else {
        
      }
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset, st);
  }
}.


(*
   PARAMETER MODULE
*)
module P: MParam = {
  proc keccakf1600_avx2x4 = Jazz_avx2.M._keccakf1600_avx2x4
  proc state_init_avx2x4 = Jazz_avx2.M.__state_init_avx2x4
  proc addratebit_avx2x4 = Jazz_avx2.M.__addratebit_avx2x4
  proc _4u64x4_u256x4 = Jazz_avx2.M.__4u64x4_u256x4
}.


lemma  aread_subu64_ll: islossless M(P).__aread_subu64
 by islossless.

hoare aread_subu64_h _buf _off _dlt _len _trail:
 M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail]).
admitted.

phoare aread_subu64_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu64_ll (aread_subu64_h _buf _off _dlt _len _trail).
qed.

lemma  aread_subu128_ll: islossless M(P).__aread_subu128
 by islossless.

hoare aread_subu128_h _buf _off _dlt _len _trail:
 M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail]).
admitted.

phoare aread_subu128_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu128_ll (aread_subu128_h _buf _off _dlt _len _trail).
qed.

lemma  aread_subu256_ll: islossless M(P).__aread_subu256
 by islossless.

hoare aread_subu256_h _buf _off _dlt _len _trail:
 M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail]).
admitted.

phoare aread_subu256_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu256_ll (aread_subu256_h _buf _off _dlt _len _trail).
qed.


lemma awrite_subu64_ll: islossless M(P).__awrite_subu64
 by islossless.

hoare awrite_subu64_h _buf _off _dlt _len _w:
 M(P).__awrite_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W8u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8.
proof.
admitted.

phoare awrite_subu64_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W8u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8
 ] = 1%r.
proof.
by conseq awrite_subu64_ll (awrite_subu64_h _buf _off _dlt _len _w).
qed.

lemma awrite_subu128_ll: islossless M(P).__awrite_subu128
 by islossless.

hoare awrite_subu128_h _buf _off _dlt _len _w:
 M(P).__awrite_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W16u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16.
proof.
admitted.

phoare awrite_subu128_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W16u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16
 ] = 1%r.
proof.
by conseq awrite_subu128_ll (awrite_subu128_h _buf _off _dlt _len _w).
qed.

lemma awrite_subu256_ll: islossless M(P).__awrite_subu256
 by islossless.

hoare awrite_subu256_h _buf _off _dlt _len _w:
 M(P).__awrite_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W32u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 32) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 32
  /\ res.`3 = _len - min (max 0 _len) 32.
proof.
admitted.

phoare awrite_subu256_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W32u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 32) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 32
  /\ res.`3 = _len - min (max 0 _len) 32
 ] = 1%r.
proof.
by conseq awrite_subu256_ll (awrite_subu256_h _buf _off _dlt _len _w).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_array_avx2x4_ll: islossless M(P).__addstate_array_avx2x4.
admitted.

lemma addstate_bcast_array_avx2x4_ll: islossless M(P).__addstate_bcast_array_avx2x4.
admitted.

phoare absorb_array_avx2x4_ll:
 [ M(P).__absorb_array_avx2x4
 : 0 < rATE8 <= 200 /\ 0 <= lEN /\ to_uint offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
proc.
have L: forall x, x <= aSIZE => x < W64.modulus.
 by move=> *; apply (ler_lt_trans aSIZE) => //; exact aSIZE_u64.
admitted.

hoare absorb_array_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _off _len _r8 _tb:
 M(P).__absorb_array_avx2x4
 : st=_st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ aT = size _l0 %% _r8
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _len /\ to_uint _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ sub _buf0 (to_uint _off) _len)
            (_l1 ++ sub _buf1 (to_uint _off) _len)
            (_l2 ++ sub _buf2 (to_uint _off) _len)
            (_l3 ++ sub _buf3 (to_uint _off) _len)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ sub _buf0 (to_uint _off) _len)
            (_l1 ++ sub _buf1 (to_uint _off) _len)
            (_l2 ++ sub _buf2 (to_uint _off) _len)
            (_l3 ++ sub _buf3 (to_uint _off) _len)
            res.`1
           /\ res.`2 = (size _l0 + _len) %% _r8
           /\ res.`3 = _off + W64.of_int _len.
admitted.

(*
hoare absorb_array_avx2x4_h _l0 _l1 _l2 _l3 _buf _off _len _r8 _tb:
 M(P).__absorb_array_avx2x4
 : aT=size _l %% _r8 /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 st
 /\ 0 <= _len
 /\ to_uint _off + _len < aSIZE
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ sub _buf (to_uint _off) _len)
       /\ res.`3 = _off + W64.of_int (max 0 _len)
     else pabsorb_spec_ref _r8 (_l ++ sub _buf (to_uint _off) _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _off + W64.of_int _len.
proof.
proc.
admit.
qed.
*)
phoare absorb_bcast_array_avx2x4_ll:
 [ M(P).__absorb_bcast_array_avx2x4
 : 0 < rATE8 <= 200 /\ 0 <= lEN /\ to_uint offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
proc.
have L: forall x, x <= aSIZE => x < W64.modulus.
 by move=> *; apply (ler_lt_trans aSIZE) => //; exact aSIZE_u64.
admitted.

hoare absorb_bcast_array_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _off _len _r8 _tb:
 M(P).__absorb_bcast_array_avx2x4
 : st=_st /\ buf=_buf
 /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ aT = size _l0 %% _r8
 /\ pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 /\ 0 <= _len /\ to_uint _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2x4 _r8 _tb
            (_l0 ++ sub _buf (to_uint _off) _len)
            (_l1 ++ sub _buf (to_uint _off) _len)
            (_l2 ++ sub _buf (to_uint _off) _len)
            (_l3 ++ sub _buf (to_uint _off) _len)
            res.`1
     else pabsorb_spec_avx2x4 _r8
            (_l0 ++ sub _buf (to_uint _off) _len)
            (_l1 ++ sub _buf (to_uint _off) _len)
            (_l2 ++ sub _buf (to_uint _off) _len)
            (_l3 ++ sub _buf (to_uint _off) _len)
            res.`1
           /\ res.`2 = (size _l0 + _len) %% _r8
           /\ res.`3 = _off + W64.of_int _len.
admitted.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

phoare dumpstate_array_avx2x4_ll: 
 [ M(P).__dumpstate_array_avx2x4
 : 0 <= lEN <= 200
 ==> true
 ] = 1%r.
proof.
proc => //.
admit(*
seq 2: true => //.
 while (#pre /\ 0 <= to_sint i <= lEN%/8) (lEN %/ 8 - to_sint i).
  move=> z; auto => /> &m; rewrite sltE /= => Hlen0 Hlen1 Hi0 _.
  rewrite of_sintK /smod ifF 1:/# modz_small 1:/# => Hi1.
  have E: to_sint W64.one = 1 by rewrite to_sintE /smod.
  do split. 
  + by rewrite to_sintD_small E /#.
  + by rewrite to_sintD_small E /#.
  + by rewrite to_sintD_small E /#.
 auto => /> &m; rewrite to_sintE /= => *.
 split.
  by rewrite /smod /= /#.
 by move=> i ???; rewrite sltE of_sintK /smod ifF 1:/# modz_small 1:/# /#.
by islossless.
*).
qed.

hoare dumpstate_array_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st:
 M(P).__dumpstate_array_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\ offset=_off /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (_st \a25bits64 0)).[i-to_uint _off]) (to_uint _off) _len _buf0
  /\ res.`2 = A.fill (fun i=> (stbytes (_st \a25bits64 1)).[i-to_uint _off]) (to_uint _off) _len _buf1
  /\ res.`3 = A.fill (fun i=> (stbytes (_st \a25bits64 2)).[i-to_uint _off]) (to_uint _off) _len _buf2
  /\ res.`4 = A.fill (fun i=> (stbytes (_st \a25bits64 3)).[i-to_uint _off]) (to_uint _off) _len _buf3
  /\ res.`5 = _off + W64.of_int _len.
admitted.

(*
hoare dumpstate_array_avx2_h _buf _off _len _st:
 M(P).__dumpstate_array_avx2
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (stavx2_to_st25 _st)).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len.
admitted.

phoare dumpstate_array_avx2_ph _buf _off _len _st:
 [ M(P).__dumpstate_array_avx2
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=> (stbytes (stavx2_to_st25 _st)).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len
 ] = 1%r.
proof.
by conseq dumpstate_array_avx2_ll (dumpstate_array_avx2_h _buf _off _len _st).
qed.
*)

phoare squeeze_array_avx2x4_ll: 
 [ M(P).__squeeze_array_avx2x4
 : 0 < rATE8 <= 200
 ==> true
 ] = 1%r.
admitted.

hoare squeeze_array_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st _r8:
 M(P).__squeeze_array_avx2x4
 : buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3
 /\ offset=_off /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _off + _len <= aSIZE
 ==>
    res.`1 =
     fill (fun i => (SQUEEZE1600 _r8 _len (_st \a25bits64 0)).[i-to_uint _off])
          (to_uint _off) _len _buf0
 /\ res.`2 =
     fill (fun i => (SQUEEZE1600 _r8 _len (_st \a25bits64 1)).[i-to_uint _off])
          (to_uint _off) _len _buf1
 /\ res.`3 =
     fill (fun i => (SQUEEZE1600 _r8 _len (_st \a25bits64 2)).[i-to_uint _off])
          (to_uint _off) _len _buf2
 /\ res.`4 =
     fill (fun i => (SQUEEZE1600 _r8 _len (_st \a25bits64 3)).[i-to_uint _off])
          (to_uint _off) _len _buf3
 /\ res.`6 = iter ((_len - 1) %/ _r8 + 1) keccak_f1600_x4 _st.
admitted.

(*
hoare squeeze_array_avx2_h _buf _off _len _st _r8:
 M(P).__squeeze_array_avx2
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=> (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st)).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1)).
proof.
admitted.


phoare squeeze_array_avx2_ph _buf _off _len _st _r8:
 [ M(P).__squeeze_array_avx2
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=> (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st)).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1))
 ] = 1%r.
proof.
by conseq squeeze_array_avx2_ll (squeeze_array_avx2_h _buf _off _len _st _r8).
qed.
*)

end KeccakArrayAvx2x4.
