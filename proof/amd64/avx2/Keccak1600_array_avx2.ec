(******************************************************************************
   Keccak1600_array_avx2.ec:

   Correctness proof for the Keccak (fixed-sized) array based
  absorb/squeeze AVX2 implementation

******************************************************************************)

require import List Real Distr Int IntDiv StdOrder Ring.

import IntID IntOrder.

from Jasmin require import JModel.
from Jasmin require import JArray.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_SHA3_Spec.
from CryptoSpecs require export Keccak1600_Spec Keccakf1600_Spec.

from JazzEC require Jazz_avx2.

from JazzEC require import WArray200.
from JazzEC require import Array7 Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require export Keccakf1600_avx2 Keccak1600_avx2.


op addstate_avx2 (st: W256.t Array7.t, l: W8.t list): W256.t Array7.t =
 stavx2_from_st25 (addstate (stavx2_to_st25 st) (bytes2state l)).


require import BitEncoding. import BS2Int BitChunking.
 
abstract theory KeccakArrayAvx2.

op aSIZE: int.
axiom aSIZE_ge0: 0 <= aSIZE.
axiom aSIZE_u64: aSIZE < W64.modulus.

module type MParam = {
  proc keccakf1600_avx2 (st:W256.t Array7.t) : W256.t Array7.t
  proc state_init_avx2 () : W256.t Array7.t
  proc pstate_init_avx2 (pst:W64.t Array25.t) : W64.t Array25.t * W256.t Array7.t
  proc addratebit_avx2 (st:W256.t Array7.t, rATE8:int) : W256.t Array7.t
  proc addstate_r3456_avx2 (st:W256.t Array7.t, r3 r4 r5 r6: W256.t): W256.t Array7.t
  proc addpst01_avx2 (st: W256.t Array7.t, pst: W64.t Array25.t): W256.t Array7.t
  proc addpstate_avx2 (st: W256.t Array7.t, pst:W64.t Array25.t): W256.t Array7.t 
}.

clone import PolyArray as A
 with op size <- aSIZE
      proof ge0_size by exact aSIZE_ge0.

clone import WArray as WA
 with op size <- aSIZE.

module M(P: MParam) = {
  proc __aread_subu64 (buf:W8.t A.t, offset:int, dELTA:int, lEN:int,
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
        (offset + dELTA));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA)));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64
          (get16_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA)));
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
            (offset + dELTA)));
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
  proc __aread_bcast_4subu64 (buf:W8.t A.t, offset:int, dELTA:int,
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
        (offset + dELTA)));
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
  proc __aread_subu128 (buf:W8.t A.t, offset:int, dELTA:int,
                        lEN:int, tRAIL:int) : int * int * int * W128.t = {
    var w:W128.t;
    var t64:W64.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WA.init8 (fun i => buf.[i]))
        (offset + dELTA));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          w <-
          (VMOV_64
          (get64_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA)));
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
  proc __aread_subu256 (buf:W8.t A.t, offset:int, dELTA:int,
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
        (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          t128_0 <-
          (get128_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA));
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
  proc __awrite_subu64 (buf:W8.t A.t, offset:int, dELTA:int,
                        lEN:int, w:W64.t) : W8.t A.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (A.init
        (WA.get8_direct
        (WA.set64_direct (WA.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (A.init
          (WA.get8_direct
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
          (WA.get8_direct
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
          (WA.get8_direct
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
  proc __awrite_subu128 (buf:W8.t A.t, offset:int, dELTA:int,
                         lEN:int, w:W128.t) : W8.t A.t * int * int = {
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
          (offset + dELTA)
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
  proc __awrite_subu256 (buf:W8.t A.t, offset:int, dELTA:int,
                         lEN:int, w:W256.t) : W8.t A.t * int * int = {
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
        (buf, dELTA, lEN) <@ __awrite_subu128 (buf, offset, dELTA, lEN,
        t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __addstate_array_avx2 (st:W256.t Array7.t, buf:W8.t A.t,
                              offset:int, lEN:int, tRAILB:int) : W256.t Array7.t *
                                                                   int = {
    var dELTA:int;
    var t64_1, t64_2, t64_3, t64_4, t64_5:W64.t;
    var t128_0:W128.t;
    var r0:W256.t;
    var r1:W256.t;
    var t128_1:W128.t;
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r2:W256.t;
    var r6:W256.t;
    dELTA <- 0;
    (dELTA, lEN, tRAILB, t64_1) <@ __aread_subu64 (buf, offset, dELTA, 
    lEN, tRAILB);
    t128_0 <- (zeroextu128 t64_1);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    st.[0] <- (st.[0] `^` r0);
    (dELTA, lEN, tRAILB, r1) <@ __aread_subu256 (buf, offset, dELTA, 
    lEN, tRAILB);
    st.[1] <- (st.[1] `^` r1);
    if ((0 < lEN)) {
      (dELTA, lEN, tRAILB, t64_2) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_1 <- (zeroextu128 t64_2);
      (dELTA, lEN, tRAILB, r3) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64_3) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_0 <- (zeroextu128 t64_3);
      (dELTA, lEN, tRAILB, r4) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64_4) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
      (dELTA, lEN, tRAILB, r5) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64_5) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_0 <- (VPINSR_2u64 t128_0 t64_5 (W8.of_int 1));
      r2 <-
      (W256.of_int
      (((W128.to_uint t128_0) %% (2 ^ 128)) +
      ((2 ^ 128) * (W128.to_uint t128_1))));
      st.[2] <- (st.[2] `^` r2);
      (dELTA, lEN, tRAILB, r6) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      st <@ P.addstate_r3456_avx2 (st, r3, r4, r5, r6);
    } else {
      
    }
    offset <- (offset + dELTA);
    return (st, offset);
  }
  proc __absorb_array_avx2 (st:W256.t Array7.t, buf:W8.t A.t,
                            offset:int, lEN:int, rATE8:int, tRAILB:int) : 
  W256.t Array7.t * int = {
    var aLL:int;
    var iTERS:int;
    var i:int;
    aLL <- (lEN + ((tRAILB <> 0) ? 1 : 0));
    iTERS <- (lEN %/ rATE8);
    if ((0 < iTERS)) {
      i <-0;
      while ((i < iTERS)) {
        (st, offset) <@ __addstate_array_avx2 (st, buf, offset, rATE8, 0);
        st <@ P.keccakf1600_avx2 (st);
        i <- i + 1;
      }
    } else {
      
    }
    lEN <- (lEN %% rATE8);
    (st, offset) <@ __addstate_array_avx2 (st, buf, offset, lEN, tRAILB);
    if ((tRAILB <> 0)) {
      st <@ P.addratebit_avx2 (st, rATE8);
    } else {
      
    }
    return (st, offset);
  }
  proc __pstate_array_avx2 (pst:W64.t Array25.t, aT:int, buf:W8.t A.t,
                            offset:int, lEN:int, tRAILB:int) : W64.t Array25.t *
                                                                 int * int = {
    var aLL:int;
    var dELTA:int;
    var lO:int;
    var at:W64.t;
    var t64:W64.t;
    var t256:W256.t;
    var t128:W128.t;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    dELTA <- 0;
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    at <- (W64.of_int (aT %/ 8));
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        (dELTA,  _2, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
        lEN, tRAILB);
        t64 <- (t64 `<<` (W8.of_int (8 * lO)));
        pst.[(W64.to_uint at)] <- (pst.[(W64.to_uint at)] `^` t64);
        lO <- 0;
        aT <- 0;
        lEN <- 0;
      } else {
        if ((8 <= lEN)) {
          t64 <-
          (get64_direct (WA.init8 (fun i => buf.[i]))
          (offset + dELTA));
          dELTA <- (dELTA + (8 - lO));
        } else {
          (dELTA,  _0,  _1, t64) <@ __aread_subu64 (buf, offset, dELTA,
          (8 - lO), 0);
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t64 <- (t64 `<<` (W8.of_int (8 * lO)));
        pst.[(W64.to_uint at)] <- (pst.[(W64.to_uint at)] `^` t64);
        at <- (at + (W64.of_int 1));
      }
    } else {
      
    }
    if ((32 <= lEN)) {
      offset <- (offset + dELTA);
      dELTA <- 0;
      while ((at \ult (W64.of_int ((aT %/ 8) + (4 * (lEN %/ 32)))))) {
        t256 <-
        (get256_direct (WA.init8 (fun i => buf.[i]))
        offset);
        offset <- offset + 32;
        pst <-
        (Array25.init
        (WArray200.get64
        (WArray200.set256_direct (WArray200.init64 (fun i => pst.[i]))
        (W64.to_uint ((W64.of_int 8) * at)) t256)));
        at <- (at + (W64.of_int 4));
      }
      lEN <- (lEN %% 32);
    } else {
      
    }
    if ((16 <= lEN)) {
      t128 <-
      (get128_direct (WA.init8 (fun i => buf.[i]))
      (offset + dELTA));
      dELTA <- (dELTA + 16);
      pst <-
      (Array25.init
      (WArray200.get64
      (WArray200.set128_direct (WArray200.init64 (fun i => pst.[i]))
      (W64.to_uint ((W64.of_int 8) * at)) t128)));
      at <- (at + (W64.of_int 2));
      lEN <- (lEN - 16);
    } else {
      
    }
    if ((8 <= lEN)) {
      t64 <-
      (get64_direct (WA.init8 (fun i => buf.[i]))
      (offset + dELTA));
      dELTA <- (dELTA + 8);
      pst <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => pst.[i]))
      (W64.to_uint ((W64.of_int 8) * at)) t64)));
      at <- (at + (W64.of_int 1));
      lEN <- (lEN - 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
      } else {
        
      }
      (dELTA,  _3, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
      lO, tRAILB);
      pst.[(aLL %/ 8)] <- t64;
    } else {
      
    }
    offset <- offset + dELTA;
    return (pst, aLL, offset);
  }
  proc __pabsorb_array_avx2 (pst:W64.t Array25.t, aT:int, st:W256.t Array7.t,
                             buf:W8.t A.t, offset:int, lEN:int,
                             rATE8:int, tRAILB:int) : W64.t Array25.t * int *
                                                      W256.t Array7.t * int = {
    var aLL:int;
    var iTERS:int;
    var i:int;
    var  _0:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (pst, aT, offset) <@ __pstate_array_avx2 (pst, aT, buf, offset, 
      lEN, tRAILB);
      if ((tRAILB <> 0)) {
        i <- (aT %/ 8) + 1;
        if ((aT <= (5 * 8))) {
          while (i <  5) {
            pst.[i] <- (W64.of_int 0);
            i <- (i + 1);
          }
          st <@ P.addpst01_avx2 (st, pst);
          st <@ P.addratebit_avx2 (st, rATE8);
        } else {
          while ((i < rATE8 %/ 8)) {
            pst.[i] <- (W64.of_int 0);
            i <- i + 1;
          }
          pst <-
          (Array25.init
          (WArray200.get64
          (WArray200.set8 (WArray200.init64 (fun i_0 => pst.[i_0]))
          (rATE8 - 1)
          ((get8 (WArray200.init64 (fun i_0 => pst.[i_0])) (rATE8 - 1)) `^`
          (W8.of_int 128)))));
          st <@ P.addpstate_avx2 (st, pst);
        }
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        (pst,  _0, offset) <@ __pstate_array_avx2 (pst, aT, buf, offset,
        (rATE8 - aT), 0);
        lEN <- (lEN - (rATE8 - aT));
        st <@ P.addpstate_avx2 (st, pst);
        st <@ P.keccakf1600_avx2 (st);
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st, offset) <@ __addstate_array_avx2 (st, buf, offset, rATE8, 0);
        st <@ P.keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      lEN <- (aLL %% rATE8);
      if ((tRAILB <> 0)) {
        (st, offset) <@ __addstate_array_avx2 (st, buf, offset, lEN, tRAILB);
        st <@ P.addratebit_avx2 (st, rATE8);
      } else {
        if ((lEN <> 0)) {
          (pst, aT, offset) <@ __pstate_array_avx2 (pst, 0, buf, offset, 
          lEN, tRAILB);
        } else {
          
        }
      }
    }
    return (pst, aT, st, offset);
  }
  proc __dumpstate_array_avx2 (buf:W8.t A.t, offset:int, lEN:int,
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
    if ((8 <= lEN)) {
      (buf, dELTA,  _0) <@ __awrite_subu256 (buf, offset, dELTA, 8, st.[0]);
      lEN <- (lEN - 8);
    } else {
      (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN,
      st.[0]);
    }
    (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN, st.[1]);
    if ((0 < lEN)) {
      t128_0 <- (truncateu128 st.[2]);
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t <- (truncateu64 t128_1);
      (buf, dELTA, lEN) <@ __awrite_subu64 (buf, offset, dELTA, lEN, t);
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
    
      if ((0 < lEN)) {
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
        (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN,
          t256_4);
        if ((0 < lEN)) {
          t <- (truncateu64 t128_0);
          (buf, dELTA, lEN) <@ __awrite_subu64 (buf, offset, dELTA, lEN, t);
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
        
        }
        if ((0 < lEN)) {
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
          (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN,
            t256_4);
        } else {
          
        }
        if ((0 < lEN)) {
          t <- (truncateu64 t128_1);
          (buf, dELTA, lEN) <@ __awrite_subu64 (buf, offset, dELTA, lEN, t);
        } else {
        
        }
        if ((0 < lEN)) {
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
          (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN,
            t256_4);
        } else {
        
        }
        if ((0 < lEN)) {
          t <- (truncateu64 t128_0);
          (buf, dELTA, lEN) <@ __awrite_subu64 (buf, offset, dELTA, lEN, t);
        } else {
        
        }
        if ((0 < lEN)) {
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
          (buf, dELTA, lEN) <@ __awrite_subu256 (buf, offset, dELTA, lEN,
            t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc __squeeze_array_avx2 (buf:W8.t A.t, offset:int, lEN:int,
                             st:W256.t Array7.t, rATE8:int) : W8.t A.t *
                                                              W256.t Array7.t = {
    var iTERS:int;
    var lO:int;
    var i:int;
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- 0;
        while (i < iTERS) {
          st <@ P.keccakf1600_avx2 (st);
          (buf, offset) <@ __dumpstate_array_avx2 (buf, offset, rATE8, st);
          i <- i + 1;
        }
      } else {
        
      }
      if ((0 < lO)) {
        st <@ P.keccakf1600_avx2 (st);
        (buf, offset) <@ __dumpstate_array_avx2 (buf, offset, lO, st);
      } else {
        
      }
    } else {
      
    }
    return (buf, st);
  }
}.


(*
   PARAMETER MODULE
*)
module P: MParam = {
  proc keccakf1600_avx2 = Jazz_avx2.M._keccakf1600_avx2
  proc state_init_avx2 = Jazz_avx2.M.__state_init_avx2
  proc pstate_init_avx2 = Jazz_avx2.M.__pstate_init_avx2
  proc addratebit_avx2 = Jazz_avx2.M.__addratebit_avx2
  proc addstate_r3456_avx2 = Jazz_avx2.M.__addstate_r3456_avx2
  proc addpst01_avx2 = Jazz_avx2.M.__addpst01_avx2
  proc addpstate_avx2 = Jazz_avx2.M._addpstate_avx2
}.


lemma  aread_subu64_ll: islossless M(P).__aread_subu64
 by islossless.

 lemma aread_subu64_contract(_buf : W8.t A.t, _off _dlt _len _trail _r1 _r2 _r3: int, _r4:W64.t) :
   0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 8 <= aSIZE /\ 0 <= _trail < 256 /\
   ((!8 %| _dlt) => _trail = 0 /\ _len = 0) /\ 0 <= _dlt <= 200 - 8  /\ 0 <= _len /\ _len + _dlt <= 200 - b2i (_trail<>0)  =>
 (   _r1 = _dlt + min (max 0 _len) 8
  /\ _r2 = _len - min (max 0 _len) 8
  /\ _r3 = (if _len < 8 then 0 else _trail)
  /\ _r4 =  W8u8.pack8 (sub _buf (_off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail])) =>
  _r4 = (bytes2state (sub _buf _off (_len+_dlt) ++ if _trail<>0 then [W8.of_int _trail] else [])).[_dlt %/ 8 + b2i (!8 %| _dlt)].
 proof.
 move => [#] ????????? [#] ??? ->.
 case (!8 %| _dlt) => Hdiv.
 + have -> : _trail = 0 by smt().
   have -> : _len = 0 by smt().
   simplify min max b2i=> /=.
   rewrite /bytes2state pack8E get_of_list 1:/# wordP => k kb.
   rewrite initiE 1:/# /= /w64L_from_bytes get_of_list 1:/#.
   case (_dlt %/ 8 + 1 < (_dlt + 1) %/ 8 + b2i (! 8 %| (_dlt + 1))) => ?.
   + rewrite (nth_map []) /=.
      + rewrite size_chunkify 1:/# size_cat size_sub 1:/# /= /# .
   rewrite pack8E initiE 1:/# /= get_of_list 1:/# /= nth_chunkify 1,2:/#.
   rewrite nth_take 1,2:/# nth_drop 1,2:/#.
   rewrite nth_cat size_sub 1:/#.
   rewrite nth_cat size_sub 1:/#.
   case (k %/ 8 < min (max 0 _len) 8) => ?; last by smt().
   rewrite ifT 1:/# /sub !nth_mkseq 1,2:/# /= /#.
 rewrite nth_cat size_sub // ifF 1:/# /= (nth_default) //=.
 by rewrite size_map size_chunkify 1:/# size_cat size_sub /= /#.

 
 rewrite /bytes2state pack8E get_of_list 1:/# wordP => k kb.
 rewrite initiE 1:/# /= /w64L_from_bytes get_of_list 1:/#.
 pose xtra := if _trail <> 0 then [W8.of_int _trail] else [].
 case (_dlt %/ 8 < (_len + _dlt + size xtra) %/ 8 + b2i (! 8 %| (_len + _dlt + size xtra))) => ?.
 + rewrite (nth_map []) /=.
   + rewrite size_chunkify 1:/# size_cat size_sub  /# .
   rewrite pack8E initiE 1:/# /= get_of_list 1:/# /= nth_chunkify 1,2:/#.
   rewrite nth_take 1,2:/# nth_drop 1,2:/#.
   rewrite nth_cat size_sub 1:/#.
   rewrite nth_cat size_sub 1:/#.
   case (k %/ 8 < min (max 0 _len) 8) => ?; last by rewrite /xtra /=; smt().
   rewrite ifT 1:/# /sub !nth_mkseq 1,2:/# /= /#.
 case (k %/ 8 < min (max 0 _len) 8) => ?.
 + rewrite nth_cat size_sub 1:/# ifT 1:/#.
   rewrite (nth_default) //=; 1: by rewrite size_sub /#.
   rewrite (nth_default) //=;  by rewrite size_map size_chunkify 1:/# size_cat size_sub /= /#.
 rewrite nth_cat size_sub 1:/# ifF 1:/# /=.
 rewrite (nth_default) //=;1:  by rewrite size_map size_chunkify 1:/# size_cat size_sub /= /#.
 case (_trail = 0) => Ht; 2: by smt().
 by rewrite Ht /=.
qed.

hoare aread_subu64_h _buf _off _dlt _len _trail:
 M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
    0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 8 <= aSIZE /\ 0 <= _trail < 256
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (_off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail]). 
pose ll := min (max 0 _len) 8.
proc => /=.
case (lEN <= 0).
+ rcondt ^if; 1: by auto.
  auto => /> [#]?????;do split; 1..3:smt().
  rewrite W8u8.of_uint_pack8.
  congr; apply W8u8.Pack.ext_eq => i ib.
  rewrite !get_of_list // (nth_map witness) /=; 1:smt(size_iota).
  rewrite nth_cat size_sub 1:/# /= ifF 1:/# /= nth_iota //=.
  case (i = 0) => Hi;
     1: by rewrite Hi /max /min /= ifT 1:/# to_uint_eq /= !modz_mod.
  rewrite ifF 1:/#; congr; have : 2^8 <= 2^(8*i); last by  simplify; smt(). 
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).
  
rcondf ^if; 1: by auto.
case (8 <= lEN).
+ rcondt ^if;1: by auto.
   auto => /> [#] ??????; do split;1..3:smt().
  rewrite /get64_direct;congr; apply W8u8.Pack.ext_eq => i ib.
  rewrite initiE 1:/# /=  get_of_list //. 
  rewrite nth_cat size_sub 1:/# /= ifT 1:/# /=.
  by rewrite nth_sub 1:/# /= initiE /#.

rcondf ^if; 1: by auto.

(* We have ll = lEN *)

auto => /> ??????.

have H : _len \in iota_ 0 8 by smt(mem_iota).
rewrite -iotaredE /= in H.

elim H => />.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.

(* _len = 7 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2iE 1:/# /= initiE 1:/# /= initiE 1:/# /= (: 0 <= i-32 < 64) 1:/# /=.
  case (32 <= i < 48) => ibbb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite get16E pack2E  initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2iE 1:/# initiE 1:/# /= initiE 1:/# /=.
  case (48 <= i < 56) => ibbbb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite /get8 initiE 1:/# /= nth_sub 1:/# get_to_uint /= of_uintK /= modz_small 1:/# (modz_small _ 18446744073709551616)  1:/#. 
    suff : 256 * (_trail %% 256) %/ 2 ^ (i - 48) %% 2 = 0 by smt().
    rewrite mulrC -pow2_8 divMr; 1: by apply dvdz_exp2l;smt().
    rewrite expz_div 1,2:/# (: 8 - (i - 48) = (8 - (i - 48) - 1) + 1) 1:/#.
    rewrite exprS 1:/# (Ring.IntID.mulrC 2 _) /#.

  rewrite ifF 1:/# zerowE /=  ifF 1:/# /= ifT 1:/#.
  rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 48 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /=.
  have -> : 2 ^ (i - 48) = 2^((i-48-8) + 8) by auto.
  rewrite exprD_nneg 1,2:/#mulrC -pow2_8 divzMpr //=.  
  by have -> : i-56 = i%%8 by smt().

+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2iE 1:/# /= initiE 1:/# /= initiE 1:/# /= (: 0 <= i-32 < 64) 1:/# /=.
  case (32 <= i < 48) => ibbb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite get16E pack2E  get_out 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /= initiE 1:/# /=.
  case (48 <= i < 56) => ibbbb.
  + rewrite ifT 1:/# ifT 1:/#.
    by rewrite /get8 initiE 1:/# /= nth_sub /#.
  rewrite ifF 1:/# zerowE /=  ifF 1:/# /= ifT 1:/#.
  rewrite !get_to_uint /= (: 0 <= i %% 8 < 8) 1:/# /=.
  by have -> /= : _trail %% 256 = 0 by smt().

(* _len = 6 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2iE 1:/# /= initiE 1:/# /= initiE 1:/# /= (: 0 <= i-32 < 64) 1:/# /=.
  case (32 <= i < 48) => ibbb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite get16E pack2E  initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# zerowE /=  ifF 1:/#.
  rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 48 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /=.
  case (48 <= i < 56) => ibbbb.
  + rewrite ifT 1:/# !of_uintK /=.
    by have -> : i-48 = i%%8 by smt().
  rewrite ifF 1:/# /=.
  suff /= : 2^8 <= 2 ^ (i - 48)  by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

+ split; 1: smt().
  apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# get_out 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /= ifT 1:/#.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (32 <= i < 48) => ibbb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite get16E pack2E  initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# ifF 1:/# zerowE. 
  case (48 <= i < 56) => ibbbb.
  + rewrite ifT 1:/#.
    rewrite !get_to_uint /= (: 0 <= i %% 8 < 8) 1:/# /=.
     by have -> /= : _trail %% 256 = 0 by smt().
  by rewrite ifF 1:/# zerowE /=.

(* _len = 5 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2iE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (32 <= i < 40) => ibbb.
  + rewrite ifT 1:/# ifT 1:/# /get8  initiE 1:/# /=. 
    rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 32 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /= (:0 <= (i - 32) %% 8 < 8) 1:/# /=.
    rewrite nth_sub 1:/#.
    have -> : (i - 32) %% 8 = i %% 8 by smt().
    have ->/= : 256 * (_trail %% 256) %/ 2 ^ (i - 32) %% 2 = 0;
       last by smt().
    have /={1}-> : 2 ^ 8 = 2^(8 - (i-32) + (i-32)) by congr;smt().
    rewrite exprD_nneg 1,2:/# mulrC mulrA mulzK;1:smt(expr_gt0).
    have ->: 2 ^ (8 - (i - 32)) = 2 ^ ((8 - (i - 32) - 1) + 1); 1: by congr;auto.
    rewrite exprS 1:/# /#.
  rewrite ifF 1:/# zerowE /=  ifF 1:/#.
  rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 32 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /=.
  rewrite mulrC -{2}pow2_8 (:2^(i-32) = 2^((i-32-8)+8));1: by congr;smt().
  rewrite exprD_nneg /= 1,2:/# divzMpr //=.
  case (40 <= i < 48) => ibbbb.
  + rewrite ifT 1:/# !of_uintK /=;1:do congr;smt().
  rewrite ifF 1:/# /=; suff /= : 2^8 <= 2^(i-40) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# get_out 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /= ifT 1:/#.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (32 <= i < 40) => ibbb.
  + rewrite ifT 1:/# ifT 1:/# /get8  initiE 1:/# /=. 
    rewrite nth_sub /#.
  rewrite ifF 1:/# zerowE /=  ifF 1:/#.
  case (40 <= i < 48) => ibbbb.
  + rewrite ifT 1:/# get_to_uint !of_uintK /= (:0 <= i %% 8 < 8) 1:/# /=.
    by have -> /= : _trail %% 256 = 0;smt().
  rewrite ifF 1:/# /=; suff /= : 2^8 <= 2^(i-40) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).


(* _len = 4 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# ifF 1:/# get_to_uint (: 0 <= i - 32 < 64) 1:/# /= of_uintK /=  (modz_small _ 18446744073709551616)  1:/#.
  case (32 <= i < 40) => ibbb.
  + rewrite ifT 1:/# get_to_uint /= (: 0 <= i %% 8 < 8) 1:/# /=.
    by have -> : (i - 32) = i %% 8 by smt().
  rewrite ifF 1:/# /=; suff /= : 2^8 <= 2^(i-32) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

+ split;1:smt().
  apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get32E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /=.
  case (0 <= i < 32) => ibb.
  + rewrite ifT 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /= ifT 1:/#.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /=. 
  rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (32 <= i < 40) => ibbb.
  + rewrite ifF 1:/# ifT 1:/# get_to_uint !of_uintK /= (:0 <= i %% 8 < 8) 1:/# /=. 
    by have -> /= : _trail %% 256 = 0;smt().
  case (40 <= i < 48) => ibbbb.
  + by rewrite ifF 1:/# ifF 1:/# get_to_uint (:0 <= i %% 8 < 8) 1:/# /=.
  by rewrite ifF 1:/# /= ifF 1:/# /=.

 (* _len = 3 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get16E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 16) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# map2E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /=.
  case (16 <= i < 24) => ibbb.
  + rewrite ifT 1:/# ifT 1:/# /get8  initiE 1:/# /=. 
    rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 16 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /= (:0 <= (i - 16) %% 8 < 8) 1:/# /=.
    rewrite nth_sub 1:/#.
    have -> : (i - 16) %% 8 = i %% 8 by smt().
    have ? : 256 * (_trail %% 256) %/ 2 ^ (i - 16) %% 2 = 0; last by have -> : i %/8 = 2; smt().
    have /={1}-> : 2 ^ 8 = 2^(8 - (i-16) + (i-16)) by congr;smt().
    rewrite exprD_nneg 1,2:/# mulrC mulrA mulzK;1:smt(expr_gt0).
    have ->: 2 ^ (8 - (i - 16)) = 2 ^ ((8 - (i - 16) - 1) + 1); 1: by congr;auto.
    rewrite exprS 1:/# /#.
  rewrite ifF 1:/# zerowE /=  ifF 1:/#.
  rewrite !get_to_uint /= !of_uintK /= (modz_small _ 18446744073709551616)  1:/# (: (0 <= i - 16 < 64)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /=.
  rewrite mulrC -{2}pow2_8 (:2^(i-16) = 2^((i-16-8)+8));1: by congr;smt().
  rewrite exprD_nneg /= 1,2:/# divzMpr //=.
  case (24 <= i < 32) => ibbbb.
  + rewrite ifT 1:/# !of_uintK /=;1:do congr;smt().
  rewrite ifF 1:/# /=; suff /= : 2^8 <= 2^(i-24) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get16E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /=.
  case (0 <= i < 16) => ibb.
  + rewrite ifT 1:/# /= W16.initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= W64.get_out 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /= ifT 1:/#.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=. 
  rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (16 <= i < 24) => ibbb.
  + rewrite ifT 1:/# ifT 1:/# /get8  initiE 1:/# /=. 
    rewrite !get_to_uint /= (:(0 <= (i - 16) %% 8 < 8)) 1:/# /= (: 0 <= i %% 8 < 8) 1:/# /=.
    rewrite nth_sub 1:/#.
    have -> : (i - 16) %% 8 = i %% 8 by smt().
    have ? : 256 * (_trail %% 256) %/ 2 ^ (i - 16) %% 2 = 0; last by have -> : i %/8 = 2; smt().
    have /={1}-> : 2 ^ 8 = 2^(8 - (i-16) + (i-16)) by congr;smt().
    rewrite exprD_nneg 1,2:/# mulrC mulrA mulzK;1:smt(expr_gt0).
    have ->: 2 ^ (8 - (i - 16)) = 2 ^ ((8 - (i - 16) - 1) + 1); 1: by congr;auto.
    rewrite exprS 1:/# /#.
  case (24 <= i < 32) => ibbbb.
  + rewrite ifF 1:/# ifF 1:/# ifT 1:/# get_to_uint (:0 <= (i-16) %% 8 < 8) 1:/# /= get_to_uint (: 0 <= i %% 8 < 8) 1:/# /= (: _trail %% 256 = 0) /#.
   by rewrite ifF 1:/# /= ifF 1:/# /= ifF 1:/# get_to_uint (:0 <= i %% 8 < 8) 1:/# /=.

 (* _len = 2 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# shlwE ib /=.
  rewrite !zeroextu64E get16E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 16) => ibb.
  + rewrite ifT 1:/# ifT 1:/#.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    by rewrite W64.get_out 1:/# nth_sub;smt().
  rewrite ifF 1:/# ifF 1:/# get_to_uint (:  0 <= i - 16 < 64) 1:/# /= of_uintK /= (modz_small _ 18446744073709551616)  1:/# /=.
  case (16 <= i < 24) => ibbb.
  + rewrite ifT 1:/#.
    rewrite !get_to_uint /= (: 0 <= i %% 8 < 8) 1:/# /=;do congr;smt().
  rewrite ifF 1:/# /=; suff /= : 2^8 <= 2^(i-16) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

  + split;1:smt().
  apply W64.wordP => i ib.
  rewrite  /(`<<`) /= ib /=.
  rewrite !zeroextu64E get16E !pack8E !pack4E !pack2E initiE 1:/# /=.
  rewrite initiE 1:/# /=.
  case (0 <= i < 16) => ibb.
  + rewrite ifT 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /= ifT 1:/#.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# initiE 1:/# /=. 
  rewrite !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (16 <= i < 24) => ibbb.
  + rewrite ifF 1:/# ifT 1:/# get_to_uint !of_uintK /= (:0 <= i %% 8 < 8) 1:/# /=. 
    by have -> /= : _trail %% 256 = 0;smt().
  case (24 <= i < 32) => ibbbb.
  + by rewrite ifF 1:/# ifF 1:/# get_to_uint (:0 <= i %% 8 < 8) 1:/# /=.
  by rewrite ifF 1:/# /= ifF 1:/# /=.

(* _len = 1 *) 
split => *.
+ apply W64.wordP => i ib.
  rewrite !orE  /= /(`<<`) /= map2iE 1:/# ib /=.
  rewrite !zeroextu64E /get8 !pack8E initiE 1:/# /=.
  rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= !get_of_list 1:/# /= nth_cat size_sub 1:/# /=.
  case (0 <= i < 8) => ibb.
  + rewrite ifT 1:/# ifT 1:/# get_to_uint !of_uintK /= ib /= (modz_small _ 18446744073709551616)  1:/#.
    rewrite mulrC -{2}pow2_8 (:2^8 = 2^((8 - i) + i));1: by congr;smt().
    rewrite exprD_nneg /= 1,2:/# mulrA mulzK;1:smt(expr_gt0).
     have ->: 2 ^ (8 - i) = 2 ^ (((8 - i) - 1) + 1); 1: by congr;auto.
    rewrite exprS 1:/# mulrA mulrC mulrA modzMl.
    by rewrite nth_sub;smt().
  rewrite ifF 1:/# ifF 1:/# zerowE /= get_to_uint ib /= of_uintK /= (modz_small _ 18446744073709551616)  1:/#.
  case (8 <= i < 16) => ibbb.
  + rewrite ifT 1:/# get_to_uint (: 0 <= i %% 8 < 8) 1:/# /=.
    rewrite mulrC -{2}pow2_8 (:2^(i) = 2^((i-8)+8));1: by congr;smt().
    rewrite exprD_nneg /= 1,2:/# divzMpr //=.
    by have -> : i - 8 = i %% 8;smt().
  rewrite ifF 1:/# /=.
  have ? : 256 * (_trail %% 256) %/ 2 ^ (i) %% 2 = 0; last by smt().
  suff /= : 2^16 <= 2^(i) by smt().
  by apply (ler_weexpn2l 2) => /=;smt(expr_ge0).

+ apply W64.wordP => i ib.
  rewrite  /(`<<`) /= ib /=.
  rewrite !zeroextu64E  !pack8E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= get_of_list 1:/# /=.
  case (0<=i<8) => ibb.
  + rewrite ifT 1:/# /get8 initiE 1:/# /=.
  rewrite   nth_cat size_sub 1:/# /= ifT 1:/# nth_sub /#.
  rewrite ifF 1:/#.
  rewrite   nth_cat size_sub 1:/# /= ifF 1:/#.
  case (8 <= i < 16) => ibbb.
  + rewrite ifT 1:/# get_to_uint !of_uintK /= (: 0 <= i %% 8 < 8) 1:/# /=.
    have -> : _trail %% 256 = 0 by smt().
  by smt().
  by rewrite ifF 1:/# /=. 
qed.

phoare aread_subu64_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
    0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 8 <= aSIZE /\ 0 <= _trail<256 
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (_off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu64_ll (aread_subu64_h _buf _off _dlt _len _trail).
qed.

lemma  aread_subu128_ll: islossless M(P).__aread_subu128
 by islossless.

hoare aread_subu128_h _buf _off _dlt _len _trail:
 M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
     0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 16 <= aSIZE  /\  0 <= _trail < 256 
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (_off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail]).
  proc. 
  case (lEN <= 0 /\ tRAIL %% 256 = 0).
  + rcondt 1; 1: by auto.
    auto => /> *;do split;1..3: smt().
    rewrite pack16E wordP => i ib.
    rewrite initiE  1:/# /= get_of_list 1:/# nth_cat size_sub 1:/# ifF 1:/# /=.
    case (i %/ 8 - min (max 0 _len) 16 = 0) => ?.
    + rewrite of_intwE /= /int_bit /= (: _trail %% 256 = 0) /= /#.
    by rewrite zerowE.

  rcondf  1; 1: by auto.

  case (16 <= lEN).
  + rcondt 1; 1: by auto.
    auto => /> *;do split; 1..3 :smt().
    rewrite get128E /of_list;congr; apply W16u8.Pack.ext_eq => i ob.
    rewrite !initiE 1,2:/# /= nth_cat nth_sub 1:/# size_sub 1:/# /= ifT 1:/#.
    by rewrite /init8 initiE 1:/#.

  rcondf 1;1: by auto.
  case (8<=lEN); last first.
  + rcondf 1; 1: by auto.
    wp; call (aread_subu64_h _buf _off _dlt _len _trail).
    auto => /> *; do split;1:smt().
    move => ? [r1 r2 r3 r4] />;do split; 1..3:smt().
    rewrite wordP => i ib; rewrite pack16E  zeroextu128_bit initiE 1:/# /= get_of_list 1:/#.
    case (0 <= i < 64) => ? /=.
    + rewrite pack8E initiE 1:/# /= get_of_list 1:/# !nth_cat !size_sub /#.
    rewrite nth_default; 1: by rewrite size_cat size_sub /#.
    by rewrite zerowE.

  rcondt 1;1: by auto.
  wp; call (aread_subu64_h _buf _off (_dlt+8) (_len-8) _trail).
  auto => /> *; do split;1,2: smt().
  move => ?? [r1 r2 r3 r4] />;do split; 1..3:smt().
  rewrite /VPINSR_2u64 /VMOV_64.
  rewrite pack2E pack16E wordP => i ib; rewrite W128.initiE 1:/# initiE 1:/# /=.
  rewrite initiE 1:/# get_of_list 1:/# /= pack2E.
  case (0 <= i < 64) => ? /=; last first.
  + rewrite ifT 1:/# /= pack8E initiE 1:/# /= get_of_list 1: /# /=.
    case (min (max 0 (_len - 8)) 8 + 1 <= i %% 64 %/ 8) => ?.
    + by rewrite !nth_default;1,2: by rewrite size_cat size_sub /= /#.
    rewrite !nth_cat !size_sub 1,2:/#;congr;last by smt().
    congr;1,3:smt().
    case (i %% 64 %/ 8 < _len - 8) => ?.
    + rewrite !nth_sub /#.
    by rewrite !nth_default;1,2: by rewrite size_sub /#.
  rewrite ifF 1:/# bits64E initiE 1:/# /= initiE 1:/# /= get_of_list 1:/# /= ifT 1:/# get64E.
  rewrite pack8E /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite nth_cat size_sub 1:/# ifT 1:/# nth_sub /#. 
qed.

 phoare aread_subu128_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
   0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 16 <= aSIZE /\ 0 <= _trail < 256 
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (_off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail])
 ] = 1%r. 
proof. 
by conseq aread_subu128_ll (aread_subu128_h _buf _off _dlt _len _trail).
qed.

lemma  aread_subu256_ll: islossless M(P).__aread_subu256
 by islossless.

lemma aread_subu256_contract(_buf : W8.t A.t, _off _dlt _len _trail _r1 _r2 _r3: int, _r4:W256.t) :
   0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 32 <= aSIZE /\ 0 <= _trail < 256 /\
   ((!8 %| _dlt) => (_len = 0 /\ _trail = 0)) /\ 0 <= _dlt <= 200-32 /\ 0 <= _len /\ _len + _dlt <= 200 - b2i (_trail<>0)  =>
 (   _r1 = _dlt + min (max 0 _len) 32
  /\ _r2 = _len - min (max 0 _len) 32
  /\ _r3 = (if _len < 32 then 0 else _trail)
  /\ _r4 =  W32u8.pack32 (sub _buf (_off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail])) =>
  forall k, 0<=k<4 =>
  (W4u64.unpack64 _r4).[k] = (bytes2state (sub _buf _off (_len+_dlt) ++ if _trail<>0 then [W8.of_int _trail] else [])).[_dlt %/ 8+k + b2i ((!8 %| _dlt))].
 proof.
 move => [#] ????????? [#] ??? -> kk kkb.
  case (!8 %| _dlt) => Hdiv.
 + have -> : _trail = 0 by smt().
   have -> : _len = 0 by smt().
   simplify min max b2i=> /=.
   rewrite /bytes2state pack32E get_of_list 1:/# wordP => k kb.
   rewrite unpack64E initiE 1:/# /= bits64E initiE 1:/# /= initiE 1:/# /= /w64L_from_bytes get_of_list 1:/# nth_cat size_sub 1:/# /=.
   case (_dlt %/ 8 + kk + 1 < (_dlt + 1) %/ 8 + b2i (! 8 %| (_dlt + 1))) => ?.
   + rewrite (nth_map []) /=.
     + rewrite size_chunkify 1:/# size_cat size_sub 1:/# /= /#.
   rewrite pack8E initiE 1:/# /= get_of_list 1:/# /= nth_chunkify 1,2:/#.
   rewrite nth_take 1,2:/# nth_drop 1,2:/#.
   rewrite nth_cat size_sub 1:/#.
   rewrite ifF 1:/# /=.
   case (8 * (_dlt %/ 8 + kk) + k %/ 8 < _dlt) => ?; last by smt().
   rewrite nth_sub 1:/# /#. 
   rewrite  ifF 1:/# /= nth_default.
   + rewrite size_map size_chunkify 1:/# size_cat size_sub 1:/# /= /# .
   by rewrite zerowE /=.

 rewrite /bytes2state pack32E get_of_list 1:/# wordP => k kb.
 rewrite unpack64E initiE 1:/# /= bits64E initiE 1:/# /= initiE 1:/# /= /w64L_from_bytes get_of_list 1:/# nth_cat size_sub 1:/# /=.
 pose xtra := if _trail <> 0 then [W8.of_int _trail] else [].
 case (_dlt %/ 8 + kk <  (_len + _dlt + size xtra) %/ 8 + b2i (! 8 %| (_len + _dlt + size xtra))) => ?.
 + rewrite (nth_map []) /=.
   + by rewrite size_chunkify 1:/# size_cat size_sub /#.
   rewrite pack8E initiE 1:/# /= get_of_list 1:/# /= nth_chunkify 1,2:/#.
   rewrite nth_take 1,2:/# nth_drop 1,2:/#.
   rewrite nth_cat size_sub 1:/#.
   case ((kk * 64 + k) %/ 8 < min (max 0 _len) 32) => ?;last by rewrite /xtra /#.   
   by rewrite  ifT 1:/# !nth_sub 1,2:/# /#.


 case ((kk * 64 + k) %/ 8 < min (max 0 _len) 32) => ?.
 rewrite nth_sub 1:/#  (nth_default) /=.
   rewrite size_map size_chunkify 1:/# size_cat size_sub 1:/# /= /# .
   by smt(W64.get_out).

 rewrite  (nth_default) /=.
   rewrite size_map size_chunkify 1:/# size_cat size_sub 1:/# /= /# .
 case (_trail = 0) => Ht;1 : by rewrite Ht /=.
 case ((kk * 64 + k) %/ 8 - min (max 0 _len) 32 = 0).  by smt(). by smt(zerowE).

 qed.

 
hoare aread_subu256_h _buf _off _dlt _len _trail:
 M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
   0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 32 <= aSIZE /\ 0 <= _trail < 256 
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (_off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail]).
proof. 
proc. 
  case (lEN <= 0 /\ tRAIL %% 256 = 0).
  + rcondt 1; 1: by auto.
    auto => /> *;do split;1..3: smt().
    rewrite pack32E wordP => i ib.
    rewrite initiE  1:/# /= get_of_list 1:/# nth_cat size_sub 1:/# ifF 1:/# /=.
    case (i %/ 8 - min (max 0 _len) 32 = 0) => ?.
    + rewrite of_intwE /= /int_bit /= (: _trail %% 256 = 0) /= /#.
    by rewrite zerowE.

  rcondf  1; 1: by auto.

  case (32 <= lEN).
  + rcondt 1; 1: by auto.
    auto => /> *;do split; 1..3 :smt().
    rewrite get256E /of_list;congr; apply W32u8.Pack.ext_eq => i ob.
    rewrite !initiE 1,2:/# /= nth_cat nth_sub 1:/# size_sub 1:/# /= ifT 1:/#.
    by rewrite /init8 initiE 1:/#.

  rcondf 1;1: by auto.
  case (16<=lEN); last first.
  + rcondf 1; 1: by auto.
    wp; call (aread_subu128_h _buf _off _dlt _len _trail).
    auto => /> *; do split;1:smt().
    move => ? [r1 r2 r3 r4] />;do split; 1..3:smt().
    rewrite wordP => i ib.
    pose x:= W128.to_uint _; rewrite modz_small; 1:by smt(pow2_128 W128.to_uint_cmp).
    rewrite -/(W2u128.zeroextu256 (pack16 _)) zeroextu256_bit pack32E initiE 1:/# /= get_of_list 1:/#.
    case (0 <= i < 128) => ? /=.
    + rewrite pack16E initiE 1:/# /= get_of_list 1:/# !nth_cat !size_sub /#.
    rewrite nth_default; 1: by rewrite size_cat size_sub /#.
    by rewrite zerowE.

  rcondt 1;1: by auto.
  wp; call (aread_subu128_h _buf _off (_dlt+16) (_len-16) _trail).
  auto => /> *; do split;1,2: smt().
  move => ?? [r1 r2 r3 r4] />;do split; 1..3:smt().
  rewrite of_uint_pack2 -iotaredE /=. 
  rewrite (Ring.IntID.mulrC 340282366920938463463374607431768211456 _) modzMDr modz_mod.
  rewrite divzMDr // divz_small 1:/# !modz_small /=;1,2:by smt(W128.to_uint_cmp pow2_128).
  rewrite pack2E pack32E wordP => i ib.
  rewrite initiE 1:/# initiE 1:/# /= get_of_list 1:/# /= get_of_list 1:/# /=.
  case (0 <= i < 128) => ? /=.
  + rewrite ifT 1:/# /= get128E pack16E initiE 1:/# /= initiE 1:/# /= /init8 initiE 1:/#.
    rewrite nth_cat size_sub 1:/# ifT 1:/# nth_sub /#.
  rewrite ifF 1:/# ifT 1:/# pack16E initiE 1:/# /= get_of_list 1:/# /=.
  rewrite nth_cat size_sub 1:/#.
  case (i %% 128 %/ 8 < min (max 0 (_len - 16)) 16) => ?.
  + by rewrite nth_sub 1:/#  nth_cat size_sub 1:/# ifT 1:/# nth_sub /#.
  case (i %% 128 %/ 8 - min (max 0 (_len - 16)) 16 = 0) => ?; last first.
  + by rewrite  nth_default;1: by rewrite size_cat size_sub /#.
  rewrite nth_cat size_sub 1:/# ifF 1:/# /#.  
qed.

phoare aread_subu256_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail /\
   0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 32 <= aSIZE /\ 0 <= _trail < 256 
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (_off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu256_ll (aread_subu256_h _buf _off _dlt _len _trail).
qed.


lemma awrite_subu64_ll: islossless M(P).__awrite_subu64
 by islossless.

hoare awrite_subu64_h _buf _off _dlt _len _w:
 M(P).__awrite_subu64
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 8 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W8u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8.
proof. 
pose ll := min (max 0 _len) 8.
pose ww := (W8u8.to_list _w).
proc => /=.
case (lEN <= 0).
+ rcondf ^if; 1: by auto => /#.
  auto => /> [#]???;do split => *;2..:smt().
  by rewrite /fill tP => i ib; rewrite initiE 1:/# /= /#.
  
rcondt ^if; 1: by auto => /#.
case (8 <= lEN).
+ rcondt ^if;1: by auto.
  auto => /> [#] ????; do split;2..:smt().
  rewrite /fill tP => i ib; rewrite initiE 1:/# initiE 1:/#.
  rewrite get8_set64_directE 1,2:/# /= /ww.
  case (_off + _dlt <= i < _off + _dlt + 8) => ?;1: by smt(). 
  by rewrite ifF 1:/# /get8 initiE 1:/#.
  
rcondf ^if; 1: by auto.

(* We have ll = lEN *)

auto => /> ????.

have H : _len \in iota_ 0 8 by smt(mem_iota).
rewrite -iotaredE /= in H.

elim H => />.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.
move => H;elim H => />;last first.

(* _len = 7 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 setE /=.
  rewrite wordP => k kb; rewrite /get8 /init8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?; last first.
  + by rewrite ifF 1:/# initiE 1:/# initiE 1:/# /set16_direct initiE 1:/# /= ifF 1:/# /= initiE 1:/# initiE 1:/# /= /set32_direct initiE 1:/# /= ifF 1:/# initiE /#.  
  case (i - (_off + _dlt) - 6 = 0) => ?/=.
  + rewrite /ww /= ifT 1:/#; do 6!(rewrite ifF 1:/#); rewrite ifT 1:/# /=. 
    by congr;rewrite /(`>>`) /= bits8_div 1:// /truncateu8;congr;rewrite to_uint_shr //.
  rewrite ifF 1:/# initiE 1:/# /=initiE 1:/# /= /set16_direct initiE 1:/# /=.
  case (_off + (_dlt + 4) <= i < _off + (_dlt + 4) + 2) => ?.
  + congr;rewrite /(`>>`) /= bits8_div 1:/# /truncateu16;rewrite to_uint_shr //=.
    rewrite of_uintK /= /ww iotaredE (nth_map witness);1:smt(size_iota).
    rewrite nth_iota 1:/# /= bits8_div 1:/#.
    apply W8.to_uint_eq;rewrite of_uintK /=.
    have -> : 4294967296 = 65536*65536 by auto.
    rewrite -pow2_16 IntDiv.modz_pow2_div 1:/# -divz_mulp 1://;1:smt(expr_gt0).
    rewrite -!(Ring.IntID.exprD_nneg) //=;1:smt().
    rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

  + congr;rewrite initiE 1:/# initiE 1:/# /set32_direct initiE 1:/# /= ifT 1:/#.
    rewrite /ww (nth_map witness) 1:/# iotaredE nth_iota 1:/# /=.
    apply W8.to_uint_eq;rewrite !bits8_div 1,2:/# to_uint_truncateu32 of_uintK /=.
    rewrite -pow2_32 IntDiv.modz_pow2_div 1:/#.
    rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

(* _len = 6 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 get8_set16_directE 1,2:/# /=.
  rewrite wordP => k kb; rewrite /get8 /init8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?; last first.
  + by rewrite ifF 1:/# initiE 1:/# /set32_direct initiE 1:/# /= ifF 1:/# /= initiE 1:/#.
  case (_off + (_dlt + 4) <= i < _off + (_dlt + 4) + 2) => ?/=.
  + congr;rewrite /(`>>`) /= bits8_div 1:/# /truncateu16;rewrite to_uint_shr //=.
    rewrite of_uintK /= /ww iotaredE (nth_map witness);1:smt(size_iota).
    rewrite nth_iota 1:/# /= bits8_div 1:/#.
    apply W8.to_uint_eq;rewrite of_uintK /=.
    have -> : 4294967296 = 65536*65536 by auto.
    rewrite -pow2_16 IntDiv.modz_pow2_div 1:/# -divz_mulp 1://;1:smt(expr_gt0).
    rewrite -!(Ring.IntID.exprD_nneg) //=;1:smt().
    rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

  + congr;rewrite initiE 1:/# /set32_direct initiE 1:/# /= ifT 1:/#.
    rewrite /ww (nth_map witness) 1:/# iotaredE nth_iota 1:/# /=.
    apply W8.to_uint_eq;rewrite !bits8_div 1,2:/# to_uint_truncateu32 of_uintK /=.
    rewrite -pow2_32 IntDiv.modz_pow2_div 1:/#.
    rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

(* _len = 5 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 setE /get8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?;last first.
  +  by rewrite ifF 1:/# initiE 1:/# /set32_direct initiE 1:/# /= initiE 1:/# /= ifF 1:/# initiE /#.
  case (i - (_off + _dlt) - 4 = 0) => ?/=.
  + rewrite /ww /= ifT 1:/#; do 4!(rewrite ifF 1:/#); rewrite ifT 1:/# /=.
    by rewrite /(`>>`) /= bits8_div 1:// /truncateu8;congr;rewrite to_uint_shr //.
  rewrite ifF 1:/#.
  
  rewrite initiE 1:/# /set32_direct initiE 1:/# /= initiE 1:/# /= ifT 1:/#.
  rewrite /ww (nth_map witness) 1:/# iotaredE nth_iota 1:/# /=.
  apply W8.to_uint_eq;rewrite !bits8_div 1,2:/# to_uint_truncateu32 of_uintK /=.
  rewrite -pow2_32 IntDiv.modz_pow2_div 1:/#.
  by rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

(* _len = 4 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 get8_set32_directE 1,2:/# /=.
  rewrite wordP => k kb; rewrite /get8 /init8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?; last by smt().
  rewrite ifT 1:/#.
  case (_off + (_dlt + 4) <= i < _off + (_dlt + 4) + 2) => ?/=.
  + congr;rewrite bits8_div 1:/# /truncateu32.
    rewrite of_uintK /= /ww iotaredE (nth_map witness);1:smt(size_iota).
    rewrite nth_iota 1:/# /= bits8_div 1:/#.
    by apply W8.to_uint_eq; rewrite of_uintK /= !(modz_small _ 4294967296);1:by smt(W32.to_uint_cmp).

  + congr;rewrite bits8_div 1:/# /truncateu32.
    rewrite of_uintK /= /ww iotaredE (nth_map witness);1:smt(size_iota).
    rewrite nth_iota 1:/# /= bits8_div 1:/#.
    apply W8.to_uint_eq; rewrite of_uintK /=.
    rewrite -pow2_32 IntDiv.modz_pow2_div 1:/#.
    by rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

(* _len = 3 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 setE /get8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?;last first.
  +   rewrite ifF 1:/# initiE 1:/# /set16_direct initiE 1:/# /= initiE 1:/# /= ifF 1:/# initiE /#.
  case (i - (_off + _dlt) - 2 = 0) => ?/=.
  + rewrite /ww /= ifT 1:/#; do 2!(rewrite ifF 1:/#); rewrite ifT 1:/# /=.
    by rewrite /(`>>`) /= bits8_div 1:// /truncateu8;congr;rewrite to_uint_shr //.
  rewrite ifF 1:/#.

  + rewrite initiE 1:/# /set16_direct initiE 1:/# /= initiE 1:/# /= ifT 1:/#.
    rewrite /ww (nth_map witness) 1:/# iotaredE nth_iota 1:/# /=.
    apply W8.to_uint_eq;rewrite !bits8_div 1,2:/# to_uint_truncateu16 of_uintK /=.
    rewrite -pow2_16 IntDiv.modz_pow2_div 1:/#.
    by rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

 (* _len = 2 *) 
+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 get8_set16_directE 1,2:/# /=.
  rewrite wordP => k kb; rewrite /get8 /init8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?; last by smt().
  rewrite ifT 1:/#.
  congr;rewrite bits8_div 1:/# /truncateu16.
  rewrite of_uintK /= /ww iotaredE (nth_map witness);1:smt(size_iota).
  rewrite nth_iota 1:/# /= bits8_div 1:/#.
  apply W8.to_uint_eq; rewrite of_uintK /= -pow2_16 IntDiv.modz_pow2_div 1:/#.
  by rewrite -pow2_8 modz_mod_pow2 /min ifF (: `|8| = 8);by smt( normr_idP).

(* len = 1 *)

+apply A.tP => i ib; rewrite initiE 1:/# /= /fill  initiE 1:/# /= /init8 setE /get8 initiE 1:/# /=.
  case (_off + _dlt <= i < _off + _dlt + ll) => ?;last by rewrite ifF 1:/# initiE 1:/#. 
  case (i - (_off + _dlt) = 0) => ?/=; last by smt().
  rewrite /ww /= ifT 1:/#;  rewrite ifT 1:/# /=.
  by rewrite /(`>>`) /= bits8_div 1:// /truncateu8 //. 

qed.

phoare awrite_subu64_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu64
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 8 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W8u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8
 ] = 1%r.
proof.
by conseq awrite_subu64_ll (awrite_subu64_h _buf _off _dlt _len _w).
qed.

lemma awrite_subu128_ll: islossless M(P).__awrite_subu128
 by islossless.

lemma truncateu64_bits8_low (_w : W128.t) i :
     0 <= i < 8 =>
        (truncateu64 _w) \bits8 i = _w \bits8 i.
move => ib.
rewrite /truncateu64 /= W8u8.of_int_bits8_div //=.
apply W8.to_uint_eq => /=.
by have -> /=:= W16u8.bits8_div _w i _;1:smt().
qed.

lemma truncateu64_bits8_high (_w : W128.t) i :
     0 <= i < 8 =>
       truncateu64 (VPUNPCKH_2u64 _w _w) \bits8 i = _w \bits8 (i+8).
move => ib.
rewrite /VPUNPCKH_2u64 /interleave_gen /get_hi_2u64 /=.
have -> : truncateu64 (pack2 [_w \bits64 1; _w \bits64 1]) = _w \bits64 1.
+ have -> : truncateu64 (pack2 [_w \bits64 1; _w \bits64 1]) =
      (unpack64 (pack2 [_w \bits64 1; _w \bits64 1])).[0]; last by rewrite pack2K get_of_list //=.
  apply W8u8.allP; rewrite allP => x;rewrite iotaredE mem_iota /= => xb.
  rewrite truncateu64_bits8_low 1:/#.
  by rewrite bits8_W2u64_red 1:/# get_of_list 1:/# /= /#.
by rewrite W128_bits64_bits8 // /#.
qed.
 
hoare awrite_subu128_h _buf _off _dlt _len _w:
 M(P).__awrite_subu128
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 16 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W16u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16.
proof.
proc => /=.
  case (lEN <= 0).
  + rcondf 1; 1: by auto => /#.
    auto => /> &hr *;have ->/= : (min (max 0 _len) 16) = 0 by smt().
    rewrite tP => k kb;rewrite /fill initiE //= /#.

  rcondt  1; 1: by auto => /#.

  case (16 <= lEN).
  + rcondt 1; 1: by auto.
    auto => /> *;do split; 2.. :smt().
    rewrite tP => k kb;rewrite /fill !initiE //=.
    rewrite get8_set128_directE 1,2:/#.
    case (_off + _dlt <= k < _off + _dlt + 16) => ?; first by smt().
    rewrite /get8 initiE /#.

  rcondf 1;1: by auto.
  case (8<=lEN); last first.
  + rcondf 1; 1: by auto.
    wp; ecall (awrite_subu64_h _buf _off _dlt _len t64).
    auto => /> *; do split;1:smt().
    move => ? /= [r1 r2 r3] />;do split; 2..:smt().
    rewrite tP => k kb;rewrite /fill !initiE //=.
    case ( _off + _dlt <= k < _off + _dlt + min (max 0 _len) 8) => ?; last by smt().
    have -> /= : _off + _dlt <= k < _off + _dlt + min (max 0 _len) 16 = true by smt().
    by smt(truncateu64_bits8_low).

  rcondt 1;1: by auto.
  wp; ecall (awrite_subu64_h
         (A.init (get8 (set64_direct (WA.init8 (fun (i : int) => _buf.[i])) (_off + _dlt) (MOVV_64 (truncateu64 _w))))) _off (_dlt+8) (_len-8) t64).
  auto => /> *; do split;1,2:by smt().
  move => ?? [r1 r2 r3] />;do split; 2..:smt().
    rewrite tP => k kb;rewrite /fill !initiE //=.
    case (_off + (_dlt + 8) <= k < _off + (_dlt + 8) + min (max 0 (_len - 8)) 8) => ?; 
     1: by smt(truncateu64_bits8_high).
     rewrite initiE 1:/# get8_set64_directE 1,2:/#.
   case (_off + _dlt <= k < _off + _dlt + 8) => ?; 1: smt(truncateu64_bits8_low).
    have -> /= : _off + _dlt <= k < _off + _dlt + min (max 0 _len) 16 = false by smt().
    rewrite /get8 initiE /#.
qed.

phoare awrite_subu128_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu128
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 16 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W16u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16
 ] = 1%r.
proof.
by conseq awrite_subu128_ll (awrite_subu128_h _buf _off _dlt _len _w).
qed.

lemma awrite_subu256_ll: islossless M(P).__awrite_subu256
 by islossless.

lemma truncateu128_bits8_low (_w : W256.t) i :
     0 <= i <  16 =>
        (truncateu128 _w) \bits8 i = _w \bits8 i.
move => ib.
rewrite /truncateu128 /= W16u8.of_int_bits8_div //=.
apply W8.to_uint_eq => /=.
by have -> /=:= W32u8.bits8_div _w i _;1:smt().
qed.

    
lemma truncateu128_bits8_high (_w : W256.t) i :
     0 <= i < 16 =>
       VEXTRACTI128 _w W8.one  \bits8 i = _w \bits8 (i+16).
move => ib.
rewrite /VEXTRACTI128 /= nth_one /= /b2i /= W256_bits128_bits8 // /#.
qed.
 
hoare awrite_subu256_h _buf _off _dlt _len _w:
 M(P).__awrite_subu256
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 32 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W32u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 32) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 32
  /\ res.`3 = _len - min (max 0 _len) 32.
proof.
proc. 
  case (lEN <= 0).
  + rcondf 1; 1: by auto => /#.
    auto => /> &hr *;have ->/= : (min (max 0 _len) 32) = 0 by smt().
    rewrite tP => k kb;rewrite /fill initiE //= /#.

  rcondt  1; 1: by auto => /#.

  case (32 <= lEN).
  + rcondt 1; 1: by auto.
    auto => /> *;do split; 2.. :smt().
    rewrite tP => k kb;rewrite /fill !initiE //=.
    rewrite get8_set256_directE 1,2:/#.
    case (_off + _dlt <= k < _off + _dlt + 32) => ?; first by smt().
    rewrite /get8 initiE /#.

  rcondf 1;1: by auto.
  sp 1;case (16<=lEN); last first.
  + rcondf 1; 1: by auto.
    wp; ecall (awrite_subu128_h _buf _off _dlt _len t128).
    auto => /> *; do split;1:smt().
    move => ? /= [r1 r2 r3] />;do split; 2..:smt().
    rewrite tP => k kb;rewrite /fill !initiE 1..2:/# /=.
    case ( _off + _dlt <= k < _off + _dlt + min (max 0 _len) 16) => ?; last by smt().
    have -> /= : _off + _dlt <= k < _off + _dlt + min (max 0 _len) 32 = true by smt().
    by smt(truncateu128_bits8_low).

  rcondt 1;1: by auto.
  wp; ecall (awrite_subu128_h
         (A.init (get8 (set128_direct (WA.init8 (fun (i : int) => _buf.[i])) (_off + _dlt) (truncateu128 _w)))) _off (_dlt+16) (_len-16) (VEXTRACTI128 _w W8.one)).
  auto => /> *; do split;1,2:by smt().
  move => ?? [r1 r2 r3] />;do split; 2..:smt().
    rewrite tP => k kb;rewrite /fill !initiE 1,2:/# /=.
    case (_off + (_dlt + 16) <= k < _off + (_dlt + 16) + min (max 0 (_len - 16)) 16) => ?; 
     1: by smt(truncateu128_bits8_high).
     rewrite initiE 1:/# get8_set128_directE 1,2:/#.
   case (_off + _dlt <= k < _off + _dlt + 16) => ?; 1: smt(truncateu128_bits8_low).
    have -> /= :_off + _dlt <= k < _off + _dlt + min (max 0 _len) 32 = false by smt().
    rewrite /get8 initiE /#.
qed.

phoare awrite_subu256_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu256
 : w = _w /\ buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\
 0 <= _off + _dlt /\ _off + _dlt + min (max 0 _len) 32 <= aSIZE 
 ==> res.`1 = A.fill (fun i => nth W8.zero (W32u8.to_list _w) (i-(_off + _dlt))) (_off + _dlt) (min (max 0 _len) 32) _buf
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

(*
addstate_array_avx2
*)
lemma addstate_array_avx2_ll: islossless M(P).__addstate_array_avx2
 by islossless.

op sll_256 (w1 w2 : W256.t) : W256.t = w1 `<<<` to_uint w2.

bind op [W256.t] sll_256 "shl".
realize bvshlP.
rewrite /sll_256 => bv1 bv2.
by rewrite W256.to_uint_shl; 1: by smt(W256.to_uint_cmp).
qed.

clone import PolyArray as Array53 with
        op size = 53.

bind array Array53."_.[_]" Array53."_.[_<-_]" Array53.to_list Array53.of_list Array53.t 53.
realize tolistP by done.
realize get_setP by smt(Array53.get_setE). 
realize eqP by smt(Array53.tP).
realize get_out by smt(Array53.get_out).

clone import PolyArray as Array28 with
        op size = 28.

bind array Array28."_.[_]" Array28."_.[_<-_]" Array28.to_list Array28.of_list Array28.t 28.
realize tolistP by done.
realize get_setP by smt(Array28.get_setE). 
realize eqP by smt(Array28.tP).
realize get_out by smt(Array28.get_out).

bind op [W64.t & W128.t] W2u64.zeroextu128 "zextend".
realize bvzextendP.
move => bv; rewrite /zeroextu128 /= of_uintK /= modz_small 2://.
apply bound_abs; smt(W64.to_uint_cmp pow2_64).
qed.

bind op [W128.t & W256.t] W2u128.zeroextu256 "zextend".
realize bvzextendP.
move => bv; rewrite /zeroextu256 /= of_uintK /= modz_small 2://.
apply bound_abs; smt(W128.to_uint_cmp pow2_128).
qed.

lemma merge_words128 (t0 t1 : W128.t) : W256.of_int (to_uint t0 %% W128.modulus + W128.modulus * to_uint t1) =
  zeroextu256 t0 `|` sll_256 (zeroextu256 t1) (W256.of_int 128).
proof.
rewrite to_uint_eq to_uint_orw_disjoint;last first.
+ rewrite W256.of_uintK modz_small /=;1:smt(W128.to_uint_cmp pow2_128).
  rewrite  /sll_256 to_uint_shl //= !to_uint_zeroextu256.
  congr;smt(modz_small W128.to_uint_cmp pow2_128).
rewrite /sll_256 wordP => i ib.
rewrite andE map2iE 1:/# /=.
rewrite !zeroextu256_bit;smt(get_out).
qed.


op init_28_64(f :  int -> W64.t) : W64.t Array28.t = Array28.init f.

bind op [W64.t & Array28.t] init_28_64 "ainit".
realize bvainitP.
proof.
rewrite /init_28_64 => f.
rewrite  BVA_Top_KeccakArrayAvx2_Array28_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array28.initE).
qed.

lemma w4256w2bits(w : W256.t) : w2bits w = flatten (map W64.w2bits (to_list (unpack64 w))).
proof.
apply (eq_from_nth false).
+ rewrite size_w2bits (size_flatten' 64).
  + move => x;rewrite mapP => H; elim H =>xx;smt(W64.size_w2bits).
    by rewrite size_map size_to_list.
move => i; rewrite size_w2bits => ib.
rewrite get_w2bits (nth_flatten false 64).
+ rewrite allP => x;rewrite mapP => H;elim H => x0 /=;smt(W64.size_w2bits).
rewrite (nth_map witness);1: by  rewrite size_to_list /= /#.
rewrite get_w2bits /= unpack64E /to_list nth_mkseq 1:/# /= initiE 1:/# bits64E initiE 1:/# /= /#.
qed.

bind circuit VPINSR_2u64 "VPINSR_2u64".

import Avx2_extra Bindings.

op F2(inp : W64.t Array53.t ) : W256.t Array7.t =
   stavx2_from_st25 (addstate (stavx2_to_st25
       (init_7_256 (fun ii => u256_pack4 inp.[4*ii+0] inp.[4*ii+1] inp.[4*ii+2] inp.[4*ii+3])))
       (init_25_64 (fun ii => inp.[28+ii]))).

op Pre = fun (x : W64.t Array53.t) =>  x.[0] = x.[1] /\ x.[0] = x.[2] /\ x.[0] = x.[3].



lemma  chunkify_chunk (n : int) (l : 'a list) :
        n %| size l => JWordList.chunkify n l = chunk n l.
rewrite /chunkify /chunk => ?;do congr => /#.
qed.

op sizes(i : int) = nth 0 [8;32;8;32;8;32;8;32;8;32] i.
op asizes(i : int) = nth 0 [0;8;40;48;80;88;120;128;160;168;200] i.
op deltai(_len : int, i : int) = (min (max 0 _len) (asizes i)).
op leni(_len : int, i : int) = _len - deltai _len i.
op traili(_len : int, _tb : int, i : int) = if all (fun k => sizes (k-1) <= leni _len (k-1)) (iotared 0 (i+1)) then _tb else 0.
op theis(i : int) =  nth 0 [0;1;1;1;1;2;3;3;3;3;4;5;5;5;5;6;7;7;7;7;8;9;9;9;9] i.
op theos(i : int) =  nth 0 [0;0;1;2;3;0;0;1;2;3;0;0;1;2;3;0;0;1;2;3;0;0;1;2;3] i.

lemma bytes2_state_commute(_buf : W8.t A.t, _off _len _tb : int, idx : int):
        0 <= idx < 25 =>
        0 <= _len <= 200 - b2i (_tb<>0) =>
       0<= _off =>
       _off + _len <= aSIZE =>
       0 <= _tb < 256 =>
(bytes2state (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else [])).[idx] =
(bytes2state (sub _buf _off (leni _len (theis idx) + deltai _len (theis idx)) ++ if traili _len _tb (theis idx) <> 0 then [W8.of_int (traili _len _tb (theis idx))] else []))
 .[deltai _len (theis idx) %/ 8 + (theos idx) + b2i (! 8 %| deltai _len (theis idx))].
proof.
move => *.
rewrite /bytes2state !get_of_list 1,2:/#.
have  : all (fun idx => nth W64.zero (w64L_from_bytes (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else [])) idx =
nth W64.zero
  (w64L_from_bytes
     (sub _buf _off (leni _len (theis idx) + deltai _len (theis idx)) ++
      if traili _len _tb (theis idx) <> 0 then [W8.of_int (traili _len _tb (theis idx))] else []))
  (deltai _len (theis idx) %/ 8 + theos idx + b2i (! 8 %| deltai _len (theis idx)))) (iota_ 0 25);
    last by rewrite allP => ?; smt( mem_iota).
pose xtra := if _tb <> 0 then [W8.of_int _tb] else [].
rewrite -iotaredE /=; do split;do (simplify theis theos traili deltai leni asizes sizes min max).
+ rewrite /w64L_from_bytes.
   case (0 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (1 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (2 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (3 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (4 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (5 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (6 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (7 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (8 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (9 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (10 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (11 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (12 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (13 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (14 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (15 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (16 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (17 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (18 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (19 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (20 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (21 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (22 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (23 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
+ rewrite /w64L_from_bytes.
   case (24 < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
   + rewrite !(nth_map []) /=;
     1,2: by rewrite size_chunkify 1:/# /= size_cat size_sub  /= /#.
     by smt().
   + rewrite !(nth_default) /=;
      1,2: rewrite size_map size_chunkify 1:/# /= size_cat size_sub  /=  /#.
     by smt().
qed.

hoare addstate_array_avx2_h _st _buf _off _len _tb:
 M(P).__addstate_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb /\ stavx2INV _st
   /\ 0 <= _len <= 200 - b2i (_tb<>0) 
   /\ 0<= offset /\ offset + _len <= aSIZE /\ 0 <= _tb < 256
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_avx2 _st l
     /\ res.`2 = _off + _len.
proof.
proc => /=.
case (32+8 < _len). 
+ rcondt 8. 
  + wp; call (aread_subu256_h _buf _off (deltai _len 1) (leni _len 1) (traili _len _tb 1)).
    wp;call (aread_subu64_h _buf _off (deltai _len 0) (leni _len 0) (traili _len _tb 0)).
    +  auto => /> *;do simplify traili;do split => />;smt(). 
   inline 22.
   swap 21 -3; swap 15 3; swap 12 5; swap 9 7; swap 7 13; swap 5 14; swap [3..4] 9.
   sp;seq 10 : (offset = _off /\ dELTA = _len /\ st = _st /\ stavx2INV _st /\
                0 <= _len <= 200 - b2i (_tb <> 0) /\ 32 + 8 < _len /\
                    bytes2state (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []) =
                    Array25.of_list W64.zero
                       (map W64.bits2w (chunk 64 (flatten [w2bits t64_1; w2bits r1;
                                                      w2bits t64_2; w2bits r3;
                                                      w2bits t64_3; w2bits r4;
                                                      w2bits t64_4; w2bits r5;
                                                      w2bits t64_5; w2bits r6])))).
   + call (aread_subu256_h _buf _off (deltai _len 9) (leni _len 9) (traili _len _tb 9)).
     call (aread_subu64_h _buf _off  (deltai _len 8) (leni _len 8) (traili _len _tb 8)).
     call (aread_subu256_h _buf _off (deltai _len 7) (leni _len 7) (traili _len _tb 7)).
     call (aread_subu64_h _buf _off  (deltai _len 6) (leni _len 6) (traili _len _tb 6)).
     call (aread_subu256_h _buf _off (deltai _len 5) (leni _len 5) (traili _len _tb 5)).
     call (aread_subu64_h _buf _off  (deltai _len 4) (leni _len 4) (traili _len _tb 4)).
     call (aread_subu256_h _buf _off (deltai _len 3) (leni _len 3) (traili _len _tb 3)).
     call (aread_subu64_h _buf _off  (deltai _len 2) (leni _len 2) (traili _len _tb 2)).
     call (aread_subu256_h _buf _off (deltai _len 1) (leni _len 1) (traili _len _tb 1)).
     call (aread_subu64_h _buf _off  (deltai _len 0) (leni _len 0) (traili _len _tb 0)).
     auto => />.
     move => *;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r0??? /=H1;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r1??? /=H2;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r2??? /=H3;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r3??? /=H4;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r4??? /=H5;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r5??? /=H6;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r6??? /=H7;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r7??? /=H8;split; 1: by  do (simplify traili deltai leni asizes sizes); do split; smt().
     move => ???????r8??? /=H9;split; 1: by  do (simplify traili deltai leni asizes sizes); do split; smt().
     move => ???????r9??? /=H10.
     split;1: by smt().
     
     have Hr0 := aread_subu64_contract  _buf _off (deltai _len 0) (leni _len 0) (traili _len _tb 0) r0.`1 r0.`2 r0.`3 r0.`4 _ _;1,2: by rewrite ?H1; do (simplify traili deltai leni asizes sizes);smt(). 
     have Hr1 := aread_subu256_contract _buf _off (deltai _len 1) (leni _len 1) (traili _len _tb 1) r1.`1 r1.`2 r1.`3 r1.`4 _ _;1,2: by  by rewrite ?H2; do (simplify traili deltai leni asizes sizes);smt().
     have Hr2 := aread_subu64_contract  _buf _off (deltai _len 2) (leni _len 2) (traili _len _tb 2) r2.`1 r2.`2 r2.`3 r2.`4 _ _;1,2: by by rewrite ?H3; do (simplify traili deltai leni asizes sizes);smt(). 
     have Hr3 := aread_subu256_contract _buf _off (deltai _len 3) (leni _len 3) (traili _len _tb 3) r3.`1 r3.`2 r3.`3 r3.`4 _ _;1,2: by rewrite ?H4; do split; do (simplify traili deltai leni asizes sizes);smt().
     have Hr4 := aread_subu64_contract  _buf _off (deltai _len 4) (leni _len 4) (traili _len _tb 4) r4.`1 r4.`2 r4.`3 r4.`4 _ _;1,2: by rewrite ?H5; do (simplify traili deltai leni asizes sizes);smt(). 
     have Hr5 := aread_subu256_contract _buf _off (deltai _len 5) (leni _len 5) (traili _len _tb 5) r5.`1 r5.`2 r5.`3 r5.`4 _ _;1,2: by rewrite ?H6; do split;do (simplify traili deltai leni asizes sizes);smt().
     have Hr6 := aread_subu64_contract  _buf _off (deltai _len 6) (leni _len 6) (traili _len _tb 6) r6.`1 r6.`2 r6.`3 r6.`4 _ _;1,2: by rewrite ?H7;  do split;do (simplify traili deltai leni asizes sizes);smt().
     have Hr7 := aread_subu256_contract _buf _off (deltai _len 7) (leni _len 7) (traili _len _tb 7) r7.`1 r7.`2 r7.`3 r7.`4 _ _;1,2: by rewrite ?H8; do (simplify traili deltai leni asizes sizes);smt().
     have Hr8 := aread_subu64_contract  _buf _off (deltai _len 8) (leni _len 8) (traili _len _tb 8) r8.`1 r8.`2 r8.`3 r8.`4 _ _;1,2: by rewrite ?H9; do (simplify traili deltai leni asizes sizes);smt(). 
     have Hr9 := aread_subu256_contract _buf _off (deltai _len 9) (leni _len 9) (traili _len _tb 9) r9.`1 r9.`2 r9.`3 r9.`4 _ _;1,2: by rewrite ?H10; do (simplify traili deltai leni asizes sizes);smt().

     rewrite !w4256w2bits /to_list /mkseq -iotaredE /=.
     rewrite Hr0 !Hr1 // Hr2 !Hr3 // Hr4 !Hr5 // Hr6 !Hr7 // Hr8 !Hr9 //.
     rewrite !flatten_cons /= !flatten_nil /=.
     do 30!(rewrite chunk_cat;1:by smt(W64.size_w2bits size_cat)).
     rewrite !(chunk0 _ []);1:by auto.
     rewrite !chunk_size 1..50:/# /=.
     have <- := (Array25.to_listK W64.zero (bytes2state (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []))).
     apply Array25.tP => i ib.
     rewrite get_of_list 1:/#.
     rewrite get_of_list 1:/#.
     congr.
     rewrite /to_list /mkseq -iotaredE /=.
     do split => /=;1..6: by smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 6 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 7 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 8 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 9 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 10 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().  
     by have -> := bytes2_state_commute _buf _off _len _tb 11 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 12 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 13 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 14 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 15 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 16 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 17 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 18 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 19 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 20 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 21 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 22 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 23 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 24 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
 
          
     + wp 20; conseq (: _ ==> st0 = addstate_avx2 _st (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else [])); 1: by auto => />.
     proc change 7 : (zeroextu256 t128_0 `|` sll_256 (W2u128.zeroextu256 t128_1) (W256.of_int 128)); 1: by move => *; apply merge_words128.
     exlim t64_1, r1, t64_2, r3, t64_3, r4, t64_4, r5, t64_5, r6 => _w1 _w2 _w3 _w4 _w5 _w6 _w7 _w8 _w9 _w10.
     inline *;
     bdep 3392 1792 [_st;_w1;_w2;_w3;_w4;_w5;_w6;_w7;_w8;_w9;_w10]
                    [st;t64_1;r1;t64_2;r3;t64_3;r4;t64_4;r5;t64_5;r6]
                    [st0]
                    F2 Pre.
     + move => />  Hst0 Hst1 Hst2  *; rewrite allP /Pre /= => x;rewrite mapP => H;elim H =>xx /=.
       move => [Hxx Hx]; have Hsti : forall i, 0 <= i < 4 => x.[i] = u256_bits64 _st.[0] i; last by  rewrite !Hsti //= Hst0 Hst1 Hst2 //.
       move => i ib.
       rewrite Hx; rewrite get_of_list 1:/# /=.
       move : Hxx; rewrite chunk_size 1:/# /=.
       + rewrite size_flatten /= (size_flatten' 256);1:by smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list => />.
       rewrite flatten_cons => ->; rewrite (nth_map []).
       + rewrite size_chunk 1:/#.
       + rewrite size_cat /= (size_flatten' 256);1:by smt(mapP W256.size_w2bits).
         rewrite size_map size_to_list size_flatten.
         by rewrite /sumz /= /#.
       rewrite chunk_cat;1: by rewrite (size_flatten' 256);smt(mapP W256.size_w2bits).
       rewrite nth_cat ifT.
       + rewrite size_chunk 1:/#.
         rewrite (size_flatten' 256);1:smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list /#.
       rewrite nth_chunk 1,2:/#.
       + rewrite (size_flatten' 256);1:smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list /#.
       apply W64.wordP => k kb.
       rewrite get_bits2w // nth_take 1,2:/# nth_drop 1,2:/#.
       rewrite (nth_flatten false 256);1: by rewrite allP => ?;rewrite mapP;smt(W256.size_w2bits).
       rewrite (nth_map witness);1:by rewrite size_to_list /#.
       rewrite (nth_map witness) /=;1:by rewrite size_iota /#.
       rewrite nth_iota 1:/# initiE 1:/# /#.

     + move => &hr /> ?????? Hin stout.
       have Hs1 : size
       (flatten
     [   flatten (map W256.w2bits (to_list st{hr})); w2bits t64_1{hr}; w2bits r1{hr}; 
        w2bits t64_2{hr}; w2bits r3{hr}; w2bits t64_3{hr}; w2bits r4{hr}; 
        w2bits t64_4{hr}; w2bits r5{hr}; w2bits t64_5{hr}; w2bits r6{hr}]) = 3392.
       + rewrite size_flatten /= (size_flatten' 256);1: smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list => />.
       have Hs2 : size (flatten (map W256.w2bits (to_list stout))) = 1792.
       + rewrite  (size_flatten' 256);1: smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list => />.       
       have Hs3 : size (flatten (map W256.w2bits (to_list st{hr}))) = 1792.
       + rewrite  (size_flatten' 256);1: smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list => />.
       have Hs4 : size (chunk 64 (flatten
        [flatten (map W256.w2bits (to_list st{hr})); w2bits t64_1{hr}; 
           w2bits r1{hr}; w2bits t64_2{hr}; w2bits r3{hr}; w2bits t64_3{hr}; 
           w2bits r4{hr}; w2bits t64_4{hr}; w2bits r5{hr}; w2bits t64_5{hr}; 
           w2bits r6{hr}])) = 53.
       + rewrite size_chunk 1:/# size_flatten /=  (size_flatten' 256);1: smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list /sumz=> />.
       

       rewrite chunk_size 1,2:/# -map_comp /(\o) /= flatten1 (chunk_size 1792) 1,2:/# /=.
       rewrite tP => Hout.
       rewrite tP => i ib.
       have := Hout i ib.
       pose aa := (F2 _).[i].
       rewrite initiE 1:/# /= (nth_map witness).
       + rewrite size_chunk 1:/# /= (size_flatten' 256);1:by smt(mapP W256.size_w2bits).
         by rewrite size_map size_to_list /= /#.
       rewrite flattenK 1:/#;1: by move => ?; rewrite mapP; smt(W256.size_w2bits).
       rewrite (nth_map witness);1:by smt(Array7.size_to_list).
       rewrite w2bitsK get_to_list => <-;rewrite /aa /F2 /addstate_avx2;do congr.
       + (* state matching *)
         rewrite tP => k kb;rewrite initiE 1:/# /= /u256_pack4 /Bindings.concat_2u128 /concat_2u64!pack2E !initiE 1..4:/# wordP => j jb.
         rewrite !initiE 1:/# /= get_of_list 1:/# /=.
         case (j %/64 = 0) => ?.
         + rewrite ifT 1:/# initiE 1:/# /= get_of_list 1:/# /= ifT 1:/# (nth_map []) 1:/#.
           rewrite get_bits2w 1:/# flatten_cons chunk_cat;1: by smt(mapP Array7.size_to_list).
           rewrite nth_cat ifT;1: by smt(size_chunk).
           rewrite nth_chunk 1..3:/# nth_take 1,2:/# nth_drop 1,2:/#.
           rewrite (nth_flatten _ 256);1: by rewrite allP => ? /=;rewrite mapP; smt( W256.size_w2bits).
           by rewrite (nth_map witness) /=;smt(Array7.size_to_list).
         case (j %/64 = 1) => ?.
         + rewrite ifT 1:/# initiE 1:/# /= get_of_list 1:/# /= ifF 1:/# (nth_map []) 1:/# ifT 1:/#.
           rewrite get_bits2w 1:/# flatten_cons chunk_cat;1: by smt(mapP Array7.size_to_list).
           rewrite nth_cat ifT;1: by smt(size_chunk).
           rewrite nth_chunk 1..3:/# nth_take 1,2:/# nth_drop 1,2:/#.
           rewrite (nth_flatten _ 256);1: by rewrite allP => ? /=;rewrite mapP; smt( W256.size_w2bits).
           by rewrite (nth_map witness) /=;smt(Array7.size_to_list).
         case (j %/64 = 2) => ?.
         + rewrite ifF 1:/# ifT 1:/# initiE 1:/# /= get_of_list 1:/# /= ifT 1:/# (nth_map []) 1:/#.
           rewrite get_bits2w 1:/# flatten_cons chunk_cat;1: by smt(mapP Array7.size_to_list).
           rewrite nth_cat ifT;1: by smt(size_chunk).
           rewrite nth_chunk 1..3:/# nth_take 1,2:/# nth_drop 1,2:/#.
           rewrite (nth_flatten _ 256);1: by rewrite allP => ? /=;rewrite mapP; smt( W256.size_w2bits).
           by rewrite (nth_map witness) /=;smt(Array7.size_to_list).
         case (j %/64 = 3) => ?.
         + rewrite ifF 1:/# ifT 1:/# initiE 1:/# /= get_of_list 1:/# /= ifF 1:/# (nth_map []) 1:/# ifT 1:/#.
           rewrite get_bits2w 1:/# flatten_cons chunk_cat;1: by smt(mapP Array7.size_to_list).
           rewrite nth_cat ifT;1: by smt(size_chunk).
           rewrite nth_chunk 1..3:/# nth_take 1,2:/# nth_drop 1,2:/#.
           rewrite (nth_flatten _ 256);1: by rewrite allP => ? /=;rewrite mapP; smt( W256.size_w2bits).
           by rewrite (nth_map witness) /=;smt(Array7.size_to_list).
         by smt(). 
     + (* read matching *) 
       rewrite Hin; rewrite tP => k kb.
       rewrite get_of_list 1:/# initiE 1:/# /= get_of_list 1:/# /= flatten_cons chunk_cat;1: by smt(mapP Array7.size_to_list).
       rewrite map_cat nth_cat ifF;1: smt(size_map size_chunk).
       rewrite size_map size_chunk 1:/# (size_flatten' 256);1:smt(mapP W256.size_w2bits).
       by rewrite size_map size_to_list /=.
         
+ rcondf 8.
  + wp; call (aread_subu256_h _buf _off (min (max 0 _len) 8) (_len - (min (max 0 _len) 8)) (if _len < 8 then 0 else _tb)).
    wp;call (aread_subu64_h _buf _off 0 _len _tb);auto => /> /#.
    swap 6 -3.
    sp;seq 2 : (offset = _off /\ dELTA = _len /\ st = _st /\ stavx2INV _st /\
                0 <= _len <= 200 - b2i (_tb <> 0) /\ (!32 + 8 < _len) /\
                    bytes2state (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []) =
                    Array25.of_list W64.zero
                       (map W64.bits2w (chunk 64 (flatten [w2bits t64_1; w2bits r1])))).
   + call (aread_subu256_h _buf _off (deltai _len 1) (leni _len 1) (traili _len _tb 1)).
     call (aread_subu64_h _buf _off  (deltai _len 0) (leni _len 0) (traili _len _tb 0)).
     auto => />.
     move => *;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r0??? /=H1;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     move => ???????r1??? /=H2;split; 1: by do (simplify traili deltai leni asizes sizes);smt().
     have Hr0 := aread_subu64_contract  _buf _off (deltai _len 0) (leni _len 0) (traili _len _tb 0) r0.`1 r0.`2 r0.`3 r0.`4 _ _;1,2: by rewrite ?H1; do (simplify traili deltai leni asizes sizes);smt(). 
     have Hr1 := aread_subu256_contract _buf _off (deltai _len 1) (leni _len 1) (traili _len _tb 1) r1.`1 r1.`2 r1.`3 r1.`4 _ _;1,2: by  by rewrite ?H2; do (simplify traili deltai leni asizes sizes);smt().

     rewrite !w4256w2bits /to_list /mkseq -iotaredE /=.
     rewrite Hr0 !Hr1 //.
     rewrite !flatten_cons /= !flatten_nil /=.
     do 6!(rewrite chunk_cat;1:by smt(W64.size_w2bits size_cat)).
     rewrite !(chunk0 _ []);1:by auto.
     rewrite !chunk_size 1..10:/# /=.
     have <- := (Array25.to_listK W64.zero (bytes2state (sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []))).
     apply Array25.tP => i ib.
     rewrite get_of_list 1:/#.
     rewrite get_of_list 1:/#.
     pose v2 := nth _ (_::_).
     pose xtra := if _tb <> 0 then [W8.of_int _tb] else [].
     case(i<5) => ?;last first.
     + rewrite /v2 (nth_default _ (_::_)) /= 1:/#.
       rewrite /to_list nth_mkseq 1:/# /= /bytes2state get_of_list 1:/# /w64L_from_bytes.
       case (i < (_len + size xtra) %/ 8 + b2i (! 8 %| (_len + size xtra))) => ?.
       + rewrite (nth_map []) /=.
         + rewrite  size_chunkify 1:/# size_cat size_sub /#. 
         rewrite pack8E /= wordP => k kb.
         rewrite initiE 1:/# /= get_of_list 1:/# /chunkify nth_mkseq /=.
         + rewrite size_cat size_sub /#.
         rewrite nth_take 1,2:/# nth_drop 1,2:/# nth_cat size_sub 1:/#.
         rewrite /xtra /=; case (8 * i + k %/ 8 < _len); first by smt().
         move => ?; case (_tb <> 0) => ?/=;2: smt().
         case (8 * i + k %/ 8 - _len = 0).
         (* Something is wrong here? *)
     (*   
     rewrite /to_list /mkseq -iotaredE /=. 
     do split => /=;1..6: by smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 6 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 7 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 8 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 9 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().
     by have -> := bytes2_state_commute _buf _off _len _tb 10 _ _ _ _ _;(simplify theis theos traili deltai leni asizes sizes);smt().  
     *)
  admit.

qed.

phoare addstate_array_avx2_ph _st _buf _off _len _tb:
 [ M(P).__addstate_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
   /\ 0 <= _len <= 200 - b2i (_tb<>0)
   /\ offset + _len <= aSIZE
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_avx2 _st l
     /\ res.`2 = _off + _len
 ] = 1%r.
proof.
by conseq addstate_array_avx2_ll (addstate_array_avx2_h _st _buf _off _len _tb).
qed.

phoare absorb_array_avx2_ll:
 [ M(P).__absorb_array_avx2
 : 0 < rATE8 <= 200 /\ 0 <= lEN /\ 0<= offset /\ offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
proc.
have L: forall x, x <= aSIZE => x < W64.modulus.
 by move=> *; apply (ler_lt_trans aSIZE) => //; exact aSIZE_u64.
seq 3: (0 < rATE8 <=200 /\ iTERS < W64.modulus) => //=.
  sp; if => //=.
   while (iTERS=lEN %/ rATE8 /\ i <= iTERS < W64.modulus) (iTERS-i).
    move=> z; wp.
    call keccakf1600_avx2_ll.
    call addstate_array_avx2_ll.
    auto => /> &m ?? /#. 
   auto => /> &m *;split;smt(pow2_64).
  auto => /> /#.
 by islossless.
hoare => /=.
sp; if => //=.
 while #post.
 wp; call (:true) => //=.
 call (:true) => //=.
 auto => /> &m *.
 by move: (L lEN{m}); smt(W64.to_uint_cmp).
by auto => /> /#.
qed.

hoare absorb_array_avx2_h _st _buf _off _len _r8 _tb:
 M(P).__absorb_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ 0 < rATE8 <= 200 /\ 0 <= lEN /\  offset + lEN <= aSIZE
 ==> res.`1 = stavx2_from_st25 (ABSORB1600 (W8.of_int _tb) _r8 (sub _buf _off _len))
  /\ res.`2 = _off + _len.
proof.
admit.
qed.

phoare absorb_array_avx2_ph _st _buf _off _len _r8 _tb:
 [ M(P).__absorb_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ 0 < rATE8 <= 200 /\ 0 <= lEN /\  0<= offset /\ offset + lEN <= aSIZE
 ==> res.`1 = stavx2_from_st25 (ABSORB1600 (W8.of_int _tb) _r8 (sub _buf _off _len))
  /\ res.`2 = _off + _len
 ] = 1%r.
proof.
by conseq absorb_array_avx2_ll (absorb_array_avx2_h _st _buf _off _len _r8 _tb).
qed.


(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ======================================
*)
op fillstate_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill 
   (fun i => l.[i-at]) at (size l) (stbytes st)).

op addstate_at (st: W64.t Array25.t) (at:int) (l: W8.t list) =
 stwords
  (WArray200.fill 
   (fun i => (stbytes st).[i] `^` l.[i-at]) at (size l) (stbytes st)).


phoare pstate_array_avx2_ll: 
 [ M(P).__pstate_array_avx2
 : 0 <= aT <= aT + lEN <= 200 - b2i (tRAILB<>0)
 /\ offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
proc => /=.
sp; if => //.
 if => //.
  rcondf 8; first by auto.
  by islossless.
 seq 1: #[/:]{~dELTA}pre => //.
   if => //; auto.
   by call aread_subu64_ll.
  sp; if => //.
   seq 3: true => //.
    elim* => _at0 _pst _t64 _at _len.
    admit.    
   by islossless.
  by islossless.
 hoare => /=; if => //; auto.
 by call (:true) => //.
if => //.
 seq 3: true => //.
  admit.
 by islossless.
by islossless.
qed.

hoare pstate_array_avx2_h _pst _at _buf _off _len _tb:
 M(P).__pstate_array_avx2
 : pst=_pst /\ aT=_at /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= _at <= _at + _len <= 200 - b2i (_tb<>0)
 /\ _off + _len <= aSIZE
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = fillpst_at _pst _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + _len.
admitted.

phoare pstate_array_avx2_ph _pst _at _buf _off _len _tb:
 [ M(P).__pstate_array_avx2
 : pst=_pst /\ aT=_at /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= _at <= _at + _len <= 200 - b2i (_tb<>0)
 /\ _off + _len <= aSIZE
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = fillpst_at _pst _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + _len
 ] = 1%r.
proof.
by conseq pstate_array_avx2_ll (pstate_array_avx2_h _pst _at _buf _off _len _tb).
qed.

(*
pabsorb_array_avx2
*)
phoare pabsorb_array_avx2_ll:
 [ M(P).__pabsorb_array_avx2
 : 0 <= aT < 200
 /\ 0 < rATE8 <= 200
 /\ offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
admitted.

hoare pabsorb_array_avx2_h _l _buf _off _len _r8 _tb:
 M(P).__pabsorb_array_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l pst st
 /\ 0 <= _len
 /\ _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ sub _buf _off _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l ++ sub _buf _off _len) res.`1 res.`3
          /\ res.`2 = (size _l + _len) %% _r8
          /\ res.`4 = _off + _len.
admitted.

phoare pabsorb_array_avx2_ph _l _buf _off _len _r8 _tb:
 [ M(P).__pabsorb_array_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l pst st
 /\ 0 <= _len
 /\ _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ sub _buf _off _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l ++ sub _buf _off _len) res.`1 res.`3
          /\ res.`2 = (size _l + _len) %% _r8
          /\ res.`4 = _off + _len
 ] = 1%r.
proof.
by conseq pabsorb_array_avx2_ll (pabsorb_array_avx2_h _l _buf _off _len _r8 _tb) => /> /#.
qed.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_array_avx2_ll: islossless M(P).__dumpstate_array_avx2
 by islossless.

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


lemma squeeze_array_avx2_ll: islossless M(P).__squeeze_array_avx2.
proof.
proc; sp; if=> //.
seq 1: true => //.
 if => //.
 while (0 < iTERS) (iTERS-i).
  move=> z.
  wp; call dumpstate_array_avx2_ll.
  call keccakf1600_avx2_ll.
  auto => /> &m /#. 
 auto => /> &m i ?H /#. 
if => //.
call  dumpstate_array_avx2_ll.
call keccakf1600_avx2_ll.
by auto.
qed.

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

end KeccakArrayAvx2.
