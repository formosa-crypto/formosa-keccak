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

require import Keccakf1600_avx2 Keccak1600_avx2 Keccak1600_imem_avx2.


op addstate_avx2 (st: W256.t Array7.t, l: W8.t list): W256.t Array7.t =
 stavx2_from_st25 (addstate (stavx2_to_st25 st) (bytes2state l)).


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
        }
        (buf, dELTA, lEN) <@ __awrite_subu128 (buf, offset, dELTA, lEN,
        t128);
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __addstate_array_avx2 (st:W256.t Array7.t, buf:W8.t A.t,
                              offset:W64.t, lEN:int, tRAILB:int) : W256.t Array7.t *
                                                                   W64.t = {
    var dELTA:int;
    var t64:W64.t;
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
    (dELTA, lEN, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
    lEN, tRAILB);
    t128_0 <- (zeroextu128 t64);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    st.[0] <- (st.[0] `^` r0);
    (dELTA, lEN, tRAILB, r1) <@ __aread_subu256 (buf, offset, dELTA, 
    lEN, tRAILB);
    st.[1] <- (st.[1] `^` r1);
    if ((0 < lEN)) {
      (dELTA, lEN, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_1 <- (zeroextu128 t64);
      (dELTA, lEN, tRAILB, r3) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_0 <- (zeroextu128 t64);
      (dELTA, lEN, tRAILB, r4) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_1 <- (VPINSR_2u64 t128_1 t64 (W8.of_int 1));
      (dELTA, lEN, tRAILB, r5) <@ __aread_subu256 (buf, offset, dELTA, 
      lEN, tRAILB);
      (dELTA, lEN, tRAILB, t64) <@ __aread_subu64 (buf, offset, dELTA, 
      lEN, tRAILB);
      t128_0 <- (VPINSR_2u64 t128_0 t64 (W8.of_int 1));
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
    offset <- (offset + (W64.of_int dELTA));
    return (st, offset);
  }
  proc __absorb_array_avx2 (st:W256.t Array7.t, buf:W8.t A.t,
                            offset:W64.t, lEN:int, rATE8:int, tRAILB:int) : 
  W256.t Array7.t * W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    aLL <- (lEN + ((tRAILB <> 0) ? 1 : 0));
    iTERS <- (lEN %/ rATE8);
    if ((0 < iTERS)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st, offset) <@ __addstate_array_avx2 (st, buf, offset, rATE8, 0);
        st <@ P.keccakf1600_avx2 (st);
        i <- (i + (W64.of_int 1));
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
                            offset:W64.t, lEN:int, tRAILB:int) : W64.t Array25.t *
                                                                 int * W64.t = {
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
          (W64.to_uint (offset + (W64.of_int dELTA))));
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
      offset <- (offset + (W64.of_int dELTA));
      dELTA <- 0;
      while ((at \ult (W64.of_int ((aT %/ 8) + (4 * (lEN %/ 32)))))) {
        t256 <-
        (get256_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint offset));
        offset <- (offset + (W64.of_int 32));
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
      (W64.to_uint (offset + (W64.of_int dELTA))));
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
      (W64.to_uint (offset + (W64.of_int dELTA))));
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
    offset <- (offset + (W64.of_int dELTA));
    return (pst, aLL, offset);
  }
  proc __pabsorb_array_avx2 (pst:W64.t Array25.t, aT:int, st:W256.t Array7.t,
                             buf:W8.t A.t, offset:W64.t, lEN:int,
                             rATE8:int, tRAILB:int) : W64.t Array25.t * int *
                                                      W256.t Array7.t * W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    var  _0:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (pst, aT, offset) <@ __pstate_array_avx2 (pst, aT, buf, offset, 
      lEN, tRAILB);
      if ((tRAILB <> 0)) {
        i <- (W64.of_int ((aT %/ 8) + 1));
        if ((aT <= (5 * 8))) {
          while ((i \ult (W64.of_int 5))) {
            pst.[(W64.to_uint i)] <- (W64.of_int 0);
            i <- (i + (W64.of_int 1));
          }
          st <@ P.addpst01_avx2 (st, pst);
          st <@ P.addratebit_avx2 (st, rATE8);
        } else {
          while ((i \ult (W64.of_int (rATE8 %/ 8)))) {
            pst.[(W64.to_uint i)] <- (W64.of_int 0);
            i <- (i + (W64.of_int 1));
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
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st, offset) <@ __addstate_array_avx2 (st, buf, offset, rATE8, 0);
        st <@ P.keccakf1600_avx2 (st);
        i <- (i + (W64.of_int 1));
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
  proc __dumpstate_array_avx2 (buf:W8.t A.t, offset:W64.t, lEN:int,
                               st:W256.t Array7.t) : W8.t A.t * W64.t = {
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
    offset <- (offset + (W64.of_int dELTA));
    return (buf, offset);
  }
  proc __squeeze_array_avx2 (buf:W8.t A.t, offset:W64.t, lEN:int,
                             st:W256.t Array7.t, rATE8:int) : W8.t A.t *
                                                              W256.t Array7.t = {
    var iTERS:int;
    var lO:int;
    var i:W64.t;
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- (W64.of_int 0);
        while ((i \ult (W64.of_int iTERS))) {
          st <@ P.keccakf1600_avx2 (st);
          (buf, offset) <@ __dumpstate_array_avx2 (buf, offset, rATE8, st);
          i <- (i + (W64.of_int 1));
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

(*
addstate_array_avx2
*)
lemma addstate_array_avx2_ll: islossless M(P).__addstate_array_avx2
 by islossless.

hoare addstate_array_avx2_h _st _buf _off _len _tb:
 M(P).__addstate_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
   /\ 0 <= _len <= 200 - b2i (_tb<>0)
   /\ to_uint offset + _len <= aSIZE
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_avx2 _st l
     /\ res.`2 = _off + (W64.of_int _len).
proof.
proc.
admit.
qed.

phoare addstate_array_avx2_ph _st _buf _off _len _tb:
 [ M(P).__addstate_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
   /\ 0 <= _len <= 200 - b2i (_tb<>0)
   /\ to_uint offset + _len <= aSIZE
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_avx2 _st l
     /\ res.`2 = _off + (W64.of_int _len)
 ] = 1%r.
proof.
by conseq addstate_array_avx2_ll (addstate_array_avx2_h _st _buf _off _len _tb).
qed.

phoare absorb_array_avx2_ll:
 [ M(P).__absorb_array_avx2
 : 0 < rATE8 <= 200 /\ 0 <= lEN /\ to_uint offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
proc.
have L: forall x, x <= aSIZE => x < W64.modulus.
 by move=> *; apply (ler_lt_trans aSIZE) => //; exact aSIZE_u64.
seq 3: (0 < rATE8 <=200 /\ iTERS < W64.modulus) => //=.
  sp; if => //=.
   while (iTERS=lEN %/ rATE8 /\ to_uint i <= iTERS < W64.modulus) (iTERS-to_uint i).
    move=> z; wp.
    call keccakf1600_avx2_ll.
    call addstate_array_avx2_ll.
    auto => /> &m ??; rewrite ultE of_uintK modz_small. 
     smt(W64.to_uint_cmp).
    by move => H; rewrite to_uintD_small /= /#. 
   auto => /> &m *.
   split. 
    by move: (L lEN{m}); smt(W64.to_uint_cmp).
   by move=> i *; rewrite ultE of_uintK modz_small; smt(W64.to_uint_cmp).
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
 /\ 0 < rATE8 <= 200 /\ 0 <= lEN /\ to_uint offset + lEN <= aSIZE
 ==> res.`1 = stavx2_from_st25 (ABSORB1600 (W8.of_int _tb) _r8 (sub _buf (to_uint _off) _len))
  /\ res.`2 = _off + W64.of_int _len.
proof.
admit.
qed.

phoare absorb_array_avx2_ph _st _buf _off _len _r8 _tb:
 [ M(P).__absorb_array_avx2
 : st=_st /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ 0 < rATE8 <= 200 /\ 0 <= lEN /\ to_uint offset + lEN <= aSIZE
 ==> res.`1 = stavx2_from_st25 (ABSORB1600 (W8.of_int _tb) _r8 (sub _buf (to_uint _off) _len))
  /\ res.`2 = _off + W64.of_int _len
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
 /\ to_uint offset + lEN <= aSIZE
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
 /\ to_uint _off + _len <= aSIZE
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = fillpst_at _pst _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + (W64.of_int _len).
admitted.

phoare pstate_array_avx2_ph _pst _at _buf _off _len _tb:
 [ M(P).__pstate_array_avx2
 : pst=_pst /\ aT=_at /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= _at <= _at + _len <= 200 - b2i (_tb<>0)
 /\ to_uint _off + _len <= aSIZE
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = fillpst_at _pst _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + (W64.of_int _len)
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
 /\ to_uint offset + lEN <= aSIZE
 ==> true
 ] = 1%r.
proof.
admitted.

hoare pabsorb_array_avx2_h _l _buf _off _len _r8 _tb:
 M(P).__pabsorb_array_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l pst st
 /\ 0 <= _len
 /\ to_uint _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ sub _buf (to_uint _off) _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l ++ sub _buf (to_uint _off) _len) res.`1 res.`3
          /\ res.`2 = (size _l + _len) %% _r8
          /\ res.`4 = _off + W64.of_int _len.
admitted.

phoare pabsorb_array_avx2_ph _l _buf _off _len _r8 _tb:
 [ M(P).__pabsorb_array_avx2
 : aT = size _l %% _r8 /\ buf=_buf /\ offset=_off /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l pst st
 /\ 0 <= _len
 /\ to_uint _off + _len <= aSIZE
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l ++ sub _buf (to_uint _off) _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l ++ sub _buf (to_uint _off) _len) res.`1 res.`3
          /\ res.`2 = (size _l + _len) %% _r8
          /\ res.`4 = _off + W64.of_int _len
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
 while (0 < iTERS) (iTERS-to_uint i).
  move=> z.
  wp; call dumpstate_array_avx2_ll.
  call keccakf1600_avx2_ll.
  auto => /> &m; rewrite ultE of_uintK => /= *.
  by rewrite to_uintD_small /= /#.
 auto => /> &m i ?H; rewrite ultE of_uintK /#.
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
