require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array3 Array5 Array6 Array7 Array24 Array25 Array26 Array101 WArray3
WArray32 WArray40 WArray160 WArray192 WArray200 WArray208 WArray224 WArray800
WArray808.

abbrev rOL8 =
((Array1.of_list witness)
[(W256.of_int
 13620818001941277694121380808605999856886653716761013959207994299728839901191
 )]
).

abbrev rOL56 =
((Array1.of_list witness)
[(W256.of_int
 10910488462195273559651782724632284871561478246514020268633800075540923875841
 )]
).

abbrev kECCAK_RHOTATES_RIGHT =
((Array6.of_list witness)
[(W256.of_int 144373339913893657577751063007562604548177214458152943091773);
(W256.of_int 232252764209307188274174373867837442080505530800860351692863);
(W256.of_int 156927543384667019098616994515559168111335794127330162507795);
(W256.of_int 351517697181654122777866749001917765472957616589092975280182);
(W256.of_int 276192476357013953622045746931053922384479139705868246843454);
(W256.of_int 313855086769334038206421612937983674734430261968315659321364)]).

abbrev kECCAK_RHOTATES_LEFT =
((Array6.of_list witness)
[(W256.of_int 257361171150853911329517531560668107745210100483895842570243);
(W256.of_int 169481746855440380633094220700393270212881784141188433969153);
(W256.of_int 244806967680080549808651600052671544182051520814718623154221);
(W256.of_int 50216813883093446129401845566312946820429698352955810381834);
(W256.of_int 125542034707733615285222847637176789908908175236180538818562);
(W256.of_int 87879424295413530700846981630247037558957052973733126340652)]).

abbrev kECCAK1600_RC =
((Array24.of_list witness)
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

module M = {
  proc __ANDN_64 (a:W64.t, b:W64.t) : W64.t = {
    var t:W64.t;
    t <- ((invw a) `&` b);
    return t;
  }
  proc keccakf1600_index (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc keccakf1600_rho_offsets (i:int) : int = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return r;
  }
  proc keccakf1600_rhotates (x:int, y:int) : int = {
    var r:int;
    var i:int;
    i <@ keccakf1600_index (x, y);
    r <@ keccakf1600_rho_offsets (i);
    return r;
  }
  proc __rol_u64_ref (x:W64.t, i:int) : W64.t = {
    var  _0:bool;
    var  _1:bool;
    if ((i <> 0)) {
      ( _0,  _1, x) <- (ROL_64 x (W8.of_int i));
    } else {
      
    }
    return x;
  }
  proc __theta_sum_ref (a:W64.t Array25.t) : W64.t Array5.t = {
    var c:W64.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c.[x] <- a.[(x + 0)];
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __theta_rol_ref (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux:W64.t;
    var d:W64.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux <@ __rol_u64_ref (d.[x], 1);
      d.[x] <- aux;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- (x + 1);
    }
    return d;
  }
  proc __rol_sum_ref (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : W64.t Array5.t = {
    var aux:W64.t;
    var b:W64.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while ((x < 5)) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ keccakf1600_rhotates (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      aux <@ __rol_u64_ref (b.[x], r);
      b.[x] <- aux;
      x <- (x + 1);
    }
    return b;
  }
  proc __set_row_ref (e:W64.t Array25.t, b:W64.t Array5.t, y:int) : W64.t Array25.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <@ __ANDN_64 (b.[x1], b.[x2]);
      t <- (t `^` b.[x]);
      e.[(x + (y * 5))] <- t;
      x <- (x + 1);
    }
    return e;
  }
  proc _pround_ref (e:W64.t Array25.t, a:W64.t Array25.t) : W64.t Array25.t = {
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    var y:int;
    var b:W64.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __theta_sum_ref (a);
    d <@ __theta_rol_ref (c);
    y <- 0;
    while ((y < 5)) {
      b <@ __rol_sum_ref (a, d, y);
      e <@ __set_row_ref (e, b, y);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t = {
    var s_e:W64.t Array25.t;
    var e:W64.t Array25.t;
    var rC:W64.t Array24.t;
    var rc:W64.t;
    var c:int;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    e <- s_e;
    c <- 0;
    (* Erased call to spill *)
    e <@ _pround_ref (e, a);
    (a, e) <- (swap_ e a);
    rC <- kECCAK1600_RC;
    rc <- rC.[c];
    e.[0] <- (e.[0] `^` rc);
    a <@ _pround_ref (a, e);
    (a, e) <- (swap_ e a);
    rC <- kECCAK1600_RC;
    rc <- rC.[(c + 1)];
    a.[0] <- (a.[0] `^` rc);
    (* Erased call to unspill *)
    c <- (c + 2);
    while ((c < (24 - 1))) {
      (* Erased call to spill *)
      e <@ _pround_ref (e, a);
      (a, e) <- (swap_ e a);
      rC <- kECCAK1600_RC;
      rc <- rC.[c];
      e.[0] <- (e.[0] `^` rc);
      a <@ _pround_ref (a, e);
      (a, e) <- (swap_ e a);
      rC <- kECCAK1600_RC;
      rc <- rC.[(c + 1)];
      a.[0] <- (a.[0] `^` rc);
      (* Erased call to unspill *)
      c <- (c + 2);
    }
    return a;
  }
  proc _keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t = {
    
    a <@ __keccakf1600_ref (a);
    return a;
  }
  proc _keccakf1600_ref_ (a:W64.t Array25.t) : W64.t Array25.t = {
    
    a <- a;
    a <@ _keccakf1600_ref (a);
    a <- a;
    return a;
  }
  proc __state_init_ref (st:W64.t Array25.t) : W64.t Array25.t = {
    var z64:W64.t;
    var i:int;
    z64 <- (W64.of_int 0);
    i <- 0;
    while ((i < 25)) {
      st.[i] <- z64;
      i <- (i + 1);
    }
    return st;
  }
  proc __addratebit_ref (st:W64.t Array25.t, _RATE8:int) : W64.t Array25.t = {
    
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8_direct (WArray200.init64 (fun i => st.[i])) (_RATE8 - 1)
    ((get8_direct (WArray200.init64 (fun i => st.[i])) (_RATE8 - 1)) `^`
    (W8.of_int 128)))));
    return st;
  }
  proc __SHLQ (x:W64.t, shbytes:int) : W64.t = {
    
    if ((shbytes <> 0)) {
      x <- (x `<<` (W8.of_int (8 * shbytes)));
    } else {
      
    }
    return x;
  }
  proc __SHLDQ (x:W128.t, shbytes:int) : W128.t = {
    
    if ((shbytes <> 0)) {
      x <- (VPSLLDQ_128 x (W8.of_int shbytes));
    } else {
      
    }
    return x;
  }
  proc __SHLQ_256 (x:W256.t, shbytes:int) : W256.t = {
    
    if ((shbytes <> 0)) {
      x <- (VPSLL_4u64 x (W128.of_int (8 * shbytes)));
    } else {
      
    }
    return x;
  }
  proc __m_ilen_read_upto8_at (buf:int, lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      if ((8 <= lEN)) {
        w <- (loadW64 Glob.mem buf);
        w <@ __SHLQ (w, (aT - cUR));
        buf <- (buf + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        if ((4 <= lEN)) {
          w <- (zeroextu64 (loadW32 Glob.mem buf));
          w <@ __SHLQ (w, (aT - cUR));
          buf <- (buf + (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          lEN <- (lEN - (((cUR + 8) <= (aT + 4)) ? ((cUR + 8) - aT) : 4));
          aT <- (((cUR + 8) <= (aT + 4)) ? (cUR + 8) : (aT + 4));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT < (cUR + 8)) /\ (2 <= lEN))) {
          t16 <- (zeroextu64 (loadW16 Glob.mem buf));
          buf <- (buf + (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          lEN <- (lEN - (((cUR + 8) <= (aT + 2)) ? ((cUR + 8) - aT) : 2));
          t16 <@ __SHLQ (t16, (aT - cUR));
          w <- (w `|` t16);
          aT <- (((cUR + 8) <= (aT + 2)) ? (cUR + 8) : (aT + 2));
        } else {
          
        }
        if (((aT < (cUR + 8)) /\ (1 <= lEN))) {
          t8 <- (zeroextu64 (loadW8 Glob.mem buf));
          buf <- (buf + 1);
          lEN <- (lEN - 1);
          t8 <@ __SHLQ (t8, (aT - cUR));
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
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_upto8_at2 (buf:int, lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var aT8:int;
    var t16:W64.t;
    var t8:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (W64.of_int 0);
    } else {
      aT8 <- (aT - cUR);
      if ((8 <= lEN)) {
        w <- (loadW64 Glob.mem buf);
        w <@ __SHLQ (w, aT8);
        buf <- (buf + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        if ((4 <= lEN)) {
          w <- (zeroextu64 (loadW32 Glob.mem buf));
          w <@ __SHLQ (w, aT8);
          buf <- (buf + ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          lEN <- (lEN - ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          aT8 <- ((8 <= (4 + aT8)) ? 8 : (4 + aT8));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT8 < 8) /\ (2 <= lEN))) {
          t16 <- (zeroextu64 (loadW16 Glob.mem buf));
          buf <- (buf + ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          lEN <- (lEN - ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          t16 <@ __SHLQ (t16, aT8);
          w <- (w `|` t16);
          aT8 <- ((8 <= (2 + aT8)) ? 8 : (2 + aT8));
        } else {
          
        }
        if ((aT8 < 8)) {
          if ((1 <= lEN)) {
            t8 <- (zeroextu64 (loadW8 Glob.mem buf));
            t8 <- (t8 `|` (W64.of_int (256 * (tRAIL %% 256))));
            buf <- (buf + 1);
            lEN <- (lEN - 1);
            t8 <@ __SHLQ (t8, aT8);
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
              t8 <@ __SHLQ (t8, aT8);
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
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_upto16_at (buf:int, lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W128.t = {
    var w:W128.t;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 16) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <- (loadW128 Glob.mem buf);
        w <@ __SHLDQ (w, (aT - cUR));
        buf <- (buf + (16 - (aT - cUR)));
        lEN <- (lEN - (16 - (aT - cUR)));
        aT <- (cUR + 16);
      } else {
        if (((cUR + 8) <= aT)) {
          w <- (set0_128);
          (buf, lEN, tRAIL, aT, t64_1) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (buf, lEN, tRAIL, aT, t64_0) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, cUR, aT);
          w <- (VMOV_64 t64_0);
          (buf, lEN, tRAIL, aT, t64_1) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, (cUR + 8), aT);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
    }
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_upto32_at (buf:int, lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W256.t = {
    var w:W256.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 32) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_256);
    } else {
      if (((aT = cUR) /\ (32 <= lEN))) {
        w <- (loadW256 Glob.mem buf);
        buf <- (buf + 32);
        lEN <- (lEN - 32);
        aT <- (aT + 32);
      } else {
        if (((cUR + 16) <= aT)) {
          w <- (set0_256);
          (buf, lEN, tRAIL, aT, t128_1) <@ __m_ilen_read_upto16_at (buf, 
          lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (buf, lEN, tRAIL, aT, t128_0) <@ __m_ilen_read_upto16_at (buf, 
          lEN, tRAIL, cUR, aT);
          w <- (zeroextu256 t128_0);
          (buf, lEN, tRAIL, aT, t128_1) <@ __m_ilen_read_upto16_at (buf, 
          lEN, tRAIL, (cUR + 16), aT);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        }
      }
    }
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_bcast_upto8_at (buf:int, lEN:int, tRAIL:int, cUR:int,
                                     aT:int) : int * int * int * int * W256.t = {
    var w256:W256.t;
    var w:W64.t;
    var t128:W128.t;
    if (((((lEN < 0) \/ (aT < cUR)) \/ ((cUR + 8) <= aT)) \/
        ((lEN = 0) /\ (tRAIL = 0)))) {
      w256 <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w256 <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
        w256 <@ __SHLQ_256 (w256, (aT - cUR));
        buf <- (buf + ((cUR + 8) - aT));
        lEN <- (lEN - ((cUR + 8) - aT));
        aT <- (cUR + 8);
      } else {
        (buf, lEN, tRAIL, aT, w) <@ __m_ilen_read_upto8_at (buf, lEN, 
        tRAIL, cUR, aT);
        t128 <- (VMOV_64 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (buf, lEN, tRAIL, aT, w256);
  }
  proc __m_ilen_write_upto8 (buf:int, lEN:int, w:W64.t) : int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        Glob.mem <- (storeW64 Glob.mem buf w);
        buf <- (buf + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          Glob.mem <- (storeW32 Glob.mem buf (truncateu32 w));
          w <- (w `>>` (W8.of_int 32));
          buf <- (buf + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          Glob.mem <- (storeW16 Glob.mem buf (truncateu16 w));
          w <- (w `>>` (W8.of_int 16));
          buf <- (buf + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          Glob.mem <- (storeW8 Glob.mem buf (truncateu8 w));
          buf <- (buf + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __m_ilen_write_upto16 (buf:int, lEN:int, w:W128.t) : int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        Glob.mem <- (storeW128 Glob.mem buf w);
        buf <- (buf + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          Glob.mem <- (storeW64 Glob.mem buf (MOVV_64 (truncateu64 w)));
          buf <- (buf + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (truncateu64 w);
        (buf, lEN) <@ __m_ilen_write_upto8 (buf, lEN, t64);
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __m_ilen_write_upto32 (buf:int, lEN:int, w:W256.t) : int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        Glob.mem <- (storeW256 Glob.mem buf w);
        buf <- (buf + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          Glob.mem <- (storeW128 Glob.mem buf t128);
          buf <- (buf + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        (buf, lEN) <@ __m_ilen_write_upto16 (buf, lEN, t128);
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __m_rlen_read_upto8 (buf:int, len:int) : int * W64.t = {
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
      w <- (loadW64 Glob.mem buf);
      buf <- (buf + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        w <- (zeroextu64 (loadW32 Glob.mem buf));
        buf <- (buf + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        x <- (zeroextu64 (loadW16 Glob.mem buf));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        buf <- (buf + 2);
        sh <- (sh + (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        x <- (zeroextu64 (loadW8 Glob.mem buf));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        buf <- (buf + 1);
      } else {
        
      }
    }
    return (buf, w);
  }
  proc __m_rlen_write_upto8 (buf:int, data:W64.t, len:int) : int = {
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
      Glob.mem <- (storeW64 Glob.mem buf data);
      buf <- (buf + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        Glob.mem <- (storeW32 Glob.mem buf (truncateu32 data));
        buf <- (buf + 4);
        data <- (data `>>` (W8.of_int 32));
      } else {
        
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        Glob.mem <- (storeW16 Glob.mem buf (truncateu16 data));
        buf <- (buf + 2);
        data <- (data `>>` (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        Glob.mem <- (storeW8 Glob.mem buf (truncateu8 data));
        buf <- (buf + 1);
      } else {
        
      }
    }
    return buf;
  }
  proc __addstate_m_ref (st:W64.t Array25.t, aT:int, buf:int, _LEN:int,
                         _TRAILB:int) : W64.t Array25.t * int * int = {
    var aT8:int;
    var w:W64.t;
    var at:int;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (buf, _LEN, _TRAILB, aT8, w) <@ __m_ilen_read_upto8_at (buf, _LEN,
      _TRAILB, aT, aT8);
      st.[(aT %/ 8)] <- (st.[(aT %/ 8)] `^` w);
      aT <- aT8;
    } else {
      
    }
    at <- (aT %/ 8);
    while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
      w <- (loadW64 Glob.mem buf);
      buf <- (buf + 8);
      st.[at] <- (st.[at] `^` w);
      at <- (at + 1);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (buf, _LEN, _TRAILB, aT, w) <@ __m_ilen_read_upto8_at (buf, _LEN,
      _TRAILB, aT, aT);
      st.[at] <- (st.[at] `^` w);
    } else {
      
    }
    return (st, aT, buf);
  }
  proc __absorb_m_ref (st:W64.t Array25.t, aT:int, buf:int, _LEN:int,
                       _TRAILB:int, _RATE8:int) : W64.t Array25.t * int * int = {
    var iTERS:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, buf) <@ __addstate_m_ref (st, aT, buf, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, buf) <@ __addstate_m_ref (st, 0, buf, _RATE8, 0);
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT, buf) <@ __addstate_m_ref (st, aT, buf, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_ref (st, _RATE8);
    } else {
      
    }
    return (st, aT, buf);
  }
  proc __dumpstate_m_ref (buf:int, _LEN:int, st:W64.t Array25.t) : int = {
    var t:W64.t;
    var i:int;
    var  _0:int;
    i <- 0;
    while ((i < (_LEN %/ 8))) {
      t <- st.[i];
      Glob.mem <- (storeW64 Glob.mem buf t);
      buf <- (buf + 8);
      i <- (i + 1);
    }
    if ((0 < (_LEN %% 8))) {
      t <- st.[i];
      (buf,  _0) <@ __m_ilen_write_upto8 (buf, (_LEN %% 8), t);
    } else {
      
    }
    return buf;
  }
  proc __squeeze_m_ref (st:W64.t Array25.t, buf:int, _LEN:int, _RATE8:int) : 
  W64.t Array25.t * int = {
    var i:int;
    i <- 0;
    while ((i < (_LEN %/ _RATE8))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      buf <@ __dumpstate_m_ref (buf, _RATE8, st);
      i <- (i + 1);
    }
    if ((0 < (_LEN %% _RATE8))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      buf <@ __dumpstate_m_ref (buf, (_LEN %% _RATE8), st);
    } else {
      
    }
    return (st, buf);
  }
  proc __keccakf1600_pround_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    var c00:W256.t;
    var c14:W256.t;
    var t2:W256.t;
    var t4:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    var d14:W256.t;
    var d00:W256.t;
    var t3:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    c00 <-
    (VPSHUFD_256 state.[2]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    c14 <- (state.[5] `^` state.[3]);
    t2 <- (state.[4] `^` state.[6]);
    c14 <- (c14 `^` state.[1]);
    c14 <- (c14 `^` t2);
    t4 <-
    (VPERMQ c14
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    c00 <- (c00 `^` state.[2]);
    t0 <-
    (VPERMQ c00
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t1 <- (c14 \vshr64u256 (W128.of_int 63));
    t2 <- (c14 \vadd64u256 c14);
    t1 <- (t1 `|` t2);
    d14 <-
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    d00 <- (t1 `^` t4);
    d00 <-
    (VPERMQ d00
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    c00 <- (c00 `^` state.[0]);
    c00 <- (c00 `^` t0);
    t0 <- (c00 \vshr64u256 (W128.of_int 63));
    t1 <- (c00 \vadd64u256 c00);
    t1 <- (t1 `|` t0);
    state.[2] <- (state.[2] `^` d00);
    state.[0] <- (state.[0] `^` d00);
    d14 <-
    (VPBLEND_8u32 d14 t1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t4 <-
    (VPBLEND_8u32 t4 c00
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
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    d14 <- (d14 `^` t4);
    t3 <- (VPSLLV_4u64 state.[2] kECCAK_RHOTATES_LEFT.[0]);
    state.[2] <- (VPSRLV_4u64 state.[2] kECCAK_RHOTATES_RIGHT.[0]);
    state.[2] <- (state.[2] `|` t3);
    state.[3] <- (state.[3] `^` d14);
    t4 <- (VPSLLV_4u64 state.[3] kECCAK_RHOTATES_LEFT.[2]);
    state.[3] <- (VPSRLV_4u64 state.[3] kECCAK_RHOTATES_RIGHT.[2]);
    state.[3] <- (state.[3] `|` t4);
    state.[4] <- (state.[4] `^` d14);
    t5 <- (VPSLLV_4u64 state.[4] kECCAK_RHOTATES_LEFT.[3]);
    state.[4] <- (VPSRLV_4u64 state.[4] kECCAK_RHOTATES_RIGHT.[3]);
    state.[4] <- (state.[4] `|` t5);
    state.[5] <- (state.[5] `^` d14);
    t6 <- (VPSLLV_4u64 state.[5] kECCAK_RHOTATES_LEFT.[4]);
    state.[5] <- (VPSRLV_4u64 state.[5] kECCAK_RHOTATES_RIGHT.[4]);
    state.[5] <- (state.[5] `|` t6);
    state.[6] <- (state.[6] `^` d14);
    t3 <-
    (VPERMQ state.[2]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t4 <-
    (VPERMQ state.[3]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t7 <- (VPSLLV_4u64 state.[6] kECCAK_RHOTATES_LEFT.[5]);
    t1 <- (VPSRLV_4u64 state.[6] kECCAK_RHOTATES_RIGHT.[5]);
    t1 <- (t1 `|` t7);
    state.[1] <- (state.[1] `^` d14);
    t5 <-
    (VPERMQ state.[4]
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    t6 <-
    (VPERMQ state.[5]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t8 <- (VPSLLV_4u64 state.[1] kECCAK_RHOTATES_LEFT.[1]);
    t2 <- (VPSRLV_4u64 state.[1] kECCAK_RHOTATES_RIGHT.[1]);
    t2 <- (t2 `|` t8);
    t7 <- (VPSRLDQ_256 t1 (W8.of_int 8));
    t0 <- ((invw t1) `&` t7);
    state.[3] <-
    (VPBLEND_8u32 t2 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t4 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 t3 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t2 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <-
    (VPBLEND_8u32 state.[3] t4
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t5
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 state.[5] t2
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t6
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <-
    (VPBLEND_8u32 state.[3] t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[5] <-
    (VPBLEND_8u32 state.[5] t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[3] <- ((invw state.[3]) `&` t8);
    state.[5] <- ((invw state.[5]) `&` t7);
    state.[6] <-
    (VPBLEND_8u32 t5 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t3 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[3] <- (state.[3] `^` t3);
    state.[6] <-
    (VPBLEND_8u32 state.[6] t3
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t4
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[5] <- (state.[5] `^` t5);
    state.[6] <-
    (VPBLEND_8u32 state.[6] t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t8 <-
    (VPBLEND_8u32 t8 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[6] <- ((invw state.[6]) `&` t8);
    state.[6] <- (state.[6] `^` t6);
    state.[4] <-
    (VPERMQ t1
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    t8 <-
    (VPBLEND_8u32 state.[4] state.[0]
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[1] <-
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[1] <-
    (VPBLEND_8u32 state.[1] state.[0]
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[1] <- ((invw state.[1]) `&` t8);
    state.[2] <-
    (VPBLEND_8u32 t4 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t6 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[2] <-
    (VPBLEND_8u32 state.[2] t6
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t3
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[2] <-
    (VPBLEND_8u32 state.[2] t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[2] <- ((invw state.[2]) `&` t7);
    state.[2] <- (state.[2] `^` t2);
    t0 <-
    (VPERMQ t0
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[3] <-
    (VPERMQ state.[3]
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state.[5] <-
    (VPERMQ state.[5]
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    state.[6] <-
    (VPERMQ state.[6]
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    state.[4] <-
    (VPBLEND_8u32 t6 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t5 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[4] <-
    (VPBLEND_8u32 state.[4] t5
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t2
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
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state.[4] <-
    (VPBLEND_8u32 state.[4] t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t7 <-
    (VPBLEND_8u32 t7 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state.[4] <- ((invw state.[4]) `&` t7);
    state.[0] <- (state.[0] `^` t0);
    state.[1] <- (state.[1] `^` t1);
    state.[4] <- (state.[4] `^` t4);
    return state;
  }
  proc __keccakf1600_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    var round_constants:W64.t Array24.t;
    var rc:W256.t;
    var r:int;
    round_constants <- witness;
    round_constants <- kECCAK1600_RC;
    r <- 0;
    state <@ __keccakf1600_pround_avx2 (state);
    rc <- (VPBROADCAST_4u64 round_constants.[r]);
    state.[0] <- (state.[0] `^` rc);
    r <- (r + 1);
    while ((r < 24)) {
      state <@ __keccakf1600_pround_avx2 (state);
      rc <- (VPBROADCAST_4u64 round_constants.[r]);
      state.[0] <- (state.[0] `^` rc);
      r <- (r + 1);
    }
    return state;
  }
  proc _keccakf1600_avx2 (state:W256.t Array7.t) : W256.t Array7.t = {
    
    state <@ __keccakf1600_avx2 (state);
    return state;
  }
  proc __stavx2_pack (st:W64.t Array25.t) : W256.t Array7.t = {
    var state:W256.t Array7.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var r:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    state <- witness;
    state.[0] <-
    (VPBROADCAST_4u64
    (get64_direct (WArray200.init64 (fun i => st.[i])) (8 * 0)));
    state.[1] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (1 * 8));
    t128_1 <- (VMOV_64 st.[5]);
    state.[3] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (6 * 8));
    t128_0 <- (VMOV_64 st.[10]);
    state.[4] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (11 * 8));
    r <- st.[15];
    t128_1 <- (VPINSR_2u64 t128_1 r (W8.of_int 1));
    state.[5] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (16 * 8));
    r <- st.[20];
    t128_0 <- (VPINSR_2u64 t128_0 r (W8.of_int 1));
    t256_0 <- (zeroextu256 t128_0);
    t256_0 <- (VINSERTI128 t256_0 t128_1 (W8.of_int 1));
    state.[2] <- t256_0;
    state.[6] <-
    (get256_direct (WArray200.init64 (fun i => st.[i])) (21 * 8));
    t256_0 <-
    (VPBLEND_8u32 state.[3] state.[5]
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
    t256_1 <-
    (VPBLEND_8u32 state.[6] state.[4]
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
    t256_2 <-
    (VPBLEND_8u32 state.[4] state.[3]
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
    state.[3] <-
    (VPBLEND_8u32 t256_0 t256_1
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
    state.[4] <-
    (VPBLEND_8u32 t256_1 t256_0
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
    t256_0 <-
    (VPBLEND_8u32 state.[5] state.[6]
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
    state.[5] <-
    (VPBLEND_8u32 t256_0 t256_2
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
    state.[6] <-
    (VPBLEND_8u32 t256_2 t256_0
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
    return state;
  }
  proc __stavx2_unpack (st:W64.t Array25.t, state:W256.t Array7.t) : 
  W64.t Array25.t = {
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    t128_0 <- (truncateu128 state.[0]);
    st.[0] <- (VMOVLPD t128_0);
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (1 * 8)
    state.[1])));
    t256_0 <-
    (VPBLEND_8u32 state.[3] state.[4]
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
    (VPBLEND_8u32 state.[4] state.[3]
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
    (VPBLEND_8u32 state.[5] state.[6]
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
    (VPBLEND_8u32 state.[6] state.[5]
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
    t128_1 <- (VEXTRACTI128 state.[2] (W8.of_int 1));
    st.[5] <- (VMOVLPD t128_1);
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
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (6 * 8)
    t256_4)));
    t128_0 <- (truncateu128 state.[2]);
    st.[10] <- (VMOVLPD t128_0);
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
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (11 * 8)
    t256_4)));
    st.[15] <- (VMOVHPD t128_1);
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
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (16 * 8)
    t256_4)));
    st.[20] <- (VMOVHPD t128_0);
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
    st <-
    (Array25.init
    (WArray200.get64
    (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) (21 * 8)
    t256_4)));
    return st;
  }
  proc _keccakf1600_st25_avx2 (st25:W64.t Array25.t) : W64.t Array25.t = {
    var state:W256.t Array7.t;
    state <- witness;
    state <@ __stavx2_pack (st25);
    state <@ __keccakf1600_avx2 (state);
    st25 <@ __stavx2_unpack (st25, state);
    return st25;
  }
  proc __u64_to_u256 (x:W64.t, l:int) : W256.t = {
    var t256:W256.t;
    var t128:W128.t;
    if (((l %% 2) = 0)) {
      t128 <- (VMOV_64 x);
    } else {
      t128 <- (set0_128);
      t128 <- (VPINSR_2u64 t128 x (W8.of_int 1));
    }
    t256 <- (set0_256);
    if (((l %/ 2) = 0)) {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 0));
    } else {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 1));
    }
    return t256;
  }
  proc __state_init_avx2 () : W256.t Array7.t = {
    var st:W256.t Array7.t;
    var i:int;
    st <- witness;
    i <- 0;
    while ((i < 7)) {
      st.[i] <- (set0_256);
      i <- (i + 1);
    }
    return st;
  }
  proc __perm_reg3456_avx2 (r3:W256.t, r4:W256.t, r5:W256.t, r6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var st3:W256.t;
    var st4:W256.t;
    var st5:W256.t;
    var st6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    t256_0 <-
    (VPBLEND_8u32 r3 r5
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
    t256_1 <-
    (VPBLEND_8u32 r6 r4
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
    t256_2 <-
    (VPBLEND_8u32 r4 r3
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
    st3 <-
    (VPBLEND_8u32 t256_0 t256_1
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
    st4 <-
    (VPBLEND_8u32 t256_1 t256_0
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
    t256_0 <-
    (VPBLEND_8u32 r5 r6
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
    st5 <-
    (VPBLEND_8u32 t256_0 t256_2
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
    st6 <-
    (VPBLEND_8u32 t256_2 t256_0
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
    return (st3, st4, st5, st6);
  }
  proc __unperm_reg3456_avx2 (st3:W256.t, st4:W256.t, st5:W256.t, st6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    t256_0 <-
    (VPBLEND_8u32 st3 st4
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
    (VPBLEND_8u32 st4 st3
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
    (VPBLEND_8u32 st5 st6
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
    (VPBLEND_8u32 st6 st5
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
    r3 <-
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
    r4 <-
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
    r5 <-
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
    r6 <-
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
    return (r3, r4, r5, r6);
  }
  proc __addstate_r3456_avx2 (st:W256.t Array7.t, r3:W256.t, r4:W256.t,
                              r5:W256.t, r6:W256.t) : W256.t Array7.t = {
    
    (r3, r4, r5, r6) <@ __perm_reg3456_avx2 (r3, r4, r5, r6);
    st.[3] <- (st.[3] `^` r3);
    st.[4] <- (st.[4] `^` r4);
    st.[5] <- (st.[5] `^` r5);
    st.[6] <- (st.[6] `^` r6);
    return st;
  }
  proc __stavx2_pos_avx2 (pOS:int) : int * int = {
    var r:int;
    var l:int;
    r <- 0;
    l <- 0;
    if ((0 < pOS)) {
      if ((pOS <= 4)) {
        r <- 1;
        l <- (pOS - 1);
      } else {
        if ((pOS = 10)) {
          r <- 2;
          l <- 0;
        } else {
          if ((pOS = 20)) {
            r <- 2;
            l <- 1;
          } else {
            if ((pOS = 5)) {
              r <- 2;
              l <- 2;
            } else {
              if ((pOS = 15)) {
                r <- 2;
                l <- 3;
              } else {
                if ((pOS = 16)) {
                  r <- 3;
                  l <- 0;
                } else {
                  if ((pOS = 7)) {
                    r <- 3;
                    l <- 1;
                  } else {
                    if ((pOS = 23)) {
                      r <- 3;
                      l <- 2;
                    } else {
                      if ((pOS = 14)) {
                        r <- 3;
                        l <- 3;
                      } else {
                        if ((pOS = 11)) {
                          r <- 4;
                          l <- 0;
                        } else {
                          if ((pOS = 22)) {
                            r <- 4;
                            l <- 1;
                          } else {
                            if ((pOS = 8)) {
                              r <- 4;
                              l <- 2;
                            } else {
                              if ((pOS = 19)) {
                                r <- 4;
                                l <- 3;
                              } else {
                                if ((pOS = 21)) {
                                  r <- 5;
                                  l <- 0;
                                } else {
                                  if ((pOS = 17)) {
                                    r <- 5;
                                    l <- 1;
                                  } else {
                                    if ((pOS = 13)) {
                                      r <- 5;
                                      l <- 2;
                                    } else {
                                      if ((pOS = 9)) {
                                        r <- 5;
                                        l <- 3;
                                      } else {
                                        if ((pOS = 6)) {
                                          r <- 6;
                                          l <- 0;
                                        } else {
                                          if ((pOS = 12)) {
                                            r <- 6;
                                            l <- 1;
                                          } else {
                                            if ((pOS = 18)) {
                                              r <- 6;
                                              l <- 2;
                                            } else {
                                              if ((pOS = 24)) {
                                                r <- 6;
                                                l <- 3;
                                              } else {
                                                
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    } else {
      
    }
    return (r, l);
  }
  proc __addratebit_avx2 (st:W256.t Array7.t, rATE_8:int) : W256.t Array7.t = {
    var t64:W64.t;
    var r:int;
    var l:int;
    var t256:W256.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE_8) - 1) %% 64)));
    (r, l) <@ __stavx2_pos_avx2 (((rATE_8 - 1) %/ 8));
    if ((r = 0)) {
      t256 <- (VPBROADCAST_4u64 t64);
    } else {
      t256 <@ __u64_to_u256 (t64, l);
    }
    st.[r] <- (st.[r] `^` t256);
    return st;
  }
  proc __addstate_m_avx2 (st:W256.t Array7.t, aT:int, buf:int, _LEN:int,
                          _TRAILB:int) : W256.t Array7.t * int * int = {
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
    if ((aT < 8)) {
      (buf, _LEN, _TRAILB, aT, r0) <@ __m_ilen_read_bcast_upto8_at (buf,
      _LEN, _TRAILB, 0, aT);
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (buf, _LEN, _TRAILB, aT, r1) <@ __m_ilen_read_upto32_at (buf, _LEN,
      _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (buf, _LEN, _TRAILB, aT, t64_2) <@ __m_ilen_read_upto8_at (buf, 
      _LEN, _TRAILB, 40, aT);
      t128_1 <- (VMOV_64 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (buf, _LEN, _TRAILB, aT, r3) <@ __m_ilen_read_upto32_at (buf, 
        _LEN, _TRAILB, 48, aT);
        (buf, _LEN, _TRAILB, aT, t64_3) <@ __m_ilen_read_upto8_at (buf, 
        _LEN, _TRAILB, 80, aT);
        t128_2 <- (VMOV_64 t64_3);
        (buf, _LEN, _TRAILB, aT, r4) <@ __m_ilen_read_upto32_at (buf, 
        _LEN, _TRAILB, 88, aT);
        (buf, _LEN, _TRAILB, aT, t64_4) <@ __m_ilen_read_upto8_at (buf, 
        _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (buf, _LEN, _TRAILB, aT, r5) <@ __m_ilen_read_upto32_at (buf, 
        _LEN, _TRAILB, 128, aT);
        (buf, _LEN, _TRAILB, aT, t64_5) <@ __m_ilen_read_upto8_at (buf, 
        _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (buf, _LEN, _TRAILB, aT, r6) <@ __m_ilen_read_upto32_at (buf, 
        _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
      } else {
        
      }
      r2 <- (zeroextu256 t128_2);
      r2 <- (VINSERTI128 r2 t128_1 (W8.of_int 1));
      st.[2] <- (st.[2] `^` r2);
    } else {
      
    }
    return (st, aT, buf);
  }
  proc __absorb_m_avx2 (st:W256.t Array7.t, aT:int, buf:int, _LEN:int,
                        _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var iTERS:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, buf) <@ __addstate_m_avx2 (st, aT, buf, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, buf) <@ __addstate_m_avx2 (st, 0, buf, _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_m_avx2 (st, aT, buf, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_m_avx2 (buf:int, _LEN:int, st:W256.t Array7.t) : int = {
    var t128_1:W128.t;
    var t128_0:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var  _0:int;
    if ((8 <= _LEN)) {
      (buf,  _0) <@ __m_ilen_write_upto32 (buf, 8, st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, st.[0]);
    }
    (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t128_0 <- (truncateu128 st.[2]);
      t <- (MOVV_64 (truncateu64 t128_1));
      (buf, _LEN) <@ __m_ilen_write_upto8 (buf, _LEN, t);
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
        (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, _LEN) <@ __m_ilen_write_upto8 (buf, _LEN, t);
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
          (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_1));
          (buf, _LEN) <@ __m_ilen_write_upto8 (buf, _LEN, t);
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
          (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (MOVV_64 (truncateu64 t128_0));
          (buf, _LEN) <@ __m_ilen_write_upto8 (buf, _LEN, t);
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
          (buf, _LEN) <@ __m_ilen_write_upto32 (buf, _LEN, t256_4);
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    return buf;
  }
  proc __squeeze_m_avx2 (st:W256.t Array7.t, buf:int, _LEN:int, _RATE8:int) : 
  W256.t Array7.t = {
    var iTERS:int;
    var lO:int;
    var i:int;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    i <- 0;
    while ((i < iTERS)) {
      st <@ _keccakf1600_avx2 (st);
      buf <@ __dumpstate_m_avx2 (buf, _RATE8, st);
      i <- (i + 1);
    }
    if ((0 < lO)) {
      st <@ _keccakf1600_avx2 (st);
      buf <@ __dumpstate_m_avx2 (buf, lO, st);
    } else {
      
    }
    return st;
  }
  proc _init_updstate_avx2 (st:W64.t Array26.t, r64:int, trailb:W8.t) : 
  W64.t Array26.t = {
    var r256:W256.t;
    var i:int;
    var status:W64.t;
    var t:W64.t;
    r256 <- (set0_256);
    i <- 0;
    while ((i < 6)) {
      st <-
      (Array26.init
      (WArray208.get64
      (WArray208.set256 (WArray208.init64 (fun i_0 => st.[i_0])) i r256)));
      i <- (i + 1);
    }
    st.[24] <- (W64.of_int 0);
    status <- (zeroextu64 trailb);
    status <- (status `<<` (W8.of_int 8));
    r64 <- (W8.to_uint ((W8.of_int r64) - (W8.of_int 1)));
    t <- (zeroextu64 (W8.of_int r64));
    status <- (status + t);
    status <- (status `<<` (W8.of_int 8));
    st.[25] <- status;
    return st;
  }
  proc _ststatus_data (ststatus:W64.t) : W8.t * int * int = {
    var trailb:W8.t;
    var at:W64.t;
    var r8:W64.t;
    var c_200:W64.t;
    var c_0:W64.t;
    var r8_ui:int;
    var at_ui:int;
    at <- ststatus;
    at <- (at `&` (W64.of_int 255));
    ststatus <- (ststatus `>>` (W8.of_int 8));
    r8 <- ststatus;
    r8 <- (r8 `&` (W64.of_int 255));
    r8 <- (r8 + (W64.of_int 1));
    r8 <- (r8 `<<` (W8.of_int 3));
    c_200 <- (W64.of_int 200);
    r8 <- (((W64.of_int 200) \ult r8) ? c_200 : r8);
    c_0 <- (W64.of_int 0);
    at <- ((r8 \ule at) ? c_0 : at);
    ststatus <- (ststatus `>>` (W8.of_int 8));
    trailb <- (truncateu8 ststatus);
    r8_ui <- (W64.to_uint r8);
    at_ui <- (W64.to_uint at);
    return (trailb, r8_ui, at_ui);
  }
  proc _finish_updstate_avx2 (st:W64.t Array26.t) : W64.t Array26.t = {
    var ststatus:W64.t;
    var trailb:W8.t;
    var r8:int;
    var at:int;
    ststatus <- st.[25];
    (trailb, r8, at) <@ _ststatus_data (ststatus);
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) at
    ((get8_direct (WArray208.init64 (fun i => st.[i])) at) `^` trailb))));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (r8 - 1)
    ((get8_direct (WArray208.init64 (fun i => st.[i])) (r8 - 1)) `^`
    (W8.of_int 128)))));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set32_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    ((get32_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)) `&`
    (W32.of_int 4278255360)))));
    return st;
  }
  proc keccak_ststatus (status:W8.t Array3.t, st:W64.t Array26.t) : W8.t Array3.t = {
    var ststatus:W64.t;
    var r8:int;
    var at:int;
    var  _0:W8.t;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    status.[0] <- (truncateu8 (W64.of_int r8));
    status.[1] <- (truncateu8 (W64.of_int at));
    status.[2] <-
    (get8_direct (WArray208.init64 (fun i => st.[i])) ((8 * 25) + 2));
    return status;
  }
  proc init_updstate_avx2 (st:W64.t Array26.t, r64:int, trailb:W8.t) : 
  W64.t Array26.t = {
    
    st <- st;
    r64 <- r64;
    trailb <- trailb;
    st <@ _init_updstate_avx2 (st, r64, trailb);
    return st;
  }
  proc finish_updstate_avx2 (st:W64.t Array26.t) : W64.t Array26.t = {
    
    st <- st;
    st <@ _finish_updstate_avx2 (st);
    return st;
  }
  proc _add_m_updstate_avx2 (st:W64.t Array25.t, at:int, buf:int, upto:int) : 
  W64.t Array25.t * int * int = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var buf2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (buf2, t64) <@ __m_rlen_read_upto8 (buf, len);
      len <- (len + (W64.to_uint at8));
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      if ((8 <= len)) {
        buf <- (buf + 8);
        buf <- (buf - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        buf <- buf2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (loadW64 Glob.mem buf);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      at <- newat;
      buf <- (buf + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (buf, t64) <@ __m_rlen_read_upto8 (buf, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
    } else {
      
    }
    at <- upto;
    return (st, at, buf);
  }
  proc _absorb_m_updstate_avx2 (st:W64.t Array26.t, buf:int, len:int) : 
  W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    len <- (len + at);
    while ((r8 <= len)) {
      (stk, at, buf) <@ _add_m_updstate_avx2 (stk, at, buf, r8);
      stk <@ _keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
    (stk, at,  _1) <@ _add_m_updstate_avx2 (stk, at, buf, len);
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }
  proc _dump_m_updstate_avx2 (buf:int, st:W64.t Array25.t, at:int, upto:int) : 
  int * int = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var buf2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      buf2 <@ __m_rlen_write_upto8 (buf, t64, len);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        buf <- (buf + 8);
        buf <- (buf - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        buf <- buf2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      Glob.mem <- (storeW64 Glob.mem buf t64);
      at <- newat;
      buf <- (buf + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      buf <@ __m_rlen_write_upto8 (buf, t64, (W64.to_uint upto8));
    } else {
      
    }
    at <- upto;
    return (buf, at);
  }
  proc _squeeze_m_updstate_avx2 (buf:int, len:int, st:W64.t Array26.t) : 
  int * W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var  _0:W8.t;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    if ((at = 0)) {
      stk <@ _keccakf1600_st25_avx2 (stk);
      at <- 0;
    } else {
      
    }
    len <- (len + at);
    while ((r8 < len)) {
      (buf, at) <@ _dump_m_updstate_avx2 (buf, stk, at, r8);
      (* Erased call to spill *)
      stk <@ _keccakf1600_st25_avx2 (stk);
      (* Erased call to unspill *)
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (buf, at) <@ _dump_m_updstate_avx2 (buf, stk, at, len);
    (* Erased call to unspill *)
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return (buf, st);
  }
  proc absorb_m_updstate_avx2 (st:W64.t Array26.t, buf:int, len:int) : 
  W64.t Array26.t = {
    
    st <- st;
    buf <- buf;
    st <@ _absorb_m_updstate_avx2 (st, buf, len);
    return st;
  }
  proc squeeze_m_updstate_avx2 (st:W64.t Array26.t, buf:int, len:int) : 
  W64.t Array26.t = {
    var  _0:int;
    st <- st;
    buf <- buf;
    ( _0, st) <@ _squeeze_m_updstate_avx2 (buf, len, st);
    return st;
  }
  proc __u256x4_4u64x4 (x0:W256.t, x1:W256.t, x2:W256.t, x3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var y0:W256.t;
    var y1:W256.t;
    var y2:W256.t;
    var y3:W256.t;
    y0 <- (VPUNPCKL_4u64 x0 x1);
    y1 <- (VPUNPCKH_4u64 x0 x1);
    y2 <- (VPUNPCKL_4u64 x2 x3);
    y3 <- (VPUNPCKH_4u64 x2 x3);
    x0 <- (VPERM2I128 y0 y2 (W8.of_int 32));
    x1 <- (VPERM2I128 y1 y3 (W8.of_int 32));
    x2 <- (VPERM2I128 y0 y2 (W8.of_int 49));
    x3 <- (VPERM2I128 y1 y3 (W8.of_int 49));
    return (x0, x1, x2, x3);
  }
  proc __st4x_pack (st4x:W256.t Array25.t, st0:W64.t Array25.t,
                    st1:W64.t Array25.t, st2:W64.t Array25.t,
                    st3:W64.t Array25.t) : W256.t Array25.t = {
    var i:int;
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    i <- 0;
    while ((i < 6)) {
      x0 <- (get256 (WArray200.init64 (fun i_0 => st0.[i_0])) i);
      x1 <- (get256 (WArray200.init64 (fun i_0 => st1.[i_0])) i);
      x2 <- (get256 (WArray200.init64 (fun i_0 => st2.[i_0])) i);
      x3 <- (get256 (WArray200.init64 (fun i_0 => st3.[i_0])) i);
      (x0, x1, x2, x3) <@ __u256x4_4u64x4 (x0, x1, x2, x3);
      st4x.[((4 * i) + 0)] <- x0;
      st4x.[((4 * i) + 1)] <- x1;
      st4x.[((4 * i) + 2)] <- x2;
      st4x.[((4 * i) + 3)] <- x3;
      i <- (i + 1);
    }
    t0 <- st0.[24];
    t1 <- st1.[24];
    t2 <- st2.[24];
    t3 <- st3.[24];
    st4x <-
    (Array25.init
    (WArray800.get256
    (WArray800.set64 (WArray800.init256 (fun i_0 => st4x.[i_0]))
    ((4 * 24) + 0) t0)));
    st4x <-
    (Array25.init
    (WArray800.get256
    (WArray800.set64 (WArray800.init256 (fun i_0 => st4x.[i_0]))
    ((4 * 24) + 1) t1)));
    st4x <-
    (Array25.init
    (WArray800.get256
    (WArray800.set64 (WArray800.init256 (fun i_0 => st4x.[i_0]))
    ((4 * 24) + 2) t2)));
    st4x <-
    (Array25.init
    (WArray800.get256
    (WArray800.set64 (WArray800.init256 (fun i_0 => st4x.[i_0]))
    ((4 * 24) + 3) t3)));
    return st4x;
  }
  proc __4u64x4_u256x4 (y0:W256.t, y1:W256.t, y2:W256.t, y3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    x0 <- (VPERM2I128 y0 y2 (W8.of_int 32));
    x1 <- (VPERM2I128 y1 y3 (W8.of_int 32));
    x2 <- (VPERM2I128 y0 y2 (W8.of_int 49));
    x3 <- (VPERM2I128 y1 y3 (W8.of_int 49));
    y0 <- (VPUNPCKL_4u64 x0 x1);
    y1 <- (VPUNPCKH_4u64 x0 x1);
    y2 <- (VPUNPCKL_4u64 x2 x3);
    y3 <- (VPUNPCKH_4u64 x2 x3);
    return (y0, y1, y2, y3);
  }
  proc __st4x_unpack (st0:W64.t Array25.t, st1:W64.t Array25.t,
                      st2:W64.t Array25.t, st3:W64.t Array25.t,
                      st4x:W256.t Array25.t) : W64.t Array25.t *
                                               W64.t Array25.t *
                                               W64.t Array25.t *
                                               W64.t Array25.t = {
    var i:int;
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    i <- 0;
    while ((i < 6)) {
      x0 <- st4x.[((4 * i) + 0)];
      x1 <- st4x.[((4 * i) + 1)];
      x2 <- st4x.[((4 * i) + 2)];
      x3 <- st4x.[((4 * i) + 3)];
      (x0, x1, x2, x3) <@ __4u64x4_u256x4 (x0, x1, x2, x3);
      st0 <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i_0 => st0.[i_0]))
      ((4 * 8) * i) x0)));
      st1 <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i_0 => st1.[i_0]))
      ((4 * 8) * i) x1)));
      st2 <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i_0 => st2.[i_0]))
      ((4 * 8) * i) x2)));
      st3 <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i_0 => st3.[i_0]))
      ((4 * 8) * i) x3)));
      i <- (i + 1);
    }
    t0 <- (get64 (WArray800.init256 (fun i_0 => st4x.[i_0])) ((4 * 24) + 0));
    t1 <- (get64 (WArray800.init256 (fun i_0 => st4x.[i_0])) ((4 * 24) + 1));
    t2 <- (get64 (WArray800.init256 (fun i_0 => st4x.[i_0])) ((4 * 24) + 2));
    t3 <- (get64 (WArray800.init256 (fun i_0 => st4x.[i_0])) ((4 * 24) + 3));
    st0.[24] <- t0;
    st1.[24] <- t1;
    st2.[24] <- t2;
    st3.[24] <- t3;
    return (st0, st1, st2, st3);
  }
  proc _keccakf1600_4x_pround (e:W256.t Array25.t, a:W256.t Array25.t,
                               r8:W256.t, r56:W256.t) : W256.t Array25.t = {
    var c_571:W256.t Array5.t;
    var d_619:W256.t Array5.t;
    var t_574:W256.t;
    var t_577:W256.t;
    var t_580:W256.t;
    var t_583:W256.t;
    var t_586:W256.t;
    var b_606:W256.t Array5.t;
    var t_593:W256.t;
    var t_596:W256.t;
    var t_599:W256.t;
    var t_602:W256.t;
    var t_607:W256.t;
    var t_608:W256.t;
    var t_609:W256.t;
    var t_610:W256.t;
    var t_611:W256.t;
    var t_612:W256.t;
    var t_613:W256.t;
    var t_614:W256.t;
    var t_615:W256.t;
    var t_616:W256.t;
    var b_638:W256.t Array5.t;
    var t_622:W256.t;
    var t_625:W256.t;
    var t_628:W256.t;
    var t_631:W256.t;
    var t_634:W256.t;
    var t_639:W256.t;
    var t_640:W256.t;
    var t_641:W256.t;
    var t_642:W256.t;
    var t_643:W256.t;
    var t_644:W256.t;
    var t_645:W256.t;
    var t_646:W256.t;
    var t_647:W256.t;
    var t_648:W256.t;
    var b_671:W256.t Array5.t;
    var t_655:W256.t;
    var t_658:W256.t;
    var t_661:W256.t;
    var t_667:W256.t;
    var t_672:W256.t;
    var t_673:W256.t;
    var t_674:W256.t;
    var t_675:W256.t;
    var t_676:W256.t;
    var t_677:W256.t;
    var t_678:W256.t;
    var t_679:W256.t;
    var t_680:W256.t;
    var t_681:W256.t;
    var b_704:W256.t Array5.t;
    var t_688:W256.t;
    var t_691:W256.t;
    var t_694:W256.t;
    var t_697:W256.t;
    var t_705:W256.t;
    var t_706:W256.t;
    var t_707:W256.t;
    var t_708:W256.t;
    var t_709:W256.t;
    var t_710:W256.t;
    var t_711:W256.t;
    var t_712:W256.t;
    var t_713:W256.t;
    var t_714:W256.t;
    var b_736:W256.t Array5.t;
    var t_720:W256.t;
    var t_723:W256.t;
    var t_726:W256.t;
    var t_729:W256.t;
    var t_732:W256.t;
    var t_737:W256.t;
    var t_738:W256.t;
    var t_739:W256.t;
    var t_740:W256.t;
    var t_741:W256.t;
    var t_742:W256.t;
    var t_743:W256.t;
    var t_744:W256.t;
    var t_745:W256.t;
    var t_746:W256.t;
    b_606 <- witness;
    b_638 <- witness;
    b_671 <- witness;
    b_704 <- witness;
    b_736 <- witness;
    c_571 <- witness;
    d_619 <- witness;
    c_571.[0] <- a.[0];
    c_571.[1] <- a.[1];
    c_571.[2] <- a.[2];
    c_571.[3] <- a.[3];
    c_571.[4] <- a.[4];
    c_571.[0] <- (c_571.[0] `^` a.[5]);
    c_571.[1] <- (c_571.[1] `^` a.[6]);
    c_571.[2] <- (c_571.[2] `^` a.[7]);
    c_571.[3] <- (c_571.[3] `^` a.[8]);
    c_571.[4] <- (c_571.[4] `^` a.[9]);
    c_571.[0] <- (c_571.[0] `^` a.[10]);
    c_571.[1] <- (c_571.[1] `^` a.[11]);
    c_571.[2] <- (c_571.[2] `^` a.[12]);
    c_571.[3] <- (c_571.[3] `^` a.[13]);
    c_571.[4] <- (c_571.[4] `^` a.[14]);
    c_571.[0] <- (c_571.[0] `^` a.[15]);
    c_571.[1] <- (c_571.[1] `^` a.[16]);
    c_571.[2] <- (c_571.[2] `^` a.[17]);
    c_571.[3] <- (c_571.[3] `^` a.[18]);
    c_571.[4] <- (c_571.[4] `^` a.[19]);
    c_571.[0] <- (c_571.[0] `^` a.[20]);
    c_571.[1] <- (c_571.[1] `^` a.[21]);
    c_571.[2] <- (c_571.[2] `^` a.[22]);
    c_571.[3] <- (c_571.[3] `^` a.[23]);
    c_571.[4] <- (c_571.[4] `^` a.[24]);
    d_619.[0] <- c_571.[1];
    t_574 <- (VPSLL_4u64 d_619.[0] (W128.of_int 1));
    d_619.[0] <- (VPSRL_4u64 d_619.[0] (W128.of_int 63));
    d_619.[0] <- (d_619.[0] `|` t_574);
    d_619.[0] <- (d_619.[0] `^` c_571.[4]);
    d_619.[1] <- c_571.[2];
    t_577 <- (VPSLL_4u64 d_619.[1] (W128.of_int 1));
    d_619.[1] <- (VPSRL_4u64 d_619.[1] (W128.of_int 63));
    d_619.[1] <- (d_619.[1] `|` t_577);
    d_619.[1] <- (d_619.[1] `^` c_571.[0]);
    d_619.[2] <- c_571.[3];
    t_580 <- (VPSLL_4u64 d_619.[2] (W128.of_int 1));
    d_619.[2] <- (VPSRL_4u64 d_619.[2] (W128.of_int 63));
    d_619.[2] <- (d_619.[2] `|` t_580);
    d_619.[2] <- (d_619.[2] `^` c_571.[1]);
    d_619.[3] <- c_571.[4];
    t_583 <- (VPSLL_4u64 d_619.[3] (W128.of_int 1));
    d_619.[3] <- (VPSRL_4u64 d_619.[3] (W128.of_int 63));
    d_619.[3] <- (d_619.[3] `|` t_583);
    d_619.[3] <- (d_619.[3] `^` c_571.[2]);
    d_619.[4] <- c_571.[0];
    t_586 <- (VPSLL_4u64 d_619.[4] (W128.of_int 1));
    d_619.[4] <- (VPSRL_4u64 d_619.[4] (W128.of_int 63));
    d_619.[4] <- (d_619.[4] `|` t_586);
    d_619.[4] <- (d_619.[4] `^` c_571.[3]);
    b_606.[0] <- a.[0];
    b_606.[0] <- (b_606.[0] `^` d_619.[0]);
    b_606.[1] <- a.[6];
    b_606.[1] <- (b_606.[1] `^` d_619.[1]);
    t_593 <- (VPSLL_4u64 b_606.[1] (W128.of_int 44));
    b_606.[1] <- (VPSRL_4u64 b_606.[1] (W128.of_int 20));
    b_606.[1] <- (b_606.[1] `|` t_593);
    b_606.[2] <- a.[12];
    b_606.[2] <- (b_606.[2] `^` d_619.[2]);
    t_596 <- (VPSLL_4u64 b_606.[2] (W128.of_int 43));
    b_606.[2] <- (VPSRL_4u64 b_606.[2] (W128.of_int 21));
    b_606.[2] <- (b_606.[2] `|` t_596);
    b_606.[3] <- a.[18];
    b_606.[3] <- (b_606.[3] `^` d_619.[3]);
    t_599 <- (VPSLL_4u64 b_606.[3] (W128.of_int 21));
    b_606.[3] <- (VPSRL_4u64 b_606.[3] (W128.of_int 43));
    b_606.[3] <- (b_606.[3] `|` t_599);
    b_606.[4] <- a.[24];
    b_606.[4] <- (b_606.[4] `^` d_619.[4]);
    t_602 <- (VPSLL_4u64 b_606.[4] (W128.of_int 14));
    b_606.[4] <- (VPSRL_4u64 b_606.[4] (W128.of_int 50));
    b_606.[4] <- (b_606.[4] `|` t_602);
    t_607 <- (VPANDN_256 b_606.[1] b_606.[2]);
    t_608 <- (t_607 `^` b_606.[0]);
    e.[0] <- t_608;
    t_609 <- (VPANDN_256 b_606.[2] b_606.[3]);
    t_610 <- (t_609 `^` b_606.[1]);
    e.[1] <- t_610;
    t_611 <- (VPANDN_256 b_606.[3] b_606.[4]);
    t_612 <- (t_611 `^` b_606.[2]);
    e.[2] <- t_612;
    t_613 <- (VPANDN_256 b_606.[4] b_606.[0]);
    t_614 <- (t_613 `^` b_606.[3]);
    e.[3] <- t_614;
    t_615 <- (VPANDN_256 b_606.[0] b_606.[1]);
    t_616 <- (t_615 `^` b_606.[4]);
    e.[4] <- t_616;
    b_638.[0] <- a.[3];
    b_638.[0] <- (b_638.[0] `^` d_619.[3]);
    t_622 <- (VPSLL_4u64 b_638.[0] (W128.of_int 28));
    b_638.[0] <- (VPSRL_4u64 b_638.[0] (W128.of_int 36));
    b_638.[0] <- (b_638.[0] `|` t_622);
    b_638.[1] <- a.[9];
    b_638.[1] <- (b_638.[1] `^` d_619.[4]);
    t_625 <- (VPSLL_4u64 b_638.[1] (W128.of_int 20));
    b_638.[1] <- (VPSRL_4u64 b_638.[1] (W128.of_int 44));
    b_638.[1] <- (b_638.[1] `|` t_625);
    b_638.[2] <- a.[10];
    b_638.[2] <- (b_638.[2] `^` d_619.[0]);
    t_628 <- (VPSLL_4u64 b_638.[2] (W128.of_int 3));
    b_638.[2] <- (VPSRL_4u64 b_638.[2] (W128.of_int 61));
    b_638.[2] <- (b_638.[2] `|` t_628);
    b_638.[3] <- a.[16];
    b_638.[3] <- (b_638.[3] `^` d_619.[1]);
    t_631 <- (VPSLL_4u64 b_638.[3] (W128.of_int 45));
    b_638.[3] <- (VPSRL_4u64 b_638.[3] (W128.of_int 19));
    b_638.[3] <- (b_638.[3] `|` t_631);
    b_638.[4] <- a.[22];
    b_638.[4] <- (b_638.[4] `^` d_619.[2]);
    t_634 <- (VPSLL_4u64 b_638.[4] (W128.of_int 61));
    b_638.[4] <- (VPSRL_4u64 b_638.[4] (W128.of_int 3));
    b_638.[4] <- (b_638.[4] `|` t_634);
    t_639 <- (VPANDN_256 b_638.[1] b_638.[2]);
    t_640 <- (t_639 `^` b_638.[0]);
    e.[5] <- t_640;
    t_641 <- (VPANDN_256 b_638.[2] b_638.[3]);
    t_642 <- (t_641 `^` b_638.[1]);
    e.[6] <- t_642;
    t_643 <- (VPANDN_256 b_638.[3] b_638.[4]);
    t_644 <- (t_643 `^` b_638.[2]);
    e.[7] <- t_644;
    t_645 <- (VPANDN_256 b_638.[4] b_638.[0]);
    t_646 <- (t_645 `^` b_638.[3]);
    e.[8] <- t_646;
    t_647 <- (VPANDN_256 b_638.[0] b_638.[1]);
    t_648 <- (t_647 `^` b_638.[4]);
    e.[9] <- t_648;
    b_671.[0] <- a.[1];
    b_671.[0] <- (b_671.[0] `^` d_619.[1]);
    t_655 <- (VPSLL_4u64 b_671.[0] (W128.of_int 1));
    b_671.[0] <- (VPSRL_4u64 b_671.[0] (W128.of_int 63));
    b_671.[0] <- (b_671.[0] `|` t_655);
    b_671.[1] <- a.[7];
    b_671.[1] <- (b_671.[1] `^` d_619.[2]);
    t_658 <- (VPSLL_4u64 b_671.[1] (W128.of_int 6));
    b_671.[1] <- (VPSRL_4u64 b_671.[1] (W128.of_int 58));
    b_671.[1] <- (b_671.[1] `|` t_658);
    b_671.[2] <- a.[13];
    b_671.[2] <- (b_671.[2] `^` d_619.[3]);
    t_661 <- (VPSLL_4u64 b_671.[2] (W128.of_int 25));
    b_671.[2] <- (VPSRL_4u64 b_671.[2] (W128.of_int 39));
    b_671.[2] <- (b_671.[2] `|` t_661);
    b_671.[3] <- a.[19];
    b_671.[3] <- (b_671.[3] `^` d_619.[4]);
    b_671.[3] <- (VPSHUFB_256 b_671.[3] r8);
    b_671.[4] <- a.[20];
    b_671.[4] <- (b_671.[4] `^` d_619.[0]);
    t_667 <- (VPSLL_4u64 b_671.[4] (W128.of_int 18));
    b_671.[4] <- (VPSRL_4u64 b_671.[4] (W128.of_int 46));
    b_671.[4] <- (b_671.[4] `|` t_667);
    t_672 <- (VPANDN_256 b_671.[1] b_671.[2]);
    t_673 <- (t_672 `^` b_671.[0]);
    e.[10] <- t_673;
    t_674 <- (VPANDN_256 b_671.[2] b_671.[3]);
    t_675 <- (t_674 `^` b_671.[1]);
    e.[11] <- t_675;
    t_676 <- (VPANDN_256 b_671.[3] b_671.[4]);
    t_677 <- (t_676 `^` b_671.[2]);
    e.[12] <- t_677;
    t_678 <- (VPANDN_256 b_671.[4] b_671.[0]);
    t_679 <- (t_678 `^` b_671.[3]);
    e.[13] <- t_679;
    t_680 <- (VPANDN_256 b_671.[0] b_671.[1]);
    t_681 <- (t_680 `^` b_671.[4]);
    e.[14] <- t_681;
    b_704.[0] <- a.[4];
    b_704.[0] <- (b_704.[0] `^` d_619.[4]);
    t_688 <- (VPSLL_4u64 b_704.[0] (W128.of_int 27));
    b_704.[0] <- (VPSRL_4u64 b_704.[0] (W128.of_int 37));
    b_704.[0] <- (b_704.[0] `|` t_688);
    b_704.[1] <- a.[5];
    b_704.[1] <- (b_704.[1] `^` d_619.[0]);
    t_691 <- (VPSLL_4u64 b_704.[1] (W128.of_int 36));
    b_704.[1] <- (VPSRL_4u64 b_704.[1] (W128.of_int 28));
    b_704.[1] <- (b_704.[1] `|` t_691);
    b_704.[2] <- a.[11];
    b_704.[2] <- (b_704.[2] `^` d_619.[1]);
    t_694 <- (VPSLL_4u64 b_704.[2] (W128.of_int 10));
    b_704.[2] <- (VPSRL_4u64 b_704.[2] (W128.of_int 54));
    b_704.[2] <- (b_704.[2] `|` t_694);
    b_704.[3] <- a.[17];
    b_704.[3] <- (b_704.[3] `^` d_619.[2]);
    t_697 <- (VPSLL_4u64 b_704.[3] (W128.of_int 15));
    b_704.[3] <- (VPSRL_4u64 b_704.[3] (W128.of_int 49));
    b_704.[3] <- (b_704.[3] `|` t_697);
    b_704.[4] <- a.[23];
    b_704.[4] <- (b_704.[4] `^` d_619.[3]);
    b_704.[4] <- (VPSHUFB_256 b_704.[4] r56);
    t_705 <- (VPANDN_256 b_704.[1] b_704.[2]);
    t_706 <- (t_705 `^` b_704.[0]);
    e.[15] <- t_706;
    t_707 <- (VPANDN_256 b_704.[2] b_704.[3]);
    t_708 <- (t_707 `^` b_704.[1]);
    e.[16] <- t_708;
    t_709 <- (VPANDN_256 b_704.[3] b_704.[4]);
    t_710 <- (t_709 `^` b_704.[2]);
    e.[17] <- t_710;
    t_711 <- (VPANDN_256 b_704.[4] b_704.[0]);
    t_712 <- (t_711 `^` b_704.[3]);
    e.[18] <- t_712;
    t_713 <- (VPANDN_256 b_704.[0] b_704.[1]);
    t_714 <- (t_713 `^` b_704.[4]);
    e.[19] <- t_714;
    b_736.[0] <- a.[2];
    b_736.[0] <- (b_736.[0] `^` d_619.[2]);
    t_720 <- (VPSLL_4u64 b_736.[0] (W128.of_int 62));
    b_736.[0] <- (VPSRL_4u64 b_736.[0] (W128.of_int 2));
    b_736.[0] <- (b_736.[0] `|` t_720);
    b_736.[1] <- a.[8];
    b_736.[1] <- (b_736.[1] `^` d_619.[3]);
    t_723 <- (VPSLL_4u64 b_736.[1] (W128.of_int 55));
    b_736.[1] <- (VPSRL_4u64 b_736.[1] (W128.of_int 9));
    b_736.[1] <- (b_736.[1] `|` t_723);
    b_736.[2] <- a.[14];
    b_736.[2] <- (b_736.[2] `^` d_619.[4]);
    t_726 <- (VPSLL_4u64 b_736.[2] (W128.of_int 39));
    b_736.[2] <- (VPSRL_4u64 b_736.[2] (W128.of_int 25));
    b_736.[2] <- (b_736.[2] `|` t_726);
    b_736.[3] <- a.[15];
    b_736.[3] <- (b_736.[3] `^` d_619.[0]);
    t_729 <- (VPSLL_4u64 b_736.[3] (W128.of_int 41));
    b_736.[3] <- (VPSRL_4u64 b_736.[3] (W128.of_int 23));
    b_736.[3] <- (b_736.[3] `|` t_729);
    b_736.[4] <- a.[21];
    b_736.[4] <- (b_736.[4] `^` d_619.[1]);
    t_732 <- (VPSLL_4u64 b_736.[4] (W128.of_int 2));
    b_736.[4] <- (VPSRL_4u64 b_736.[4] (W128.of_int 62));
    b_736.[4] <- (b_736.[4] `|` t_732);
    t_737 <- (VPANDN_256 b_736.[1] b_736.[2]);
    t_738 <- (t_737 `^` b_736.[0]);
    e.[20] <- t_738;
    t_739 <- (VPANDN_256 b_736.[2] b_736.[3]);
    t_740 <- (t_739 `^` b_736.[1]);
    e.[21] <- t_740;
    t_741 <- (VPANDN_256 b_736.[3] b_736.[4]);
    t_742 <- (t_741 `^` b_736.[2]);
    e.[22] <- t_742;
    t_743 <- (VPANDN_256 b_736.[4] b_736.[0]);
    t_744 <- (t_743 `^` b_736.[3]);
    e.[23] <- t_744;
    t_745 <- (VPANDN_256 b_736.[0] b_736.[1]);
    t_746 <- (t_745 `^` b_736.[4]);
    e.[24] <- t_746;
    return e;
  }
  proc __keccakf1600_avx2x4_orig (a:W256.t Array25.t) : W256.t Array25.t = {
    var rC:W64.t Array24.t;
    var s_e:W256.t Array25.t;
    var e:W256.t Array25.t;
    var r8:W256.t;
    var r56:W256.t;
    var rc:W256.t;
    var t:W256.t;
    var c:int;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    rC <- kECCAK1600_RC;
    e <- s_e;
    r8 <- rOL8.[0];
    r56 <- rOL56.[0];
    c <- 0;
    while ((c < 24)) {
      rc <- (VPBROADCAST_4u64 rC.[c]);
      e <@ _keccakf1600_4x_pround (e, a, r8, r56);
      t <- (rc `^` e.[0]);
      e.[0] <- t;
      (a, e) <- (swap_ e a);
      rc <- (VPBROADCAST_4u64 rC.[(c + 1)]);
      a <@ _keccakf1600_4x_pround (a, e, r8, r56);
      t <- (rc `^` a.[0]);
      a.[0] <- t;
      (a, e) <- (swap_ e a);
      c <- (c + 2);
    }
    return a;
  }
  proc __keccakf1600_4x_pround_unpacked (st0:W64.t Array25.t,
                                         st1:W64.t Array25.t,
                                         st2:W64.t Array25.t,
                                         st3:W64.t Array25.t) : W64.t Array25.t *
                                                                W64.t Array25.t *
                                                                W64.t Array25.t *
                                                                W64.t Array25.t = {
    var r8:W256.t;
    var r56:W256.t;
    var st4x1:W256.t Array25.t;
    var st4x2:W256.t Array25.t;
    st4x1 <- witness;
    st4x2 <- witness;
    r8 <- rOL8.[0];
    r56 <- rOL56.[0];
    st4x1 <@ __st4x_pack (st4x1, st0, st1, st2, st3);
    st4x2 <@ _keccakf1600_4x_pround (st4x2, st4x1, r8, r56);
    (st0, st1, st2, st3) <@ __st4x_unpack (st0, st1, st2, st3, st4x2);
    return (st0, st1, st2, st3);
  }
  proc __keccakf1600_4x_pround_equiv (e:W256.t Array25.t, a:W256.t Array25.t) : 
  W256.t Array25.t = {
    var st0:W64.t Array25.t;
    var st1:W64.t Array25.t;
    var st2:W64.t Array25.t;
    var st3:W64.t Array25.t;
    st0 <- witness;
    st1 <- witness;
    st2 <- witness;
    st3 <- witness;
    (st0, st1, st2, st3) <@ __st4x_unpack (st0, st1, st2, st3, a);
    (st0, st1, st2, st3) <@ __keccakf1600_4x_pround_unpacked (st0, st1, 
    st2, st3);
    e <@ __st4x_pack (e, st0, st1, st2, st3);
    return e;
  }
  proc __rol_4u64_rho56 (a:W256.t) : W256.t = {
    var r:W256.t;
    r <- (VPSHUFB_256 a rOL56.[0]);
    return r;
  }
  proc __rol_4u64_rho8 (a:W256.t) : W256.t = {
    var r:W256.t;
    r <- (VPSHUFB_256 a rOL8.[0]);
    return r;
  }
  proc __rol_4u64 (a:W256.t, o:int) : W256.t = {
    var r:W256.t;
    var t256:W256.t;
    r <- (VPSLL_4u64 a (W128.of_int o));
    t256 <- (VPSRL_4u64 a (W128.of_int (64 - o)));
    r <- (r `|` t256);
    return r;
  }
  proc __prepare_theta (a_4x:W256.t Array25.t) : W256.t * W256.t * W256.t *
                                                 W256.t * W256.t = {
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    ca <- a_4x.[20];
    ca <- (ca `^` a_4x.[15]);
    ca <- (ca `^` a_4x.[10]);
    ca <- (ca `^` a_4x.[5]);
    ca <- (ca `^` a_4x.[0]);
    ce <- a_4x.[21];
    ce <- (ce `^` a_4x.[16]);
    ce <- (ce `^` a_4x.[11]);
    ce <- (ce `^` a_4x.[6]);
    ce <- (ce `^` a_4x.[1]);
    ci <- a_4x.[22];
    ci <- (ci `^` a_4x.[17]);
    ci <- (ci `^` a_4x.[12]);
    ci <- (ci `^` a_4x.[7]);
    ci <- (ci `^` a_4x.[2]);
    co <- a_4x.[23];
    co <- (co `^` a_4x.[18]);
    co <- (co `^` a_4x.[13]);
    co <- (co `^` a_4x.[8]);
    co <- (co `^` a_4x.[3]);
    cu <- a_4x.[24];
    cu <- (cu `^` a_4x.[19]);
    cu <- (cu `^` a_4x.[14]);
    cu <- (cu `^` a_4x.[9]);
    cu <- (cu `^` a_4x.[4]);
    return (ca, ce, ci, co, cu);
  }
  proc __first (ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    var ce1:W256.t;
    var ci1:W256.t;
    var co1:W256.t;
    var cu1:W256.t;
    var ca1:W256.t;
    ce1 <@ __rol_4u64 (ce, 1);
    da <- (cu `^` ce1);
    ci1 <@ __rol_4u64 (ci, 1);
    de <- (ca `^` ci1);
    co1 <@ __rol_4u64 (co, 1);
    di <- (ce `^` co1);
    cu1 <@ __rol_4u64 (cu, 1);
    do_0 <- (ci `^` cu1);
    ca1 <@ __rol_4u64 (ca, 1);
    du <- (co `^` ca1);
    return (da, de, di, do_0, du);
  }
  proc __second_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      rc_index:W256.t, ca:W256.t, ce:W256.t, ci:W256.t,
                      co:W256.t, cu:W256.t, da:W256.t, de:W256.t, di:W256.t,
                      do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                W256.t Array25.t * W256.t *
                                                W256.t * W256.t * W256.t *
                                                W256.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` rc_index);
    e_4x.[0] <- t256;
    ca <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    ce <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    ci <- t256;
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    co <- t256;
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __third_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fourth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fifth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __sixth_even (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __second_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                     rc_index:W256.t, ca:W256.t, ce:W256.t, ci:W256.t,
                     co:W256.t, cu:W256.t, da:W256.t, de:W256.t, di:W256.t,
                     do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                               W256.t Array25.t * W256.t *
                                               W256.t * W256.t * W256.t *
                                               W256.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` rc_index);
    e_4x.[0] <- t256;
    ca <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    ce <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    ci <- t256;
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    co <- t256;
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __third_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fourth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fifth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __sixth_odd (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, ca:W256.t,
                    ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                    de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                                    W256.t Array25.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t *
                                                                    W256.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    ca <- (ca `^` t256);
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    ce <- (ce `^` t256);
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __second_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      rc_index:W256.t, da:W256.t, de:W256.t, di:W256.t,
                      do_0:W256.t, du:W256.t) : W256.t Array25.t *
                                                W256.t Array25.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- a_4x.[0];
    t256 <- (t256 `^` da);
    a_4x.[0] <- t256;
    bba <- t256;
    t256 <- a_4x.[6];
    t256 <- (t256 `^` de);
    a_4x.[6] <- t256;
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- a_4x.[12];
    t256 <- (t256 `^` di);
    a_4x.[12] <- t256;
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` rc_index);
    e_4x.[0] <- t256;
    t256 <- a_4x.[18];
    t256 <- (t256 `^` do_0);
    a_4x.[18] <- t256;
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x.[1] <- t256;
    t256 <- a_4x.[24];
    t256 <- (t256 `^` du);
    a_4x.[24] <- t256;
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x.[2] <- t256;
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x.[3] <- t256;
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x.[4] <- t256;
    return (a_4x, e_4x);
  }
  proc __third_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- a_4x.[3];
    t256 <- (t256 `^` do_0);
    a_4x.[3] <- t256;
    bga <@ __rol_4u64 (t256, 28);
    t256 <- a_4x.[9];
    t256 <- (t256 `^` du);
    a_4x.[9] <- t256;
    bge <@ __rol_4u64 (t256, 20);
    t256 <- a_4x.[10];
    t256 <- (t256 `^` da);
    a_4x.[10] <- t256;
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x.[5] <- t256;
    t256 <- a_4x.[16];
    t256 <- (t256 `^` de);
    a_4x.[16] <- t256;
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x.[6] <- t256;
    t256 <- a_4x.[22];
    t256 <- (t256 `^` di);
    a_4x.[22] <- t256;
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x.[7] <- t256;
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x.[8] <- t256;
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x.[9] <- t256;
    return (a_4x, e_4x);
  }
  proc __fourth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- a_4x.[1];
    t256 <- (t256 `^` de);
    a_4x.[1] <- t256;
    bka <@ __rol_4u64 (t256, 1);
    t256 <- a_4x.[7];
    t256 <- (t256 `^` di);
    a_4x.[7] <- t256;
    bke <@ __rol_4u64 (t256, 6);
    t256 <- a_4x.[13];
    t256 <- (t256 `^` do_0);
    a_4x.[13] <- t256;
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x.[10] <- t256;
    t256 <- a_4x.[19];
    t256 <- (t256 `^` du);
    a_4x.[19] <- t256;
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x.[11] <- t256;
    t256 <- a_4x.[20];
    t256 <- (t256 `^` da);
    a_4x.[20] <- t256;
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x.[12] <- t256;
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x.[13] <- t256;
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x.[14] <- t256;
    return (a_4x, e_4x);
  }
  proc __fifth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- a_4x.[4];
    t256 <- (t256 `^` du);
    a_4x.[4] <- t256;
    bma <@ __rol_4u64 (t256, 27);
    t256 <- a_4x.[5];
    t256 <- (t256 `^` da);
    a_4x.[5] <- t256;
    bme <@ __rol_4u64 (t256, 36);
    t256 <- a_4x.[11];
    t256 <- (t256 `^` de);
    a_4x.[11] <- t256;
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x.[15] <- t256;
    t256 <- a_4x.[17];
    t256 <- (t256 `^` di);
    a_4x.[17] <- t256;
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x.[16] <- t256;
    t256 <- a_4x.[23];
    t256 <- (t256 `^` do_0);
    a_4x.[23] <- t256;
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x.[17] <- t256;
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x.[18] <- t256;
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x.[19] <- t256;
    return (a_4x, e_4x);
  }
  proc __sixth_last (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  W256.t Array25.t * W256.t Array25.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- a_4x.[2];
    t256 <- (t256 `^` di);
    a_4x.[2] <- t256;
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- a_4x.[8];
    t256 <- (t256 `^` do_0);
    a_4x.[8] <- t256;
    bse <@ __rol_4u64 (t256, 55);
    t256 <- a_4x.[14];
    t256 <- (t256 `^` du);
    a_4x.[14] <- t256;
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x.[20] <- t256;
    t256 <- a_4x.[15];
    t256 <- (t256 `^` da);
    a_4x.[15] <- t256;
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x.[21] <- t256;
    t256 <- a_4x.[21];
    t256 <- (t256 `^` de);
    a_4x.[21] <- t256;
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x.[22] <- t256;
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x.[23] <- t256;
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x.[24] <- t256;
    return (a_4x, e_4x);
  }
  proc _theta_rho_pi_chi_iota_prepare_theta_even (a_4x:W256.t Array25.t,
                                                  e_4x:W256.t Array25.t,
                                                  rc_index:W256.t, ca:W256.t,
                                                  ce:W256.t, ci:W256.t,
                                                  co:W256.t, cu:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_even (a_4x, e_4x, rc_index,
    ca, ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc _theta_rho_pi_chi_iota_prepare_theta_odd (a_4x:W256.t Array25.t,
                                                 e_4x:W256.t Array25.t,
                                                 rc_index:W256.t, ca:W256.t,
                                                 ce:W256.t, ci:W256.t,
                                                 co:W256.t, cu:W256.t) : 
  W256.t Array25.t * W256.t Array25.t * W256.t * W256.t * W256.t * W256.t *
  W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_odd (a_4x, e_4x, rc_index,
    ca, ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __theta_rho_pi_chi_iota (a_4x:W256.t Array25.t, e_4x:W256.t Array25.t,
                                rc_index:W256.t, ca:W256.t, ce:W256.t,
                                ci:W256.t, co:W256.t, cu:W256.t) : W256.t Array25.t *
                                                                   W256.t Array25.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x) <@ __second_last (a_4x, e_4x, rc_index, da, de, di, 
    do_0, du);
    (a_4x, e_4x) <@ __third_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fourth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fifth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __sixth_last (a_4x, e_4x, da, de, di, do_0, du);
    return (a_4x, e_4x);
  }
  proc __keccakf1600_avx2x4_alt (a_4x:W256.t Array25.t) : W256.t Array25.t = {
    var rC:W64.t Array24.t;
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    var rc_index:W256.t;
    var e_4x:W256.t Array25.t;
    e_4x <- witness;
    rC <- witness;
    rC <- kECCAK1600_RC;
    (ca, ce, ci, co, cu) <@ __prepare_theta (a_4x);
    rc_index <- (VPBROADCAST_4u64 rC.[0]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[1]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[2]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[3]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[4]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[5]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[6]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[7]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[8]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[9]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[10]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[11]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[12]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[13]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[14]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[15]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[16]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[17]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[18]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[19]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[20]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[21]);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[22]);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ _theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, rc_index, ca, ce, ci, co, cu);
    rc_index <- (VPBROADCAST_4u64 rC.[23]);
    (e_4x, a_4x) <@ __theta_rho_pi_chi_iota (e_4x, a_4x, rc_index, ca, 
    ce, ci, co, cu);
    return a_4x;
  }
  proc __f1600_loopbody_native (st:W256.t Array25.t, rol8:W256.t Array1.t,
                                rol56:W256.t Array1.t, rC:W64.t Array24.t,
                                i:int, y10:W256.t, y14:W256.t, y8:W256.t,
                                y15:W256.t, y9:W256.t, y13:W256.t, y3:W256.t,
                                y7:W256.t, y2:W256.t) : W256.t Array25.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t * W256.t *
                                                        W256.t = {
    var i0:int;
    var i1:int;
    var i2:int;
    var i3:int;
    var i4:int;
    var i5:int;
    var i6:int;
    var i7:int;
    var i8:int;
    var i9:int;
    var i10:int;
    var i11:int;
    var i12:int;
    var i13:int;
    var i14:int;
    var i15:int;
    var i16:int;
    var i17:int;
    var i18:int;
    var i19:int;
    var i20:int;
    var i21:int;
    var i22:int;
    var i23:int;
    var y4:W256.t;
    var y0:W256.t;
    var y11:W256.t;
    var y12:W256.t;
    var y1:W256.t;
    var y6:W256.t;
    var y5:W256.t;
    i0 <- 0;
    i1 <- 1;
    i2 <- 2;
    i3 <- 3;
    i4 <- 4;
    i5 <- 5;
    i6 <- 6;
    i7 <- 9;
    i8 <- 10;
    i9 <- 13;
    i10 <- 14;
    i11 <- 16;
    i12 <- 17;
    i13 <- 19;
    i14 <- 20;
    i15 <- 23;
    i16 <- 7;
    i17 <- 8;
    i18 <- 11;
    i19 <- 12;
    i20 <- 15;
    i21 <- 18;
    i22 <- 21;
    i23 <- 22;
    y4 <- st.[i5];
    y0 <- (y9 `^` st.[i14]);
    st.[i16] <- y9;
    y9 <- y10;
    y11 <- st.[i6];
    y12 <- st.[i11];
    st.[i18] <- y3;
    y1 <- (y4 `^` st.[i8]);
    y10 <- st.[i2];
    st.[i17] <- y4;
    y12 <- (y12 `^` y3);
    y6 <- st.[i1];
    y4 <- st.[i10];
    st.[i21] <- y14;
    y0 <- (y0 `^` y1);
    y1 <- (y11 `^` y8);
    y11 <- (y7 `^` st.[i12]);
    st.[i20] <- y10;
    y12 <- (y12 `^` y1);
    y1 <- (y9 `^` y15);
    y3 <- st.[i7];
    st.[i19] <- y8;
    y11 <- (y11 `^` y1);
    y1 <- (y14 `^` st.[i9]);
    y12 <- (y12 `^` y6);
    y8 <- st.[i3];
    y11 <- (y11 `^` y10);
    y10 <- (y13 `^` st.[i15]);
    y3 <- (y3 `^` y4);
    st.[i22] <- y4;
    y4 <- (VPSRL_4u64 y12 (W128.of_int 63));
    y5 <- (VPSRL_4u64 y11 (W128.of_int 63));
    y0 <- (y0 `^` st.[i0]);
    y10 <- (y10 `^` y1);
    y1 <- st.[i4];
    y10 <- (y10 `^` y8);
    y14 <- y1;
    y1 <- (y2 `^` st.[i13]);
    st.[i23] <- y14;
    y1 <- (y1 `^` y3);
    y3 <- (VPSLL_4u64 y12 (W128.of_int 1));
    y3 <- (y3 `|` y4);
    y4 <- (VPSLL_4u64 y11 (W128.of_int 1));
    y1 <- (y1 `^` y14);
    y4 <- (y4 `|` y5);
    y14 <- (VPSRL_4u64 y10 (W128.of_int 63));
    y3 <- (y3 `^` y1);
    y5 <- (VPSLL_4u64 y10 (W128.of_int 1));
    y4 <- (y4 `^` y0);
    y5 <- (y5 `|` y14);
    y6 <- (y4 `^` y6);
    y5 <- (y5 `^` y12);
    y12 <- (VPSRL_4u64 y1 (W128.of_int 63));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 1));
    y7 <- (y5 `^` y7);
    y9 <- (y5 `^` y9);
    y1 <- (y1 `|` y12);
    y12 <- (y3 `^` st.[i0]);
    y1 <- (y1 `^` y11);
    y11 <- (VPSRL_4u64 y0 (W128.of_int 63));
    y0 <- (VPSLL_4u64 y0 (W128.of_int 1));
    y13 <- (y1 `^` y13);
    y8 <- (y1 `^` y8);
    y0 <- (y0 `|` y11);
    y0 <- (y0 `^` y10);
    y10 <- (y4 `^` st.[i6]);
    y2 <- (y0 `^` y2);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 20));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 44));
    y10 <- (y10 `|` y11);
    y11 <- (y5 `^` y15);
    y15 <- (VPBROADCAST_4u64 rC.[(W64.to_uint (W64.of_int i))]);
    y14 <- (VPSRL_4u64 y11 (W128.of_int 21));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 43));
    y11 <- (y11 `|` y14);
    y14 <- ((invw y10) `&` y11);
    y14 <- (y14 `^` y15);
    y15 <- (y14 `^` y12);
    y14 <- (VPSRL_4u64 y13 (W128.of_int 43));
    y13 <- (VPSLL_4u64 y13 (W128.of_int 21));
    st.[i0] <- y15;
    y13 <- (y13 `|` y14);
    y14 <- ((invw y11) `&` y13);
    y15 <- (y14 `^` y10);
    y14 <- (VPSRL_4u64 y2 (W128.of_int 50));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 14));
    st.[i1] <- y15;
    y2 <- (y2 `|` y14);
    y14 <- ((invw y13) `&` y2);
    y11 <- (y14 `^` y11);
    st.[i2] <- y11;
    y11 <- ((invw y2) `&` y12);
    y12 <- ((invw y12) `&` y10);
    y11 <- (y11 `^` y13);
    st.[i3] <- y11;
    y11 <- (y12 `^` y2);
    y2 <- (VPSRL_4u64 y8 (W128.of_int 36));
    y8 <- (VPSLL_4u64 y8 (W128.of_int 28));
    st.[i4] <- y11;
    y8 <- (y8 `|` y2);
    y2 <- (y0 `^` st.[i7]);
    y10 <- (VPSRL_4u64 y2 (W128.of_int 44));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 20));
    y2 <- (y2 `|` y10);
    y10 <- (y3 `^` st.[i8]);
    y11 <- (VPSRL_4u64 y10 (W128.of_int 61));
    y10 <- (VPSLL_4u64 y10 (W128.of_int 3));
    y10 <- (y10 `|` y11);
    y11 <- ((invw y2) `&` y10);
    y11 <- (y11 `^` y8);
    st.[i5] <- y11;
    y11 <- (y4 `^` st.[i11]);
    y12 <- (VPSRL_4u64 y11 (W128.of_int 19));
    y11 <- (VPSLL_4u64 y11 (W128.of_int 45));
    y11 <- (y11 `|` y12);
    y12 <- ((invw y10) `&` y11);
    y12 <- (y12 `^` y2);
    st.[i6] <- y12;
    y12 <- (VPSRL_4u64 y7 (W128.of_int 3));
    y7 <- (VPSLL_4u64 y7 (W128.of_int 61));
    y7 <- (y7 `|` y12);
    y12 <- ((invw y11) `&` y7);
    y10 <- (y12 `^` y10);
    y12 <- ((invw y7) `&` y8);
    y8 <- ((invw y8) `&` y2);
    y2 <- (VPSRL_4u64 y6 (W128.of_int 63));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 1));
    y14 <- (y12 `^` y11);
    y6 <- (y6 `|` y2);
    y2 <- (VPSRL_4u64 y9 (W128.of_int 58));
    y12 <- (y8 `^` y7);
    y9 <- (VPSLL_4u64 y9 (W128.of_int 6));
    st.[i7] <- y12;
    y7 <- (y0 `^` st.[i13]);
    y9 <- (y9 `|` y2);
    y2 <- (y1 `^` st.[i9]);
    y7 <- (VPSHUFB_256 y7 rol8.[0]);
    y11 <- (VPSRL_4u64 y2 (W128.of_int 39));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 25));
    y11 <- (y11 `|` y2);
    y2 <- ((invw y9) `&` y11);
    y8 <- ((invw y11) `&` y7);
    y12 <- (y2 `^` y6);
    y2 <- (y3 `^` st.[i14]);
    y8 <- (y8 `^` y9);
    st.[i8] <- y12;
    y12 <- (VPSRL_4u64 y2 (W128.of_int 46));
    y2 <- (VPSLL_4u64 y2 (W128.of_int 18));
    y2 <- (y12 `|` y2);
    y12 <- ((invw y7) `&` y2);
    y15 <- (y12 `^` y11);
    y11 <- ((invw y2) `&` y6);
    y6 <- ((invw y6) `&` y9);
    y12 <- (y11 `^` y7);
    st.[i9] <- y12;
    y12 <- (y6 `^` y2);
    y6 <- (y0 `^` st.[i23]);
    y0 <- (y0 `^` st.[i22]);
    st.[i10] <- y12;
    y2 <- (VPSRL_4u64 y6 (W128.of_int 37));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 27));
    y2 <- (y2 `|` y6);
    y6 <- (y3 `^` st.[i17]);
    y3 <- (y3 `^` st.[i16]);
    y7 <- (VPSRL_4u64 y6 (W128.of_int 28));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 36));
    y7 <- (y7 `|` y6);
    y6 <- (y4 `^` st.[i19]);
    y4 <- (y4 `^` st.[i18]);
    y12 <- (VPSRL_4u64 y6 (W128.of_int 54));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 10));
    y12 <- (y12 `|` y6);
    y6 <- (y5 `^` st.[i12]);
    y5 <- (y5 `^` st.[i20]);
    y9 <- ((invw y7) `&` y12);
    y11 <- (VPSRL_4u64 y6 (W128.of_int 49));
    y6 <- (VPSLL_4u64 y6 (W128.of_int 15));
    y9 <- (y9 `^` y2);
    y11 <- (y11 `|` y6);
    y6 <- ((invw y12) `&` y11);
    y6 <- (y6 `^` y7);
    st.[i11] <- y6;
    y6 <- (y1 `^` st.[i15]);
    y1 <- (y1 `^` st.[i21]);
    y6 <- (VPSHUFB_256 y6 rol56.[0]);
    y13 <- ((invw y11) `&` y6);
    y13 <- (y13 `^` y12);
    st.[i12] <- y13;
    y13 <- ((invw y6) `&` y2);
    y2 <- ((invw y2) `&` y7);
    y2 <- (y2 `^` y6);
    y6 <- (VPSRL_4u64 y4 (W128.of_int 62));
    y13 <- (y13 `^` y11);
    st.[i13] <- y2;
    y2 <- (VPSRL_4u64 y5 (W128.of_int 2));
    y5 <- (VPSLL_4u64 y5 (W128.of_int 62));
    y2 <- (y2 `|` y5);
    y5 <- (VPSRL_4u64 y1 (W128.of_int 9));
    y1 <- (VPSLL_4u64 y1 (W128.of_int 55));
    y4 <- (VPSLL_4u64 y4 (W128.of_int 2));
    y1 <- (y5 `|` y1);
    y5 <- (VPSRL_4u64 y0 (W128.of_int 25));
    y4 <- (y6 `|` y4);
    y0 <- (VPSLL_4u64 y0 (W128.of_int 39));
    y5 <- (y5 `|` y0);
    y0 <- ((invw y1) `&` y5);
    y0 <- (y0 `^` y2);
    st.[i14] <- y0;
    y0 <- (VPSRL_4u64 y3 (W128.of_int 23));
    y3 <- (VPSLL_4u64 y3 (W128.of_int 41));
    y0 <- (y0 `|` y3);
    y7 <- ((invw y0) `&` y4);
    y3 <- ((invw y5) `&` y0);
    y7 <- (y7 `^` y5);
    y5 <- ((invw y4) `&` y2);
    y2 <- ((invw y2) `&` y1);
    y5 <- (y5 `^` y0);
    y3 <- (y3 `^` y1);
    y2 <- (y2 `^` y4);
    st.[i15] <- y5;
    return (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
  }
  proc __regs_fetch (st:W256.t Array25.t) : W256.t * W256.t * W256.t *
                                            W256.t * W256.t * W256.t *
                                            W256.t * W256.t * W256.t = {
    var y10:W256.t;
    var y14:W256.t;
    var y8:W256.t;
    var y15:W256.t;
    var y9:W256.t;
    var y13:W256.t;
    var y3:W256.t;
    var y7:W256.t;
    var y2:W256.t;
    y10 <- st.[7];
    y14 <- st.[8];
    y8 <- st.[11];
    y15 <- st.[12];
    y9 <- st.[15];
    y13 <- st.[18];
    y3 <- st.[21];
    y7 <- st.[22];
    y2 <- st.[24];
    return (y10, y14, y8, y15, y9, y13, y3, y7, y2);
  }
  proc __regs_unfetch (st:W256.t Array25.t, y10:W256.t, y14:W256.t,
                       y8:W256.t, y15:W256.t, y9:W256.t, y13:W256.t,
                       y3:W256.t, y7:W256.t, y2:W256.t) : W256.t Array25.t = {
    
    st.[7] <- y10;
    st.[8] <- y14;
    st.[11] <- y8;
    st.[12] <- y15;
    st.[15] <- y9;
    st.[18] <- y13;
    st.[21] <- y3;
    st.[22] <- y7;
    st.[24] <- y2;
    return st;
  }
  proc test_keccakf1600x4_native (st:W256.t Array25.t, c:W64.t) : W256.t Array25.t = {
    var y10:W256.t;
    var y14:W256.t;
    var y8:W256.t;
    var y15:W256.t;
    var y9:W256.t;
    var y13:W256.t;
    var y3:W256.t;
    var y7:W256.t;
    var y2:W256.t;
    var rol8:W256.t Array1.t;
    var rol56:W256.t Array1.t;
    var rc:W64.t Array24.t;
    rc <- witness;
    rol56 <- witness;
    rol8 <- witness;
    (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __regs_fetch (st);
    rol8 <- rOL8;
    rol56 <- rOL56;
    rc <- kECCAK1600_RC;
    (st, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __f1600_loopbody_native (
    st, rol8, rol56, rc, (W64.to_uint c), y10, y14, y8, y15, y9, y13, 
    y3, y7, y2);
    st <@ __regs_unfetch (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
    return st;
  }
  proc __keccakf1600_avx2x4_native (st:W256.t Array25.t) : W256.t Array25.t = {
    var y10:W256.t;
    var y14:W256.t;
    var y8:W256.t;
    var y15:W256.t;
    var y9:W256.t;
    var y13:W256.t;
    var y3:W256.t;
    var y7:W256.t;
    var y2:W256.t;
    var rol8:W256.t Array1.t;
    var rol56:W256.t Array1.t;
    var rc:W64.t Array24.t;
    var i:int;
    rc <- witness;
    rol56 <- witness;
    rol8 <- witness;
    (y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __regs_fetch (st);
    rol8 <- rOL8;
    rol56 <- rOL56;
    rc <- kECCAK1600_RC;
    i <- 0;
    (st, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __f1600_loopbody_native (
    st, rol8, rol56, rc, i, y10, y14, y8, y15, y9, y13, y3, y7, y2);
    i <- (i + 1);
    while ((i < 24)) {
      (st, y10, y14, y8, y15, y9, y13, y3, y7, y2) <@ __f1600_loopbody_native (
      st, rol8, rol56, rc, i, y10, y14, y8, y15, y9, y13, y3, y7, y2);
      i <- (i + 1);
    }
    st <@ __regs_unfetch (st, y10, y14, y8, y15, y9, y13, y3, y7, y2);
    return st;
  }
  proc __keccakf1600_avx2x4 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    a <@ __keccakf1600_avx2x4_native (a);
    return a;
  }
  proc _keccakf1600_avx2x4 (a:W256.t Array25.t) : W256.t Array25.t = {
    
    a <@ __keccakf1600_avx2x4 (a);
    return a;
  }
  proc _keccakf1600_avx2x4_ (a:W256.t Array25.t) : W256.t Array25.t = {
    
    a <- a;
    a <@ _keccakf1600_avx2x4 (a);
    a <- a;
    return a;
  }
  proc __state_init_avx2x4 (st:W256.t Array25.t) : W256.t Array25.t = {
    var z256:W256.t;
    var i:int;
    z256 <- (set0_256);
    i <- 0;
    while ((i < (32 * 25))) {
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i_0 => st.[i_0])) 
      i z256)));
      i <- (i + 32);
    }
    return st;
  }
  proc __addratebit_avx2x4 (st:W256.t Array25.t, rATE8:int) : W256.t Array25.t = {
    var t64:W64.t;
    var t128:W128.t;
    var t256:W256.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE8) - 1) %% 64)));
    t128 <- (VMOV_64 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    t256 <- (t256 `^` st.[((rATE8 - 1) %/ 8)]);
    st.[((rATE8 - 1) %/ 8)] <- t256;
    return st;
  }
  proc __addstate_m_bcast_avx2x4 (st:W256.t Array25.t, aT:int, buf:int,
                                  _LEN:int, _TRAILB:int) : W256.t Array25.t *
                                                           int = {
    var aT8:int;
    var w:W256.t;
    var at:int;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (buf, _LEN, _TRAILB, aT8, w) <@ __m_ilen_read_bcast_upto8_at (buf,
      _LEN, _TRAILB, aT, aT8);
      w <- (w `^` st.[(aT %/ 8)]);
      st.[(aT %/ 8)] <- w;
      aT <- aT8;
    } else {
      
    }
    at <- (32 * (aT %/ 8));
    while ((at < (32 * ((aT %/ 8) + (_LEN %/ 8))))) {
      w <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
      buf <- (buf + 8);
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
      (buf, _LEN, _TRAILB, aT, w) <@ __m_ilen_read_bcast_upto8_at (buf, 
      _LEN, _TRAILB, aT, aT);
      w <- (w `^` (get256_direct (WArray800.init256 (fun i => st.[i])) at));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) at w)));
    } else {
      
    }
    return (st, aT);
  }
  proc __absorb_m_bcast_avx2x4 (st:W256.t Array25.t, aT:int, buf:int,
                                _LEN:int, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var iTERS:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0) <@ __addstate_m_bcast_avx2x4 (st, aT, buf, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1) <@ __addstate_m_bcast_avx2x4 (st, 0, buf, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT) <@ __addstate_m_bcast_avx2x4 (st, aT, buf, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __addstate_m_avx2x4 (st:W256.t Array25.t, aT:int, buf0:int, buf1:int,
                            buf2:int, buf3:int, _LEN:int, _TRAILB:int) : 
  W256.t Array25.t * int * int * int * int * int = {
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
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (buf0,  _0,  _1,  _2, t0) <@ __m_ilen_read_upto8_at (buf0, _LEN,
      _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 0)) `^`
      t0))));
      (buf1,  _3,  _4,  _5, t1) <@ __m_ilen_read_upto8_at (buf1, _LEN,
      _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 1)) `^`
      t1))));
      (buf2,  _6,  _7,  _8, t2) <@ __m_ilen_read_upto8_at (buf2, _LEN,
      _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 2)) `^`
      t2))));
      (buf3, _LEN, _TRAILB, aT8, t3) <@ __m_ilen_read_upto8_at (buf3, 
      _LEN, _TRAILB, aT, aT8);
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
    at <- (4 * (aT %/ 8));
    while ((at < ((4 * (aT %/ 8)) + (4 * (_LEN %/ 8))))) {
      t0 <- (loadW64 Glob.mem buf0);
      buf0 <- (buf0 + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      t1 <- (loadW64 Glob.mem buf1);
      buf1 <- (buf1 + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      t2 <- (loadW64 Glob.mem buf2);
      buf2 <- (buf2 + 8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      t3 <- (loadW64 Glob.mem buf3);
      buf3 <- (buf3 + 8);
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
      (buf0,  _9,  _10,  _11, t0) <@ __m_ilen_read_upto8_at (buf0, _LEN,
      _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      (buf1,  _12,  _13,  _14, t1) <@ __m_ilen_read_upto8_at (buf1, _LEN,
      _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      (buf2,  _15,  _16,  _17, t2) <@ __m_ilen_read_upto8_at (buf2, _LEN,
      _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      (buf3,  _18,  _19, aT, t3) <@ __m_ilen_read_upto8_at (buf3, _LEN,
      _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 3)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 3)) `^` t3))));
    } else {
      
    }
    return (st, aT, buf0, buf1, buf2, buf3);
  }
  proc __absorb_m_avx2x4 (st:W256.t Array25.t, aT:int, buf0:int, buf1:int,
                          buf2:int, buf3:int, _LEN:int, _TRAILB:int,
                          _RATE8:int) : W256.t Array25.t * int = {
    var iTERS:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, buf0, buf1, buf2, buf3) <@ __addstate_m_avx2x4 (st, aT, 
      buf0, buf1, buf2, buf3, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, buf0, buf1, buf2, buf3) <@ __addstate_m_avx2x4 (st, 0,
        buf0, buf1, buf2, buf3, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2,  _3,  _4,  _5) <@ __addstate_m_avx2x4 (st, aT, buf0, 
    buf1, buf2, buf3, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_m_avx2x4 (buf0:int, buf1:int, buf2:int, buf3:int,
                             _LEN:int, st:W256.t Array25.t) : int * int *
                                                              int * int = {
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
      (x0, x1, x2, x3) <@ __4u64x4_u256x4 (x0, x1, x2, x3);
      Glob.mem <- (storeW256 Glob.mem buf0 x0);
      buf0 <- (buf0 + 32);
      Glob.mem <- (storeW256 Glob.mem buf1 x1);
      buf1 <- (buf1 + 32);
      Glob.mem <- (storeW256 Glob.mem buf2 x2);
      buf2 <- (buf2 + 32);
      Glob.mem <- (storeW256 Glob.mem buf3 x3);
      buf3 <- (buf3 + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      Glob.mem <- (storeW64 Glob.mem (buf0 + i) t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      Glob.mem <- (storeW64 Glob.mem (buf1 + i) t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      Glob.mem <- (storeW64 Glob.mem (buf2 + i) t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      Glob.mem <- (storeW64 Glob.mem (buf3 + i) t3);
      i <- (i + 8);
    }
    buf0 <- (buf0 + i);
    buf1 <- (buf1 + i);
    buf2 <- (buf2 + i);
    buf3 <- (buf3 + i);
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0) <@ __m_ilen_write_upto8 (buf0, (_LEN %% 8), t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _1) <@ __m_ilen_write_upto8 (buf1, (_LEN %% 8), t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _2) <@ __m_ilen_write_upto8 (buf2, (_LEN %% 8), t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _3) <@ __m_ilen_write_upto8 (buf3, (_LEN %% 8), t3);
    } else {
      
    }
    return (buf0, buf1, buf2, buf3);
  }
  proc __squeeze_m_avx2x4 (st:W256.t Array25.t, buf0:int, buf1:int, buf2:int,
                           buf3:int, _LEN:int, _RATE8:int) : W256.t Array25.t = {
    var iTERS:int;
    var lO:int;
    var i:int;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    if ((0 < iTERS)) {
      i <- 0;
      while ((i < iTERS)) {
        st <@ _keccakf1600_avx2x4 (st);
        (buf0, buf1, buf2, buf3) <@ __dumpstate_m_avx2x4 (buf0, buf1, 
        buf2, buf3, _RATE8, st);
        i <- (i + 1);
      }
    } else {
      
    }
    if ((0 < lO)) {
      st <@ _keccakf1600_avx2x4 (st);
      (buf0, buf1, buf2, buf3) <@ __dumpstate_m_avx2x4 (buf0, buf1, buf2,
      buf3, lO, st);
    } else {
      
    }
    return st;
  }
  proc _init_updstate_avx2x4 (st:W64.t Array101.t, r64:int, trailb:W8.t) : 
  W64.t Array101.t = {
    var kst:W256.t Array25.t;
    var status:W64.t;
    var t:W64.t;
    kst <- witness;
    kst <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    kst <@ __state_init_avx2x4 (kst);
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => kst.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    status <- (zeroextu64 trailb);
    status <- (status `<<` (W8.of_int 8));
    r64 <- (W8.to_uint ((W8.of_int r64) - (W8.of_int 1)));
    t <- (zeroextu64 (W8.of_int r64));
    status <- (status + t);
    status <- (status `<<` (W8.of_int 8));
    st.[(4 * 25)] <- status;
    return st;
  }
  proc _ststatus_data_avx2x4 (ststatus:W64.t) : W64.t * int * int = {
    var trailb:W64.t;
    var at:W64.t;
    var r8:W64.t;
    var c_200:W64.t;
    var c_0:W64.t;
    var r8_ui:int;
    var at_ui:int;
    at <- ststatus;
    at <- (at `&` (W64.of_int 255));
    ststatus <- (ststatus `>>` (W8.of_int 8));
    r8 <- ststatus;
    r8 <- (r8 `&` (W64.of_int 255));
    r8 <- (r8 + (W64.of_int 1));
    r8 <- (r8 `<<` (W8.of_int 3));
    c_200 <- (W64.of_int 200);
    r8 <- (((W64.of_int 200) \ult r8) ? c_200 : r8);
    c_0 <- (W64.of_int 0);
    at <- ((r8 \ule at) ? c_0 : at);
    ststatus <- (ststatus `>>` (W8.of_int 8));
    ststatus <- (ststatus `&` (W64.of_int 255));
    trailb <- ststatus;
    r8_ui <- (W64.to_uint r8);
    at_ui <- (W64.to_uint at);
    return (trailb, r8_ui, at_ui);
  }
  proc _finish_updstate_avx2x4 (st:W64.t Array101.t) : W64.t Array101.t = {
    var ststatus:W64.t;
    var trailb:W64.t;
    var t8:W8.t;
    var t128:W128.t;
    var t256:W256.t;
    var rbit:W64.t;
    var r8:int;
    var at:int;
    ststatus <- st.[(4 * 25)];
    (trailb, r8, at) <@ _ststatus_data_avx2x4 (ststatus);
    t8 <- (truncateu8 (W64.of_int at));
    at <- (at `|>>` 3);
    at <- (at `<<` 5);
    t8 <- (t8 `&` (W8.of_int 7));
    t8 <- (t8 `<<` (W8.of_int 3));
    trailb <- (trailb `<<` (t8 `&` (W8.of_int 63)));
    t128 <- (VMOV_64 trailb);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    t256 <-
    (t256 `^` (get256_direct (WArray808.init64 (fun i => st.[i])) at));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set256_direct (WArray808.init64 (fun i => st.[i])) at t256)));
    rbit <- (W64.of_int 1);
    rbit <- (rbit `<<` (W8.of_int 63));
    r8 <- (r8 - 1);
    r8 <- (r8 `|>>` 3);
    r8 <- (r8 `<<` 5);
    t128 <- (VMOV_64 rbit);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    t256 <-
    (t256 `^` (get256_direct (WArray808.init64 (fun i => st.[i])) r8));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set256_direct (WArray808.init64 (fun i => st.[i])) r8 t256)));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set32_direct (WArray808.init64 (fun i => st.[i]))
    ((4 * 8) * 25)
    ((get32_direct (WArray808.init64 (fun i => st.[i])) ((4 * 8) * 25)) `&`
    (W32.of_int 4278255360)))));
    return st;
  }
  proc ststatus_updstate_avx2x4 (status:W8.t Array3.t, st:W64.t Array101.t) : 
  W8.t Array3.t = {
    var ststatus:W64.t;
    var r8:int;
    var at:int;
    var  _0:W64.t;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data_avx2x4 (ststatus);
    status.[0] <- (truncateu8 (W64.of_int r8));
    status.[1] <- (truncateu8 (W64.of_int at));
    status.[2] <-
    (get8_direct (WArray808.init64 (fun i => st.[i])) ((8 * 25) + 2));
    return status;
  }
  proc init_updstate_avx2x4 (st:W64.t Array101.t, r64:int, trailb:W8.t) : 
  W64.t Array101.t = {
    
    st <- st;
    r64 <- r64;
    trailb <- trailb;
    st <@ _init_updstate_avx2x4 (st, r64, trailb);
    return st;
  }
  proc finish_updstate_avx2x4 (st:W64.t Array101.t) : W64.t Array101.t = {
    
    st <- st;
    st <@ _finish_updstate_avx2x4 (st);
    return st;
  }
}.
