require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array6 Array7 Array24 Array25 Array999 WArray40 WArray160 WArray192
WArray200 WArray224 WArray800 WArray999.

abbrev rOL8 =
(W256.of_int
13620818001941277694121380808605999856886653716761013959207994299728839901191
).

abbrev rOL56 =
(W256.of_int
10910488462195273559651782724632284871561478246514020268633800075540923875841
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
    var aT8:int;
    var t16:W64.t;
    var t8:W64.t;
    if ((((aT < cUR) \/ ((cUR + 8) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
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
    var aT16:int;
    var t64_0:W64.t;
    var t64_1:W64.t;
    if ((((aT < cUR) \/ ((cUR + 16) <= aT)) \/ ((lEN = 0) /\ (tRAIL = 0)))) {
      w <- (set0_128);
    } else {
      aT16 <- (aT - cUR);
      if ((16 <= lEN)) {
        w <- (loadW128 Glob.mem buf);
        w <@ __SHLDQ (w, aT16);
        buf <- (buf + (16 - aT16));
        lEN <- (lEN - (16 - aT16));
        aT16 <- 16;
      } else {
        if ((8 <= aT16)) {
          w <- (set0_128);
          (buf, lEN, tRAIL, aT16, t64_1) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, 8, aT16);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        } else {
          (buf, lEN, tRAIL, aT16, t64_0) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, 0, aT16);
          w <- (zeroextu128 t64_0);
          (buf, lEN, tRAIL, aT16, t64_1) <@ __m_ilen_read_upto8_at (buf, 
          lEN, tRAIL, 8, aT16);
          w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
        }
      }
      aT <- (cUR + aT16);
    }
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_upto32_at (buf:int, lEN:int, tRAIL:int, cUR:int, aT:int) : 
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
        w <- (loadW256 Glob.mem buf);
        aT32 <- (aT32 + 32);
        buf <- (buf + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= aT32)) {
          w <- (set0_256);
          (buf, lEN, tRAIL, aT32, t128_1) <@ __m_ilen_read_upto16_at (
          buf, lEN, tRAIL, 16, aT32);
          w <- (VINSERTI128 w t128_1 (W8.of_int 1));
        } else {
          (buf, lEN, tRAIL, aT32, t128_0) <@ __m_ilen_read_upto16_at (
          buf, lEN, tRAIL, 0, aT32);
          (buf, lEN, tRAIL, aT32, t128_1) <@ __m_ilen_read_upto16_at (
          buf, lEN, tRAIL, 16, aT32);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        }
      }
      aT <- (cUR + aT32);
    }
    return (buf, lEN, tRAIL, aT, w);
  }
  proc __m_ilen_read_bcast_upto8_at (buf:int, lEN:int, tRAIL:int, cUR:int,
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
        w256 <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
        w256 <@ __SHLQ_256 (w256, aT8);
        buf <- (buf + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        aT8 <- (aT - cUR);
        (buf, lEN, tRAIL, aT, w) <@ __m_ilen_read_upto8_at (buf, lEN, 
        tRAIL, cUR, aT);
        t128 <- (zeroextu128 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
        w256 <@ __SHLQ_256 (w256, aT8);
        buf <- (buf + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      }
      aT <- (cUR + aT8);
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
      t128 <- (zeroextu128 x);
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
  proc __keccakf1600_avx2x4 (a:W256.t Array25.t) : W256.t Array25.t = {
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
    r8 <- rOL8;
    r56 <- rOL56;
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
  proc __keccakf1600_pround_unpacked (st0:W64.t Array25.t,
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
    r8 <- rOL8;
    r56 <- rOL56;
    st4x1 <@ __st4x_pack (st4x1, st0, st1, st2, st3);
    st4x2 <@ _keccakf1600_4x_pround (st4x2, st4x1, r8, r56);
    (st0, st1, st2, st3) <@ __st4x_unpack (st0, st1, st2, st3, st4x2);
    return (st0, st1, st2, st3);
  }
  proc __keccakf1600_pround_equiv (e:W256.t Array25.t, a:W256.t Array25.t) : 
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
    (st0, st1, st2, st3) <@ __keccakf1600_pround_unpacked (st0, st1, 
    st2, st3);
    e <@ __st4x_pack (e, st0, st1, st2, st3);
    return e;
  }
  proc __state_init_avx2x4 (st:W256.t Array25.t) : W256.t Array25.t = {
    var z256:W256.t;
    var i:int;
    z256 <- (set0_256);
    i <- 0;
    while ((i < (32 * 25))) {
      st.[i] <- z256;
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
    t128 <- (zeroextu128 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    t256 <- (t256 `^` st.[((rATE8 - 1) %/ 8)]);
    st.[((rATE8 - 1) %/ 8)] <- t256;
    return st;
  }
  proc __a_ilen_read_upto8_at (buf:W8.t Array999.t, offset:int, dELTA:int,
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
        (get64_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA))));
        w <@ __SHLQ (w, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray999.init8 (fun i => buf.[i]))
          (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
          w <@ __SHLQ (w, aT8);
          dELTA <- (dELTA + ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          lEN <- (lEN - ((8 <= (4 + aT8)) ? (8 - aT8) : 4));
          aT8 <- ((8 <= (4 + aT8)) ? 8 : (4 + aT8));
        } else {
          w <- (W64.of_int 0);
        }
        if (((aT8 < 8) /\ (2 <= lEN))) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray999.init8 (fun i => buf.[i]))
          (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
          dELTA <- (dELTA + ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          lEN <- (lEN - ((8 <= (2 + aT8)) ? (8 - aT8) : 2));
          t16 <@ __SHLQ (t16, aT8);
          w <- (w `|` t16);
          aT8 <- ((8 <= (2 + aT8)) ? 8 : (2 + aT8));
        } else {
          
        }
        if ((aT8 < 8)) {
          if ((1 <= lEN)) {
            t8 <-
            (zeroextu64
            (get8_direct (WArray999.init8 (fun i => buf.[i]))
            (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
            t8 <- (t8 `|` (W64.of_int (256 * (tRAIL %% 256))));
            dELTA <- (dELTA + 1);
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
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto16_at (buf:W8.t Array999.t, offset:int, dELTA:int,
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
        (get128_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA))));
        w <@ __SHLDQ (w, aT16);
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
  proc __a_ilen_read_upto32_at (buf:W8.t Array999.t, offset:int, dELTA:int,
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
        (get256_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA));
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
  proc __a_ilen_read_bcast_upto8_at (buf:W8.t Array999.t, offset:int,
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
        (get64_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA)));
        w256 <@ __SHLQ_256 (w256, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        aT8 <- (aT - cUR);
        (dELTA, lEN, tRAIL, aT, w) <@ __a_ilen_read_upto8_at (buf, offset,
        dELTA, lEN, tRAIL, cUR, aT);
        t128 <- (zeroextu128 w);
        w256 <- (VPBROADCAST_4u64 (truncateu64 t128));
        w256 <@ __SHLQ_256 (w256, aT8);
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      }
      aT <- (cUR + aT8);
    }
    return (dELTA, lEN, tRAIL, aT, w256);
  }
  proc __a_ilen_write_upto8 (buf:W8.t Array999.t, offset:int, dELTA:int,
                             lEN:int, w:W64.t) : W8.t Array999.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set64_direct (WArray999.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set32_direct (WArray999.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set16_direct (WArray999.init8 (fun i => buf.[i]))
          (offset + dELTA) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set8_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __a_ilen_write_upto16 (buf:W8.t Array999.t, offset:int, dELTA:int,
                              lEN:int, w:W128.t) : W8.t Array999.t * int *
                                                   int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set128_direct (WArray999.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set64_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __a_ilen_write_upto32 (buf:W8.t Array999.t, offset:int, dELTA:int,
                              lEN:int, w:W256.t) : W8.t Array999.t * int *
                                                   int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set256_direct (WArray999.init8 (fun i => buf.[i]))
        (offset + dELTA) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set128_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __a_rlen_read_upto8 (a:W8.t Array999.t, off:int, len:int) : int *
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
      w <- (get64_direct (WArray999.init8 (fun i => a.[i])) off);
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        w <-
        (zeroextu64 (get32_direct (WArray999.init8 (fun i => a.[i])) off));
        off <- (off + 4);
        sh <- (W8.of_int 32);
      } else {
        w <- (W64.of_int 0);
        sh <- (W8.of_int 0);
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        x <-
        (zeroextu64 (get16_direct (WArray999.init8 (fun i => a.[i])) off));
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
        (zeroextu64 (get8_direct (WArray999.init8 (fun i => a.[i])) off));
        x <- (x `<<` (sh `&` (W8.of_int 63)));
        w <- (w + x);
        off <- (off + 1);
      } else {
        
      }
    }
    return (off, w);
  }
  proc __a_rlen_write_upto8 (buf:W8.t Array999.t, off:int, data:W64.t,
                             len:int) : W8.t Array999.t * int = {
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
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i => buf.[i])) off data))
      );
      off <- (off + 8);
    } else {
      ( _0,  _1,  _2,  _3, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 4));
      if ((! zf)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set32_direct (WArray999.init8 (fun i => buf.[i])) 
        off (truncateu32 data))));
        off <- (off + 4);
        data <- (data `>>` (W8.of_int 32));
      } else {
        
      }
      ( _4,  _5,  _6,  _7, zf) <- (TEST_64 (W64.of_int len) (W64.of_int 2));
      if ((! zf)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set16_direct (WArray999.init8 (fun i => buf.[i])) 
        off (truncateu16 data))));
        off <- (off + 2);
        data <- (data `>>` (W8.of_int 16));
      } else {
        
      }
      ( _8,  _9,  _10,  _11, zf) <-
      (TEST_64 (W64.of_int len) (W64.of_int 1));
      if ((! zf)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set8_direct (WArray999.init8 (fun i => buf.[i])) off
        (truncateu8 data))));
        off <- (off + 1);
      } else {
        
      }
    }
    return (buf, off);
  }
  proc __addstate_ref (st:W64.t Array25.t, aT:int, buf:W8.t Array999.t,
                       offset:int, _LEN:int, _TRAILB:int) : W64.t Array25.t *
                                                            int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if ((aT8 <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ __a_ilen_read_upto8_at (buf, 
      offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st.[(aT %/ 8)] <- (st.[(aT %/ 8)] `^` w);
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (aT %/ 8);
    while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
      w <- (get64_direct (WArray999.init8 (fun i => buf.[i])) offset);
      offset <- (offset + 8);
      st.[at] <- (st.[at] `^` w);
      at <- (at + 1);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ __a_ilen_read_upto8_at (buf, offset,
      0, _LEN, _TRAILB, aT, aT);
      st.[at] <- (st.[at] `^` w);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_ref (st:W64.t Array25.t, aT:int, buf:W8.t Array999.t,
                     _TRAILB:int, _RATE8:int) : W64.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 999;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_ref (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_ref (st, 0, buf, offset, _RATE8, 0);
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_ref (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_ref (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_ref (buf:W8.t Array999.t, offset:int, _LEN:int,
                        st:W64.t Array25.t) : W8.t Array999.t * int = {
    var t:W64.t;
    var dELTA:int;
    var i:int;
    var  _0:int;
    i <- 0;
    while ((i < (_LEN %/ 8))) {
      t <- st.[i];
      buf <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf.[i_0])) 
      offset t)));
      offset <- (offset + 8);
      i <- (i + 1);
    }
    if ((0 < (_LEN %% 8))) {
      t <- st.[i];
      (buf, dELTA,  _0) <@ __a_ilen_write_upto8 (buf, offset, 0, (_LEN %% 8),
      t);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (buf, offset);
  }
  proc __squeeze_ref (st:W64.t Array25.t, buf:W8.t Array999.t, _RATE8:int) : 
  W64.t Array25.t * W8.t Array999.t = {
    var offset:int;
    var i:int;
    offset <- 0;
    i <- 0;
    while ((i < (999 %/ _RATE8))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, _RATE8, st);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    if ((0 < (999 %% _RATE8))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, (999 %% _RATE8), st);
    } else {
      
    }
    return (st, buf);
  }
  proc __addstate_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array999.t,
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
        (get64_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
        dELTA <- (dELTA + 8);
        _LEN <- (_LEN - 8);
        aT <- 8;
      } else {
        (dELTA, _LEN, _TRAILB, aT, t64_1) <@ __a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 0, aT);
        t128_0 <- (zeroextu128 t64_1);
        r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
      }
      st.[0] <- (st.[0] `^` r0);
    } else {
      
    }
    if (((aT < 40) /\ ((0 < _LEN) \/ (_TRAILB <> 0)))) {
      (dELTA, _LEN, _TRAILB, aT, r1) <@ __a_ilen_read_upto32_at (buf, 
      offset, dELTA, _LEN, _TRAILB, 8, aT);
      st.[1] <- (st.[1] `^` r1);
    } else {
      
    }
    if (((0 < _LEN) \/ (_TRAILB <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, t64_2) <@ __a_ilen_read_upto8_at (buf,
      offset, dELTA, _LEN, _TRAILB, 40, aT);
      t128_1 <- (zeroextu128 t64_2);
      t128_2 <- (set0_128);
      if (((0 < _LEN) \/ (_TRAILB <> 0))) {
        (dELTA, _LEN, _TRAILB, aT, r3) <@ __a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 48, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_3) <@ __a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 80, aT);
        t128_2 <- (zeroextu128 t64_3);
        (dELTA, _LEN, _TRAILB, aT, r4) <@ __a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 88, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_4) <@ __a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 120, aT);
        t128_1 <- (VPINSR_2u64 t128_1 t64_4 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r5) <@ __a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 128, aT);
        (dELTA, _LEN, _TRAILB, aT, t64_5) <@ __a_ilen_read_upto8_at (
        buf, offset, dELTA, _LEN, _TRAILB, 160, aT);
        t128_2 <- (VPINSR_2u64 t128_2 t64_5 (W8.of_int 1));
        (dELTA, _LEN, _TRAILB, aT, r6) <@ __a_ilen_read_upto32_at (buf,
        offset, dELTA, _LEN, _TRAILB, 168, aT);
        st <@ __addstate_r3456_avx2 (st, r3, r4, r5, r6);
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
  proc __absorb_avx2 (st:W256.t Array7.t, aT:int, buf:W8.t Array999.t,
                      _TRAILB:int, _RATE8:int) : W256.t Array7.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 999;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_avx2 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_avx2 (st, 0, buf, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_avx2 (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_avx2 (buf:W8.t Array999.t, offset:int, _LEN:int,
                         st:W256.t Array7.t) : W8.t Array999.t * int = {
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
      (buf, dELTA,  _0) <@ __a_ilen_write_upto32 (buf, offset, dELTA, 8,
      st.[0]);
      _LEN <- (_LEN - 8);
    } else {
      (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA, 
      _LEN, st.[0]);
    }
    (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA, 
    _LEN, st.[1]);
    if ((0 < _LEN)) {
      t128_0 <- (truncateu128 st.[2]);
      t128_1 <- (VEXTRACTI128 st.[2] (W8.of_int 1));
      t <- (truncateu64 t128_1);
      (buf, dELTA, _LEN) <@ __a_ilen_write_upto8 (buf, offset, dELTA, 
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
        (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA,
        _LEN, t256_4);
        if ((0 < _LEN)) {
          t <- (truncateu64 t128_0);
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto8 (buf, offset, dELTA,
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
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA,
          _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (truncateu64 t128_1);
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto8 (buf, offset, dELTA,
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
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA,
          _LEN, t256_4);
        } else {
          
        }
        if ((0 < _LEN)) {
          t <- (truncateu64 t128_0);
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto8 (buf, offset, dELTA,
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
          (buf, dELTA, _LEN) <@ __a_ilen_write_upto32 (buf, offset, dELTA,
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
  proc __squeeze_avx2 (st:W256.t Array7.t, buf:W8.t Array999.t, _RATE8:int) : 
  W256.t Array7.t * W8.t Array999.t = {
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    offset <- 0;
    _LEN <- 999;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    i <- 0;
    while ((i < iTERS)) {
      st <@ _keccakf1600_avx2 (st);
      (buf, offset) <@ __dumpstate_avx2 (buf, offset, _RATE8, st);
      i <- (i + 1);
    }
    if ((0 < lO)) {
      st <@ _keccakf1600_avx2 (st);
      (buf, offset) <@ __dumpstate_avx2 (buf, offset, lO, st);
    } else {
      
    }
    return (st, buf);
  }
  proc __addstate_bcast_avx2x4 (st:W256.t Array25.t, aT:int,
                                buf:W8.t Array999.t, offset:int, _LEN:int,
                                _TRAILB:int) : W256.t Array25.t * int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W256.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if (((aT8 %% 8) <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ __a_ilen_read_bcast_upto8_at (
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
      (get64_direct (WArray999.init8 (fun i => buf.[i])) offset));
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
      (dELTA, _LEN, _TRAILB, aT, w) <@ __a_ilen_read_bcast_upto8_at (
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
                              buf:W8.t Array999.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 999;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_bcast_avx2x4 (st, 0, buf, offset,
        _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_bcast_avx2x4 (st, aT, buf, offset, _LEN,
    _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __addstate_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t Array999.t,
                          buf1:W8.t Array999.t, buf2:W8.t Array999.t,
                          buf3:W8.t Array999.t, offset:int, _LEN:int,
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
      ( _0,  _1,  _2,  _3, t0) <@ __a_ilen_read_upto8_at (buf0, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 0)) `^`
      t0))));
      ( _4,  _5,  _6,  _7, t1) <@ __a_ilen_read_upto8_at (buf1, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 1)) `^`
      t1))));
      ( _8,  _9,  _10,  _11, t2) <@ __a_ilen_read_upto8_at (buf2, offset,
      dELTA, _LEN, _TRAILB, aT, aT8);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i]))
      ((4 * (aT %/ 8)) + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) ((4 * (aT %/ 8)) + 2)) `^`
      t2))));
      (dELTA, _LEN, _TRAILB, aT8, t3) <@ __a_ilen_read_upto8_at (buf3,
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
      t0 <- (get64_direct (WArray999.init8 (fun i => buf0.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      t1 <- (get64_direct (WArray999.init8 (fun i => buf1.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      t2 <- (get64_direct (WArray999.init8 (fun i => buf2.[i])) offset);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      t3 <- (get64_direct (WArray999.init8 (fun i => buf3.[i])) offset);
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
      ( _12,  _13,  _14,  _15, t0) <@ __a_ilen_read_upto8_at (buf0, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 0)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 0)) `^` t0))));
      ( _16,  _17,  _18,  _19, t1) <@ __a_ilen_read_upto8_at (buf1, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 1)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 1)) `^` t1))));
      ( _20,  _21,  _22,  _23, t2) <@ __a_ilen_read_upto8_at (buf2, offset,
      0, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64 (WArray800.init256 (fun i => st.[i])) (at + 2)
      ((get64 (WArray800.init256 (fun i => st.[i])) (at + 2)) `^` t2))));
      (dELTA, _LEN, _TRAILB, aT, t3) <@ __a_ilen_read_upto8_at (buf3, 
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
  proc __absorb_avx2x4 (st:W256.t Array25.t, aT:int, buf0:W8.t Array999.t,
                        buf1:W8.t Array999.t, buf2:W8.t Array999.t,
                        buf3:W8.t Array999.t, _TRAILB:int, _RATE8:int) : 
  W256.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- 999;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, 
      buf3, offset, (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      st <@ _keccakf1600_avx2x4 (st);
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_avx2x4 (st, 0, buf0, buf1, buf2,
        buf3, offset, _RATE8, 0);
        st <@ _keccakf1600_avx2x4 (st);
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_avx2x4 (st, aT, buf0, buf1, buf2, buf3,
    offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ __addratebit_avx2x4 (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_avx2x4 (buf0:W8.t Array999.t, buf1:W8.t Array999.t,
                           buf2:W8.t Array999.t, buf3:W8.t Array999.t,
                           offset:int, _LEN:int, st:W256.t Array25.t) : 
  W8.t Array999.t * W8.t Array999.t * W8.t Array999.t * W8.t Array999.t * int = {
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
      (x0, x1, x2, x3) <@ __4u64x4_u256x4 (x0, x1, x2, x3);
      buf0 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set256_direct (WArray999.init8 (fun i_0 => buf0.[i_0]))
      offset x0)));
      buf1 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set256_direct (WArray999.init8 (fun i_0 => buf1.[i_0]))
      offset x1)));
      buf2 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set256_direct (WArray999.init8 (fun i_0 => buf2.[i_0]))
      offset x2)));
      buf3 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set256_direct (WArray999.init8 (fun i_0 => buf3.[i_0]))
      offset x3)));
      offset <- (offset + 32);
    }
    while ((i < (8 * (_LEN %/ 8)))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      buf0 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf0.[i_0]))
      offset t0)));
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      buf1 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf1.[i_0]))
      offset t1)));
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      buf2 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf2.[i_0]))
      offset t2)));
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      buf3 <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf3.[i_0]))
      offset t3)));
      i <- (i + 8);
      offset <- (offset + 8);
    }
    if ((0 < (_LEN %% 8))) {
      t0 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (0 * 8)));
      (buf0,  _0,  _1) <@ __a_ilen_write_upto8 (buf0, offset, 0, (_LEN %% 8),
      t0);
      t1 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (1 * 8)));
      (buf1,  _2,  _3) <@ __a_ilen_write_upto8 (buf1, offset, 0, (_LEN %% 8),
      t1);
      t2 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (2 * 8)));
      (buf2,  _4,  _5) <@ __a_ilen_write_upto8 (buf2, offset, 0, (_LEN %% 8),
      t2);
      t3 <-
      (get64_direct (WArray800.init256 (fun i_0 => st.[i_0]))
      ((4 * i) + (3 * 8)));
      (buf3,  _6,  _7) <@ __a_ilen_write_upto8 (buf3, offset, 0, (_LEN %% 8),
      t3);
      offset <- (offset + (_LEN %% 8));
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, offset);
  }
  proc __squeeze_avx2x4 (st:W256.t Array25.t, buf0:W8.t Array999.t,
                         buf1:W8.t Array999.t, buf2:W8.t Array999.t,
                         buf3:W8.t Array999.t, _RATE8:int) : W256.t Array25.t *
                                                             W8.t Array999.t *
                                                             W8.t Array999.t *
                                                             W8.t Array999.t *
                                                             W8.t Array999.t = {
    var _LEN:int;
    var iTERS:int;
    var lO:int;
    var offset:int;
    var i:int;
    offset <- 0;
    _LEN <- 999;
    iTERS <- (_LEN %/ _RATE8);
    lO <- (_LEN %% _RATE8);
    if ((0 < iTERS)) {
      i <- 0;
      while ((i < iTERS)) {
        st <@ _keccakf1600_avx2x4 (st);
        (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, 
        buf1, buf2, buf3, offset, _RATE8, st);
        i <- (i + 1);
      }
    } else {
      
    }
    if ((0 < lO)) {
      st <@ _keccakf1600_avx2x4 (st);
      (buf0, buf1, buf2, buf3, offset) <@ __dumpstate_avx2x4 (buf0, buf1,
      buf2, buf3, offset, lO, st);
    } else {
      
    }
    return (st, buf0, buf1, buf2, buf3);
  }
}.
