require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array24 Array25 Array999 WArray40 WArray192 WArray200 WArray999.

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
    var t64:W64.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * _RATE8) - 1) %% 64)));
    t64 <- (t64 `^` st.[((_RATE8 - 1) %/ 8)]);
    st.[((_RATE8 - 1) %/ 8)] <- t64;
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
  proc __addstate_m_ref (st:W64.t Array25.t, aT:int, buf:int, _LEN:int,
                         _TRAILB:int) : W64.t Array25.t * int * int = {
    var aT8:int;
    var w:W64.t;
    var at:int;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if ((aT8 <> 0)) {
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
  proc __aread_subu64 (buf:W8.t Array999.t, offset:W64.t, dELTA:int, lEN:int,
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
        (get64_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray999.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray999.init8 (fun i => buf.[i]))
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
            (get8_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __aread_bcast_4subu64 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
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
        (get64_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __aread_subu128 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
                        lEN:int, tRAIL:int) : int * int * int * W128.t = {
    var w:W128.t;
    var t64:W64.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          w <-
          (VMOV_64
          (get64_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __aread_subu256 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
                        lEN:int, tRAIL:int) : int * int * int * W256.t = {
    var w:W256.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((32 <= lEN)) {
        w <-
        (get256_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          t128_0 <-
          (get128_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __awrite_subu64 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
                        lEN:int, w:W64.t) : W8.t Array999.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set64_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set32_direct (WArray999.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu32 w))));
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
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu16 w))));
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
  proc __awrite_subu128 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
                         lEN:int, w:W128.t) : W8.t Array999.t * int * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set128_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set64_direct (WArray999.init8 (fun i => buf.[i]))
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
  proc __awrite_subu256 (buf:W8.t Array999.t, offset:W64.t, dELTA:int,
                         lEN:int, w:W256.t) : W8.t Array999.t * int * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        buf <-
        (Array999.init
        (WArray999.get8
        (WArray999.set256_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          buf <-
          (Array999.init
          (WArray999.get8
          (WArray999.set128_direct (WArray999.init8 (fun i => buf.[i]))
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
}.
