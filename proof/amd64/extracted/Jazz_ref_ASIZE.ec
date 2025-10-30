require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array24 Array25 Array999 WArray40 WArray192 WArray200 WArray999.

abbrev [-printing] __RATE8 = (W64.of_int 199).

abbrev [-printing] __ASIZE = (W64.of_int 999).

abbrev  kECCAK1600_RC =
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
    c <- (c + 2);
    while ((c < (24 - 1))) {
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
  proc __addratebit_ref (st:W64.t Array25.t, rATE8:int) : W64.t Array25.t = {
    var t64:W64.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE8) - 1) %% 64)));
    t64 <- (t64 `^` st.[((rATE8 - 1) %/ 8)]);
    st.[((rATE8 - 1) %/ 8)] <- t64;
    return st;
  }
  proc __a_ilen_read_upto8_at (buf:W8.t Array999.t, offset:int, dELTA:int,
                               lEN:int, tRAIL:int, cUR:int, aT:int) : 
  int * int * int * int * W64.t = {
    var w:W64.t;
    var aT8:int;
    var t16:W64.t;
    var t8:W64.t;
    if (((aT < cUR) \/ ((cUR + 8) <= aT))) {
      w <- (W64.of_int 0);
    } else {
      aT8 <- (aT - cUR);
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WArray999.init8 (fun i => buf.[i]))
        (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA))));
        w <- (w `<<` (W8.of_int (8 * aT8)));
        dELTA <- (dELTA + (8 - aT8));
        lEN <- (lEN - (8 - aT8));
        aT8 <- 8;
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray999.init8 (fun i => buf.[i]))
          (W64.to_uint ((W64.of_int offset) + (W64.of_int dELTA)))));
          w <- (w `<<` (W8.of_int (8 * aT8)));
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
          t16 <- (t16 `<<` (W8.of_int (8 * aT8)));
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
            t8 <- (t8 `<<` (W8.of_int (8 * aT8)));
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
              t8 <- (t8 `<<` (W8.of_int (8 * aT8)));
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
    if (((aT < cUR) \/ ((cUR + 16) <= aT))) {
      w <- (set0_128);
    } else {
      aT16 <- (aT - cUR);
      if ((8 <= aT16)) {
        w <- (set0_128);
        (dELTA, lEN, tRAIL, aT16, t64_1) <@ __a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, 8, aT16);
        w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
      } else {
        (dELTA, lEN, tRAIL, aT16, t64_0) <@ __a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, 0, aT16);
        w <- (zeroextu128 t64_0);
        (dELTA, lEN, tRAIL, aT16, t64_1) <@ __a_ilen_read_upto8_at (buf,
        offset, dELTA, lEN, tRAIL, 8, aT16);
        w <- (VPINSR_2u64 w t64_1 (W8.of_int 1));
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
    if (((aT < cUR) \/ ((cUR + 32) <= aT))) {
      w <- (set0_256);
    } else {
      aT32 <- (aT - cUR);
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
      aT <- (cUR + aT32);
    }
    return (dELTA, lEN, tRAIL, aT, w);
  }
  proc __a_ilen_read_upto8 (buf:W8.t Array999.t, offset:int, dELTA:int,
                            lEN:int, tRAIL:int) : int * int * int * W64.t = {
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
        (get64_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64
          (get16_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
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
  proc __a_ilen_read_bcast_upto8 (buf:W8.t Array999.t, offset:int, dELTA:int,
                                  lEN:int, tRAIL:int) : int * int * int *
                                                        W256.t = {
    var w:W256.t;
    var t64:W64.t;
    var t128:W128.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w <-
        (VPBROADCAST_4u64
        (get64_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        (dELTA, lEN, tRAIL, t64) <@ __a_ilen_read_upto8 (buf, offset, 
        dELTA, lEN, tRAIL);
        t128 <- (zeroextu128 t64);
        w <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __a_ilen_read_upto16 (buf:W8.t Array999.t, offset:int, dELTA:int,
                             lEN:int, tRAIL:int) : int * int * int * W128.t = {
    var w:W128.t;
    var t64:W64.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <-
        (get128_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          w <-
          (VMOV_64
          (get64_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA)
          ));
          dELTA <- (dELTA + 8);
          lEN <- (lEN - 8);
          (dELTA, lEN, tRAIL, t64) <@ __a_ilen_read_upto8 (buf, offset,
          dELTA, lEN, tRAIL);
          w <- (VPINSR_2u64 w t64 (W8.of_int 1));
        } else {
          (dELTA, lEN, tRAIL, t64) <@ __a_ilen_read_upto8 (buf, offset,
          dELTA, lEN, tRAIL);
          w <- (zeroextu128 t64);
        }
      }
    }
    return (dELTA, lEN, tRAIL, w);
  }
  proc __a_ilen_read_upto32 (buf:W8.t Array999.t, offset:int, dELTA:int,
                             lEN:int, tRAIL:int) : int * int * int * W256.t = {
    var w:W256.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((32 <= lEN)) {
        w <-
        (get256_direct (WArray999.init8 (fun i => buf.[i])) (offset + dELTA));
        dELTA <- (dELTA + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          t128_0 <-
          (get128_direct (WArray999.init8 (fun i => buf.[i]))
          (offset + dELTA));
          dELTA <- (dELTA + 16);
          lEN <- (lEN - 16);
          (dELTA, lEN, tRAIL, t128_1) <@ __a_ilen_read_upto16 (buf, offset,
          dELTA, lEN, tRAIL);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        } else {
          t128_1 <- (set0_128);
          (dELTA, lEN, tRAIL, t128_0) <@ __a_ilen_read_upto16 (buf, offset,
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
                       offset:int, lEN:int, tRAILB:int) : W64.t Array25.t *
                                                          int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if ((aT8 <> 0)) {
      (dELTA, lEN, tRAILB, aT8, w) <@ __a_ilen_read_upto8_at (buf, offset,
      dELTA, lEN, tRAILB, aT, aT8);
      st.[(aT %/ 8)] <- (st.[(aT %/ 8)] `^` w);
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (aT %/ 8);
    while ((at < ((aT %/ 8) + (lEN %/ 8)))) {
      w <- (get64_direct (WArray999.init8 (fun i => buf.[i])) offset);
      offset <- (offset + 8);
      st.[at] <- (st.[at] `^` w);
      at <- (at + 1);
    }
    aT <- (aT + (8 * (lEN %/ 8)));
    lEN <- (lEN %% 8);
    if (((0 < lEN) \/ ((tRAILB %% 256) <> 0))) {
      aT <- (aT + (lEN + (((tRAILB %% 256) <> 0) ? 1 : 0)));
      (dELTA, lEN, tRAILB, w) <@ __a_ilen_read_upto8 (buf, offset, 0, 
      lEN, tRAILB);
      st.[at] <- (st.[at] `^` w);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_at_ref (st:W64.t Array25.t, aT:int, buf:W8.t Array999.t,
                        tRAILB:int) : W64.t Array25.t * int = {
    var lEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    lEN <- 999;
    if ((199 <= (aT + lEN))) {
      (st,  _0, offset) <@ __addstate_ref (st, aT, buf, offset, (199 - aT),
      0);
      lEN <- (lEN - (199 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      iTERS <- (lEN %/ 199);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_ref (st, 0, buf, offset, 199, 0);
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      lEN <- (lEN %% 199);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_ref (st, aT, buf, offset, lEN, tRAILB);
    if ((tRAILB <> 0)) {
      st <@ __addratebit_ref (st, 199);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_ref (buf:W8.t Array999.t, offset:int, lEN:int,
                        st:W64.t Array25.t) : W8.t Array999.t * int = {
    var t:W64.t;
    var dELTA:int;
    var i:int;
    var  _0:int;
    i <- 0;
    while ((i < (lEN %/ 8))) {
      t <- st.[i];
      buf <-
      (Array999.init
      (WArray999.get8
      (WArray999.set64_direct (WArray999.init8 (fun i_0 => buf.[i_0])) 
      offset t)));
      offset <- (offset + 8);
      i <- (i + 1);
    }
    if ((0 < (lEN %% 8))) {
      t <- st.[i];
      (buf, dELTA,  _0) <@ __a_ilen_write_upto8 (buf, offset, 0, (lEN %% 8),
      t);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (buf, offset);
  }
  proc __squeeze_array_ref (buf:W8.t Array999.t, st:W64.t Array25.t) : 
  W8.t Array999.t * W64.t Array25.t = {
    var offset:int;
    var i:int;
    offset <- 0;
    i <- 0;
    while ((i < (999 %/ 199))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, 199, st);
      i <- (i + 1);
    }
    if ((0 < (999 %% 199))) {
      (* Erased call to spill *)
      st <@ _keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, (999 %% 199), st);
    } else {
      
    }
    return (buf, st);
  }
}.
