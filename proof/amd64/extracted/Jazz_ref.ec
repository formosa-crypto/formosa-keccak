require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array5 Array24 Array25 WArray40 WArray192 WArray200.

abbrev kECCAK1600_RC =
(Array24.of_list witness
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
    t <- a;
    t <- (invw t);
    t <- (t `&` b);
    return t;
  }
  proc keccakf1600_index (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc keccakf1600_rho_offsets (i:int) : int = {
    var aux:int;
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
    var aux:int;
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
    var aux:int;
    var aux_0:W64.t;
    var d:W64.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux_0 <@ __rol_u64_ref (d.[x], 1);
      d.[x] <- aux_0;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- (x + 1);
    }
    return d;
  }
  proc __rol_sum_ref (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : W64.t Array5.t = {
    var aux:int;
    var aux_0:W64.t;
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
      aux_0 <@ __rol_u64_ref (b.[x], r);
      b.[x] <- aux_0;
      x <- (x + 1);
    }
    return b;
  }
  proc __set_row_ref (e:W64.t Array25.t, b:W64.t Array5.t, y:int, s_rc:W64.t) : 
  W64.t Array25.t = {
    var aux:int;
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
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` s_rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- (x + 1);
    }
    return e;
  }
  proc __round_ref (e:W64.t Array25.t, a:W64.t Array25.t, s_rc:W64.t) : 
  W64.t Array25.t = {
    var aux:int;
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
      e <@ __set_row_ref (e, b, y, s_rc);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t = {
    var rC:W64.t Array24.t;
    var s_RC:W64.t Array24.t;
    var s_e:W64.t Array25.t;
    var e:W64.t Array25.t;
    var c:W64.t;
    var s_c:W64.t;
    var rc:W64.t;
    var s_rc:W64.t;
    rC <- witness;
    e <- witness;
    s_RC <- witness;
    s_e <- witness;
    rC <- kECCAK1600_RC;
    s_RC <- rC;
    e <- s_e;
    c <- (W64.of_int 0);
    s_c <- c;
    rC <- s_RC;
    rc <- rC.[(W64.to_uint c)];
    s_rc <- rc;
    e <@ __round_ref (e, a, s_rc);
    rC <- s_RC;
    rc <- rC.[((W64.to_uint c) + 1)];
    s_rc <- rc;
    a <@ __round_ref (a, e, s_rc);
    c <- s_c;
    c <- (c + (W64.of_int 2));
    while ((c \ult (W64.of_int (24 - 1)))) {
      s_c <- c;
      rC <- s_RC;
      rc <- rC.[(W64.to_uint c)];
      s_rc <- rc;
      e <@ __round_ref (e, a, s_rc);
      rC <- s_RC;
      rc <- rC.[((W64.to_uint c) + 1)];
      s_rc <- rc;
      a <@ __round_ref (a, e, s_rc);
      c <- s_c;
      c <- (c + (W64.of_int 2));
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
    var i:W64.t;
    z64 <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 25))) {
      st.[(W64.to_uint i)] <- z64;
      i <- (i + (W64.of_int 1));
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
  proc __mread_subu64 (buf:W64.t, lEN:int, tRAIL:int) : W64.t * int * int *
                                                        W64.t = {
    var w:W64.t;
    var iLEN:int;
    var t16:W64.t;
    var t8:W64.t;
    iLEN <- lEN;
    if ((lEN <= 0)) {
      w <- (W64.of_int tRAIL);
      tRAIL <- 0;
    } else {
      if ((8 <= lEN)) {
        w <- (loadW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
        buf <- (buf + (W64.of_int 8));
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64 (loadW32 Glob.mem (W64.to_uint (buf + (W64.of_int 0))))
          );
          buf <- (buf + (W64.of_int 4));
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64 (loadW16 Glob.mem (W64.to_uint (buf + (W64.of_int 0))))
          );
          buf <- (buf + (W64.of_int 2));
          lEN <- (lEN - 2);
        } else {
          t16 <- (W64.of_int 0);
        }
        if (((1 <= lEN) \/ (tRAIL <> 0))) {
          if ((1 <= lEN)) {
            t8 <-
            (zeroextu64
            (loadW8 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))));
            if ((tRAIL <> 0)) {
              t8 <- (t8 `|` (W64.of_int (256 * tRAIL)));
            } else {
              
            }
            buf <- (buf + (W64.of_int 1));
            lEN <- (lEN - 1);
          } else {
            t8 <- (W64.of_int tRAIL);
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
    return (buf, lEN, tRAIL, w);
  }
  proc __mread_bcast_4subu64 (buf:W64.t, lEN:int, tRAIL:int) : W64.t * int *
                                                               int * W256.t = {
    var w:W256.t;
    var t64:W64.t;
    var t128:W128.t;
    if (((lEN <= 0) /\ (tRAIL = 0))) {
      w <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        w <-
        (VPBROADCAST_4u64
        (loadW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))));
        buf <- (buf + (W64.of_int 8));
        lEN <- (lEN - 8);
      } else {
        (buf, lEN, tRAIL, t64) <@ __mread_subu64 (buf, lEN, tRAIL);
        t128 <- (zeroextu128 t64);
        w <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (buf, lEN, tRAIL, w);
  }
  proc __mread_subu128 (buf:W64.t, lEN:int, tRAIL:int) : W64.t * int * int *
                                                         W128.t = {
    var w:W128.t;
    var t64:W64.t;
    if (((lEN <= 0) /\ (tRAIL = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        w <- (loadW128 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
        buf <- (buf + (W64.of_int 16));
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          w <-
          (VMOV_64 (loadW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))));
          buf <- (buf + (W64.of_int 8));
          lEN <- (lEN - 8);
          (buf, lEN, tRAIL, t64) <@ __mread_subu64 (buf, lEN, tRAIL);
          w <- (VPINSR_2u64 w t64 (W8.of_int 1));
        } else {
          (buf, lEN, tRAIL, t64) <@ __mread_subu64 (buf, lEN, tRAIL);
          w <- (zeroextu128 t64);
        }
      }
    }
    return (buf, lEN, tRAIL, w);
  }
  proc __mread_subu256 (buf:W64.t, lEN:int, tRAIL:int) : W64.t * int * int *
                                                         W256.t = {
    var w:W256.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    if (((lEN <= 0) /\ (tRAIL = 0))) {
      w <- (set0_256);
    } else {
      if ((32 <= lEN)) {
        w <- (loadW256 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
        buf <- (buf + (W64.of_int 32));
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          t128_0 <- (loadW128 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
          buf <- (buf + (W64.of_int 16));
          lEN <- (lEN - 16);
          (buf, lEN, tRAIL, t128_1) <@ __mread_subu128 (buf, lEN, tRAIL);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        } else {
          t128_1 <- (set0_128);
          (buf, lEN, tRAIL, t128_0) <@ __mread_subu128 (buf, lEN, tRAIL);
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        }
      }
    }
    return (buf, lEN, tRAIL, w);
  }
  proc __mwrite_subu64 (buf:W64.t, lEN:int, w:W64.t) : W64.t * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        Glob.mem <-
        (storeW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0))) w);
        buf <- (buf + (W64.of_int 8));
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          Glob.mem <-
          (storeW32 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))
          (truncateu32 w));
          w <- (w `>>` (W8.of_int 32));
          buf <- (buf + (W64.of_int 4));
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          Glob.mem <-
          (storeW16 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))
          (truncateu16 w));
          w <- (w `>>` (W8.of_int 16));
          buf <- (buf + (W64.of_int 2));
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          Glob.mem <-
          (storeW8 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))
          (truncateu8 w));
          buf <- (buf + (W64.of_int 1));
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __mwrite_subu128 (buf:W64.t, lEN:int, w:W128.t) : W64.t * int = {
    var t64:W64.t;
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        Glob.mem <-
        (storeW128 Glob.mem (W64.to_uint (buf + (W64.of_int 0))) w);
        buf <- (buf + (W64.of_int 16));
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          Glob.mem <-
          (storeW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))
          (MOVV_64 (truncateu64 w)));
          buf <- (buf + (W64.of_int 8));
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (truncateu64 w);
        (buf, lEN) <@ __mwrite_subu64 (buf, lEN, t64);
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __mwrite_subu256 (buf:W64.t, lEN:int, w:W256.t) : W64.t * int = {
    var t128:W128.t;
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        Glob.mem <-
        (storeW256 Glob.mem (W64.to_uint (buf + (W64.of_int 0))) w);
        buf <- (buf + (W64.of_int 32));
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          Glob.mem <-
          (storeW128 Glob.mem (W64.to_uint (buf + (W64.of_int 0)))
          (truncateu128 w));
          buf <- (buf + (W64.of_int 16));
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          t128 <- (truncateu128 w);
        }
        (buf, lEN) <@ __mwrite_subu128 (buf, lEN, t128);
      }
    } else {
      
    }
    return (buf, lEN);
  }
  proc __addstate_imem_ref (st:W64.t Array25.t, aT:int, buf:W64.t, lEN:int,
                            tRAILB:int) : W64.t Array25.t * int * W64.t = {
    var aLL:int;
    var lO:int;
    var at:W64.t;
    var t:W64.t;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    at <- (W64.of_int (aT %/ 8));
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        (buf,  _2,  _3, t) <@ __mread_subu64 (buf, lEN, tRAILB);
        t <- (t `<<` (W8.of_int (8 * lO)));
        t <- (t `^` st.[(W64.to_uint at)]);
        st.[(W64.to_uint at)] <- t;
        lO <- 0;
        aT <- 0;
        lEN <- 0;
        tRAILB <- 0;
      } else {
        if ((8 <= lEN)) {
          t <- (loadW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
          buf <- (buf + (W64.of_int (8 - lO)));
        } else {
          (buf,  _0,  _1, t) <@ __mread_subu64 (buf, (8 - lO), tRAILB);
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t <- (t `<<` (W8.of_int (8 * lO)));
        t <- (t `^` st.[(W64.to_uint at)]);
        st.[(W64.to_uint at)] <- t;
        at <- (at + (W64.of_int 1));
      }
    } else {
      
    }
    if ((8 <= lEN)) {
      while ((at \ult (W64.of_int ((aT %/ 8) + (lEN %/ 8))))) {
        t <- (loadW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0))));
        buf <- (buf + (W64.of_int 8));
        t <- (t `^` st.[(W64.to_uint at)]);
        st.[(W64.to_uint at)] <- t;
        at <- (at + (W64.of_int 1));
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      (buf,  _4,  _5, t) <@ __mread_subu64 (buf, lO, tRAILB);
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
        tRAILB <- 0;
      } else {
        
      }
      t <- (t `^` st.[(W64.to_uint at)]);
      st.[(W64.to_uint at)] <- t;
    } else {
      
    }
    return (st, aLL, buf);
  }
  proc __absorb_imem_ref (st:W64.t Array25.t, aT:int, buf:W64.t, lEN:int,
                          rATE8:int, tRAILB:int) : W64.t Array25.t * int *
                                                   W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    var  _0:int;
    var  _1:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (st, aT, buf) <@ __addstate_imem_ref (st, aT, buf, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ __addratebit_ref (st, rATE8);
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        (st,  _0, buf) <@ __addstate_imem_ref (st, aT, buf, (rATE8 - aT), 0);
        lEN <- (lEN - (rATE8 - aT));
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st,  _1, buf) <@ __addstate_imem_ref (st, 0, buf, rATE8, 0);
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        i <- (i + (W64.of_int 1));
      }
      lEN <- (aLL %% rATE8);
      (st, aT, buf) <@ __addstate_imem_ref (st, 0, buf, lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ __addratebit_ref (st, rATE8);
      } else {
        
      }
    }
    return (st, aT, buf);
  }
  proc __dumpstate_imem_ref (buf:W64.t, lEN:int, st:W64.t Array25.t) : W64.t = {
    var i:W64.t;
    var t:W64.t;
    var  _0:int;
    i <- (W64.of_int 0);
    while ((i \slt (W64.of_int (lEN %/ 8)))) {
      t <- st.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      Glob.mem <- (storeW64 Glob.mem (W64.to_uint (buf + (W64.of_int 0))) t);
      buf <- (buf + (W64.of_int 8));
    }
    if ((0 < (lEN %% 8))) {
      t <- st.[(W64.to_uint i)];
      (buf,  _0) <@ __mwrite_subu64 (buf, (lEN %% 8), t);
    } else {
      
    }
    return buf;
  }
  proc __squeeze_imem_ref (buf:W64.t, lEN:int, st:W64.t Array25.t, rATE8:int) : 
  W64.t * W64.t Array25.t = {
    var iTERS:int;
    var lO:int;
    var i:W64.t;
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- (W64.of_int 0);
        while ((i \ult (W64.of_int iTERS))) {
          (* Erased call to spill *)
          st <@ _keccakf1600_ref (st);
          (* Erased call to unspill *)
          buf <@ __dumpstate_imem_ref (buf, rATE8, st);
          i <- (i + (W64.of_int 1));
        }
      } else {
        
      }
      if ((0 < lO)) {
        (* Erased call to spill *)
        st <@ _keccakf1600_ref (st);
        (* Erased call to unspill *)
        buf <@ __dumpstate_imem_ref (buf, lO, st);
      } else {
        
      }
    } else {
      
    }
    return (buf, st);
  }
}.
