(******************************************************************************
   Keccak1600_updstate_avx2x4.ec:

   Correctness proof for the Keccak1600 (updstate) array-buffer absorb/squeeze
   4-way AVX2 implementation.

   Modelled on Keccak1600_fixedsizes_avx2x4.ec — same skeleton (abstract theory
   parameterised on _ASIZE, MM module, lemma stubs) extended for the streaming
   updstate procs. Equivalence between MM here and the concrete extraction at
   _ASIZE=999 is checked by Keccak1600_updstate_avx2x4_checkXtr.ec.

******************************************************************************)

require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray800 WArray808.
from JazzEC require import Array25 Array101.

from CryptoSpecs require import JWordList.

require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Keccak1600_subreadwrite.

abstract theory KeccakUpdstateAvx2x4.

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
  proc _add_updstate_avx2x4 (st:W256.t Array25.t, at:int,
                             buf0:W8.t A.t, buf1:W8.t A.t,
                             buf2:W8.t A.t, buf3:W8.t A.t,
                             off:int, upto:int) : int * int *
                                                  W256.t Array25.t = {
    var at8:W64.t;
    var shval:W8.t;
    var t64:W64.t;
    var sh:W8.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      shval <- (truncateu8 at8);
      shval <- (shval `<<` (W8.of_int 3));
      ( _0, t64) <@ RW.MM.__a_rlen_read_upto8 (buf0, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      ( _1, t64) <@ RW.MM.__a_rlen_read_upto8 (buf1, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      ( _2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf2, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      (off2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf3, off, len);
      sh <- shval;
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WA.init8 (fun i => buf0.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf1.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf2.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      t64 <- (get64_direct (WA.init8 (fun i => buf3.[i])) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      ( _3, t64) <@ RW.MM.__a_rlen_read_upto8 (buf0, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      ( _4, t64) <@ RW.MM.__a_rlen_read_upto8 (buf1, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      ( _5, t64) <@ RW.MM.__a_rlen_read_upto8 (buf2, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf3, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 24)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24)) `^`
      t64))));
    } else {
      
    }
    at <- upto;
    return (at, off, st);
  }
  proc _add_bcast_updstate_avx2x4 (st:W256.t Array25.t, at:int,
                                   buf:W8.t A.t, off:int, upto:int) : 
  int * int * W256.t Array25.t = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var t128:W128.t;
    var t256:W256.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      (off2, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, len);
      len <- (len + at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `<<` (sh `&` (W8.of_int 63)));
      t128 <- (zeroextu128 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0) t256)));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t256 <-
      (VPBROADCAST_4u64
      (get64_direct (WA.init8 (fun i => buf.[i])) off));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) (4 * at)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) 
      (4 * at) t256)));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, (W64.to_uint upto8));
      t128 <- (zeroextu128 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
      t256 <-
      (t256 `^`
      (get256_direct (WArray800.init256 (fun i => st.[i])) (4 * at)));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set256_direct (WArray800.init256 (fun i => st.[i])) 
      (4 * at) t256)));
    } else {
      
    }
    at <- upto;
    return (at, off, st);
  }
  proc _absorb_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                                buf1:W8.t A.t, buf2:W8.t A.t,
                                buf3:W8.t A.t, len:int) : W64.t Array101.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ _ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    (* Erased call to spill *)
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (* Erased call to spill *)
      (at, off, stk) <@ _add_updstate_avx2x4 (stk, at, buf0, buf1, buf2,
      buf3, off, r8);
      (* Erased call to unspill *)
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, stk) <@ _add_updstate_avx2x4 (stk, at, buf0, buf1, buf2, 
    buf3, off, len);
    (* Erased call to unspill *)
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }
  proc _absorb_bcast_updstate_avx2x4 (st:W64.t Array101.t,
                                      buf:W8.t A.t, len:int) : 
  W64.t Array101.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ _ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (at, off, stk) <@ _add_bcast_updstate_avx2x4 (stk, at, buf, off, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, stk) <@ _add_bcast_updstate_avx2x4 (stk, at, buf, off, len);
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return st;
  }
  proc _dump_updstate_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                              buf2:W8.t A.t, buf3:W8.t A.t,
                              off:int, st:W256.t Array25.t, at:int, upto:int) : 
  int * int * W8.t A.t * W8.t A.t * W8.t A.t *
  W8.t A.t = {
    var at8:W64.t;
    var sh:W8.t;
    var t64:W64.t;
    var upto8:W64.t;
    var len:int;
    var off2:int;
    var newat:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    at8 <- (W64.of_int at);
    at8 <- (at8 `&` (W64.of_int 7));
    if ((at8 <> (W64.of_int 0))) {
      len <- upto;
      len <- (len - at);
      at <- (at `|>>` 3);
      at <- (at `<<` 3);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf0,  _0) <@ RW.MM.__a_rlen_write_upto8 (buf0, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf1,  _1) <@ RW.MM.__a_rlen_write_upto8 (buf1, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf2,  _2) <@ RW.MM.__a_rlen_write_upto8 (buf2, off, t64, len);
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf3, off2) <@ RW.MM.__a_rlen_write_upto8 (buf3, off, t64, len);
      len <- (len + (W64.to_uint at8));
      if ((8 <= len)) {
        off <- (off + 8);
        off <- (off - (W64.to_uint at8));
        at <- (at + 8);
      } else {
        off <- off2;
        at <- upto;
      }
    } else {
      
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      buf0 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf0.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf1.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf2.[i])) off t64))
      );
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf3.[i])) off t64))
      );
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0));
      (buf0,  _3) <@ RW.MM.__a_rlen_write_upto8 (buf0, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      (buf1,  _4) <@ RW.MM.__a_rlen_write_upto8 (buf1, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      (buf2,  _5) <@ RW.MM.__a_rlen_write_upto8 (buf2, off, t64,
      (W64.to_uint upto8));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      (buf3, off) <@ RW.MM.__a_rlen_write_upto8 (buf3, off, t64,
      (W64.to_uint upto8));
    } else {
      
    }
    at <- upto;
    return (at, off, buf0, buf1, buf2, buf3);
  }
  proc _squeeze_updstate_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
                                 buf1:W8.t A.t, buf2:W8.t A.t,
                                 buf3:W8.t A.t, len:int) : W64.t Array101.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t *
                                                                  W8.t A.t = {
    var ststatus:W64.t;
    var stk:W256.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W64.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[(4 * 25)];
    ( _0, r8, at) <@ _ststatus_data_avx2x4 (ststatus);
    stk <-
    (Array25.init
    (fun i => (get256 (WArray808.init64 (fun i => st.[i])) (0 + i))));
    if ((at = 0)) {
      stk <@ M._keccakf1600_avx2x4 (stk);
    } else {
      
    }
    off <- 0;
    len <- (len + at);
    while ((r8 < len)) {
      (at, off, buf0, buf1, buf2, buf3) <@ _dump_updstate_avx2x4 (buf0, 
      buf1, buf2, buf3, off, stk, at, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, buf0, buf1, buf2, buf3) <@ _dump_updstate_avx2x4 (buf0, 
    buf1, buf2, buf3, off, stk, at, len);
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.init8
    (fun i => (if ((32 * 0) <= i < ((32 * 0) + 800)) then (WArray800.get8
                                                          (WArray800.init256
                                                          (fun i => stk.[i]))
                                                          (i - (32 * 0))) else 
              (WArray808.get8 (WArray808.init64 (fun i => st.[i])) i)))
    )));
    st <-
    (Array101.init
    (WArray808.get64
    (WArray808.set8_direct (WArray808.init64 (fun i => st.[i])) (32 * 25)
    (truncateu8 (W64.of_int at)))));
    return (st, buf0, buf1, buf2, buf3);
  }
}.

(* ------------------------------------------------------------------------ *)
(* Spec-side operators (placeholder declarations). Each updstate proc has a  *)
(* pure-functional companion that captures its intended result; the hoare    *)
(* lemma below relates the proc to the operator. Bodies are deferred (`op`   *)
(* without definition) until the streaming-absorb / streaming-squeeze spec   *)
(* layer is filled in.                                                        *)
(* ------------------------------------------------------------------------ *)

op ststatus_data_avx2x4_spec : W64.t -> W64.t * int * int.

op add_updstate_avx2x4_spec :
  W256.t Array25.t -> int -> W8.t A.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> int -> int
  -> int * int * W256.t Array25.t.

op add_bcast_updstate_avx2x4_spec :
  W256.t Array25.t -> int -> W8.t A.t -> int -> int
  -> int * int * W256.t Array25.t.

op absorb_updstate_avx2x4_spec :
  W64.t Array101.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> int
  -> W64.t Array101.t.

op absorb_bcast_updstate_avx2x4_spec :
  W64.t Array101.t -> W8.t A.t -> int
  -> W64.t Array101.t.

op dump_updstate_avx2x4_spec :
  W8.t A.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> int -> W256.t Array25.t -> int -> int
  -> int * int * W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t.

op squeeze_updstate_avx2x4_spec :
  W64.t Array101.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> W8.t A.t -> int
  -> W64.t Array101.t * W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t.

(* ------------------------------------------------------------------------ *)
(* Lossless / hoare / phoare triples for each updstate proc.                 *)
(* ------------------------------------------------------------------------ *)

lemma ststatus_data_avx2x4_ll: islossless MM._ststatus_data_avx2x4.
proof. admitted.

hoare ststatus_data_avx2x4_h _s:
  MM._ststatus_data_avx2x4
  : ststatus = _s
  ==> res = ststatus_data_avx2x4_spec _s.
proof. admitted.

phoare ststatus_data_avx2x4_ph _s:
  [ MM._ststatus_data_avx2x4
  : ststatus = _s
  ==> res = ststatus_data_avx2x4_spec _s
  ] = 1%r.
proof. by conseq ststatus_data_avx2x4_ll (ststatus_data_avx2x4_h _s). qed.


lemma add_updstate_avx2x4_ll: islossless MM._add_updstate_avx2x4.
proof. admitted.

hoare add_updstate_avx2x4_h _st _at _b0 _b1 _b2 _b3 _off _upto:
  MM._add_updstate_avx2x4
  : st = _st /\ at = _at /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3
    /\ off = _off /\ upto = _upto
  ==> res = add_updstate_avx2x4_spec _st _at _b0 _b1 _b2 _b3 _off _upto.
proof. admitted.

phoare add_updstate_avx2x4_ph _st _at _b0 _b1 _b2 _b3 _off _upto:
  [ MM._add_updstate_avx2x4
  : st = _st /\ at = _at /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3
    /\ off = _off /\ upto = _upto
  ==> res = add_updstate_avx2x4_spec _st _at _b0 _b1 _b2 _b3 _off _upto
  ] = 1%r.
proof.
by conseq add_updstate_avx2x4_ll
       (add_updstate_avx2x4_h _st _at _b0 _b1 _b2 _b3 _off _upto).
qed.


lemma add_bcast_updstate_avx2x4_ll: islossless MM._add_bcast_updstate_avx2x4.
proof. admitted.

hoare add_bcast_updstate_avx2x4_h _st _at _buf _off _upto:
  MM._add_bcast_updstate_avx2x4
  : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
  ==> res = add_bcast_updstate_avx2x4_spec _st _at _buf _off _upto.
proof. admitted.

phoare add_bcast_updstate_avx2x4_ph _st _at _buf _off _upto:
  [ MM._add_bcast_updstate_avx2x4
  : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
  ==> res = add_bcast_updstate_avx2x4_spec _st _at _buf _off _upto
  ] = 1%r.
proof.
by conseq add_bcast_updstate_avx2x4_ll
       (add_bcast_updstate_avx2x4_h _st _at _buf _off _upto).
qed.


lemma absorb_updstate_avx2x4_ll: islossless MM._absorb_updstate_avx2x4.
proof. admitted.

hoare absorb_updstate_avx2x4_h _st _b0 _b1 _b2 _b3 _len:
  MM._absorb_updstate_avx2x4
  : st = _st /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3 /\ len = _len
  ==> res = absorb_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len.
proof. admitted.

phoare absorb_updstate_avx2x4_ph _st _b0 _b1 _b2 _b3 _len:
  [ MM._absorb_updstate_avx2x4
  : st = _st /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3 /\ len = _len
  ==> res = absorb_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len
  ] = 1%r.
proof.
by conseq absorb_updstate_avx2x4_ll
       (absorb_updstate_avx2x4_h _st _b0 _b1 _b2 _b3 _len).
qed.


lemma absorb_bcast_updstate_avx2x4_ll: islossless MM._absorb_bcast_updstate_avx2x4.
proof. admitted.

hoare absorb_bcast_updstate_avx2x4_h _st _buf _len:
  MM._absorb_bcast_updstate_avx2x4
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = absorb_bcast_updstate_avx2x4_spec _st _buf _len.
proof. admitted.

phoare absorb_bcast_updstate_avx2x4_ph _st _buf _len:
  [ MM._absorb_bcast_updstate_avx2x4
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = absorb_bcast_updstate_avx2x4_spec _st _buf _len
  ] = 1%r.
proof.
by conseq absorb_bcast_updstate_avx2x4_ll
       (absorb_bcast_updstate_avx2x4_h _st _buf _len).
qed.


lemma dump_updstate_avx2x4_ll: islossless MM._dump_updstate_avx2x4.
proof. admitted.

hoare dump_updstate_avx2x4_h _b0 _b1 _b2 _b3 _off _st _at _upto:
  MM._dump_updstate_avx2x4
  : buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3
    /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
  ==> res = dump_updstate_avx2x4_spec _b0 _b1 _b2 _b3 _off _st _at _upto.
proof. admitted.

phoare dump_updstate_avx2x4_ph _b0 _b1 _b2 _b3 _off _st _at _upto:
  [ MM._dump_updstate_avx2x4
  : buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3
    /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
  ==> res = dump_updstate_avx2x4_spec _b0 _b1 _b2 _b3 _off _st _at _upto
  ] = 1%r.
proof.
by conseq dump_updstate_avx2x4_ll
       (dump_updstate_avx2x4_h _b0 _b1 _b2 _b3 _off _st _at _upto).
qed.


lemma squeeze_updstate_avx2x4_ll: islossless MM._squeeze_updstate_avx2x4.
proof. admitted.

hoare squeeze_updstate_avx2x4_h _st _b0 _b1 _b2 _b3 _len:
  MM._squeeze_updstate_avx2x4
  : st = _st /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3 /\ len = _len
  ==> res = squeeze_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len.
proof. admitted.

phoare squeeze_updstate_avx2x4_ph _st _b0 _b1 _b2 _b3 _len:
  [ MM._squeeze_updstate_avx2x4
  : st = _st /\ buf0 = _b0 /\ buf1 = _b1 /\ buf2 = _b2 /\ buf3 = _b3 /\ len = _len
  ==> res = squeeze_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len
  ] = 1%r.
proof.
by conseq squeeze_updstate_avx2x4_ll
       (squeeze_updstate_avx2x4_h _st _b0 _b1 _b2 _b3 _len).
qed.

end KeccakUpdstateAvx2x4.
