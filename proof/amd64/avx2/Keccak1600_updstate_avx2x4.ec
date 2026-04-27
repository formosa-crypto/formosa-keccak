(******************************************************************************
   Keccak1600_updstate_avx2.ec:

   Correctness proof for the Keccak (updstate) array absorb/squeeze
  4-way AVX2 implementation



******************************************************************************)

require import AllCore List Int IntDiv BitEncoding.
(*---*) import BitEncoding.BitChunking.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz_upd.

from JazzEC require import WArray200 WArray800 WArray808.
from JazzEC require import Array100 Array101.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccak1600_Spec.


require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Keccak1600_subreadwrite.


(*
   INCREMENTAL (UPDSTATE) ARRAY ABSORB
   ===================================
*)

lemma add_bcast_updstate_avx2x4_ll: islossless M.___add_bcast_updstate_avx2x4.
proof.
admitted.
(*
proc.
seq 5: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.
*)

lemma add_updstate_avx2x4_ll: islossless M.___add_updstate_avx2x4.
proof.
admitted.
(*
proc.
seq 5: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
by auto => /#.
qed.
*)

lemma absorb_bcast_updstate_avx2x4_ll: islossless M.___absorb_bcast_updstate_avx2x4 .
proof.
admitted.
(*
proc.
seq 7: true => //.
 wp; while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move => z; auto => /#.
 sp; if => //.
  by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
if => //.
by wp; call m_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.
*)

lemma absorb_updstate_avx2x4_ll: islossless M.___absorb_updstate_avx2x4.
proof.
admitted.
(*
proc.
seq 7: true => //.
 wp; while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move => z; auto => /#.
 sp; if => //.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  wp; call m_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
if => //.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
wp; call m_ilen_read_upto8_at_ll.
by auto => /#.
qed.
*)

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dump_updstate_avx2x4_ll: islossless M.___dump_updstate_avx2x4.
proof.
admitted.
(*
proc.
seq 7: true => //.
 wp; while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
wp; call m_ilen_write_upto8_ll.
by auto => /#.
qed.
*)

lemma squeeze_updstate_avx2x4_ll: islossless M.___squeeze_updstate_avx2x4.
proof.
admitted.
(*
proc.
seq 3: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_m_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_m_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.
*)



abstract theory KeccakArrayAvx2x4.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

clone import Keccak1600_Jazz_upd with
  op A.size <- _ASIZE,
  op WA.size <- _ASIZE
  proof A.ge0_size by exact _ASIZE_ge0.
(*
clone import Keccak1600x4_Jazz.A as A
 with op size <- _ASIZE
      proof ge0_size by exact _ASIZE_ge0.

clone import Keccak1600x4_Jazz.WA as WA
 with op size <- _ASIZE.
*)
clone import ReadWriteArray as RW
 with op _ASIZE <- _ASIZE,
      theory A <- A,
      theory WA <- WA
      proof _ASIZE_ge0 by exact _ASIZE_ge0
      proof _ASIZE_u64 by exact _ASIZE_u64.

module MM = {

  proc _ststatus_data_avx2x4 (ststatus: W64.t) : W64.t * int *int = {
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

  proc _init_updstate_avx2x4 (st:W64.t Array101.t, r64:int, trailb:W8.t) : 
  W64.t Array101.t = {
    var zero:W256.t;
    var status:W64.t;
    var t:W64.t;
    var i:int;
    zero <- (set0_256);
    status <- (zeroextu64 trailb);
    status <- (status `<<` (W8.of_int 8));
    r64 <- (W8.to_uint ((W8.of_int r64) - (W8.of_int 1)));
    t <- (zeroextu64 (W8.of_int r64));
    status <- (status + t);
    status <- (status `<<` (W8.of_int 8));
    i <- 0;
    while ((i < (32 * 25))) {
      st <-
      (Array101.init
      (WArray808.get64
      (WArray808.set256_direct (WArray808.init64 (fun i_0 => st.[i_0])) 
      i zero)));
      i <- (i + 32);
    }
    st.[(4 * 25)] <- status;
    return st;
  }
  proc init_updstate_avx2x4 (st:W64.t Array101.t, r64:int, trailb:W8.t) : 
  W64.t Array101.t = {
    
    st <- st;
    r64 <- r64;
    trailb <- trailb;
    st <@ _init_updstate_avx2x4 (st, r64, trailb);
    return st;
  }

  proc __addstate_bcast_avx2x4 (st:W256.t Array25.t, at:int, buf:W8.t A.t, off:int,
                                     upto:int) : int * int * W256.t Array25.t = {
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
      t128 <- (VMOV_64 t64);
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
      (WA.get64_direct (WA.init8 (fun i => A."_.[_]" buf i)) off));
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
      t128 <- (VMOV_64 t64);
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
  proc __absorb_bcast_avx2x4 (st:W64.t Array101.t, buf:W8.t A.t, len:int) : 
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
      (at, off, stk) <@ __addstate_bcast_avx2x4 (stk, at, buf, 
      off, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, stk) <@ __addstate_bcast_avx2x4 (stk, at, buf, 
    off, len);
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

  proc __addstate_avx2x4 (st:W256.t Array25.t, at:int, buf0:W8.t A.t, buf1:W8.t A.t, 
                          buf2:W8.t A.t, buf3:W8.t A.t, off:int, upto:int) 
                         : int * int * W256.t Array25.t = {

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
      t64 <- (WA.get64_direct (WA.init8 (fun i => A."_.[_]" buf0 i)) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      t64 <- (WA.get64_direct (WA.init8 (fun i => A."_.[_]" buf1 i)) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      t64 <- (WA.get64_direct (WA.init8 (fun i => A."_.[_]" buf2 i)) off);
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      t64 <- (WA.get64_direct (WA.init8 (fun i => A."_.[_]" buf3 i)) off);
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
      ( _3, t64) <@ RW.MM.__a_rlen_read_upto8 (buf0, off,
      (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 0)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 0)) `^`
      t64))));
      ( _4, t64) <@ RW.MM.__a_rlen_read_upto8 (buf1, off,
      (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 8)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8)) `^`
      t64))));
      ( _5, t64) <@ RW.MM.__a_rlen_read_upto8 (buf2, off,
      (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray800.get256
      (WArray800.set64_direct (WArray800.init256 (fun i => st.[i]))
      ((4 * at) + 16)
      ((get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16)) `^`
      t64))));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf3, off,
      (W64.to_uint upto8));
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
  proc __absorb_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t, buf1:W8.t A.t, 
                        buf2:W8.t A.t, buf3:W8.t A.t, len: int) : W64.t Array101.t = {
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
      (at, off, stk) <@ M.___add_updstate_avx2x4 (stk, at, buf0, buf1, 
      buf2, buf3, off, r8);
      (* Erased call to unspill *)
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, stk) <@ M.___add_updstate_avx2x4 (stk, at, buf0, buf1, 
    buf2, buf3, off, len);
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
  proc finish_updstate_avx2x4 (st:W64.t Array101.t) : W64.t Array101.t = {
    
    st <- st;
    st <@ _finish_updstate_avx2x4 (st);
    return st;
  }

  proc __dumpstate_avx2x4 (buf0:W8.t A.t, buf1:W8.t A.t,
                           buf2:W8.t A.t, buf3:W8.t A.t,
                           off:int, st:W256.t Array25.t, 
                           at:int, upto:int) : int * int *
  W8.t A.t * W8.t A.t * W8.t A.t * W8.t A.t = {
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
      (WA.set64_direct (WA.init8 (fun i => A."_.[_]" buf0 i)) off t64)));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 8));
      buf1 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => A."_.[_]" buf1 i)) off t64)));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 16));
      buf2 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => A."_.[_]" buf2 i)) off t64)));
      t64 <-
      (get64_direct (WArray800.init256 (fun i => st.[i])) ((4 * at) + 24));
      buf3 <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => A."_.[_]" buf3 i)) off t64)));
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
  proc __squeeze_avx2x4 (st:W64.t Array101.t, buf0:W8.t A.t,
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
      (at, off, buf0, buf1, buf2, buf3) <@ __dumpstate_avx2x4 (
      buf0, buf1, buf2, buf3, off, stk, at, r8);
      stk <@ M._keccakf1600_avx2x4 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, buf0, buf1, buf2, buf3) <@ __dumpstate_avx2x4 (
    buf0, buf1, buf2, buf3, off, stk, at, len);
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

(*
   BASIC OPERATORS
   ===============
*)

op u256_pack4 (w0 w1 w2 w3 : W64.t) : W256.t =
 W256.init (fun i => if i < 64 then w0.[i]
                     else if i < 128 then w1.[i-64]
                     else if i < 192 then w2.[i-128]
                     else w3.[i-192]).

op A100u64toA25u256 (st: W64.t Array100.t): W256.t Array25.t = 
  Array25.init (fun i => u256_pack4 st.[i*4] st.[i*4+1] st.[i*4+2] st.[i*4+3]).

op A101u64toA25u256 (st: W64.t Array101.t): W256.t Array25.t = 
  Array25.init (fun i => u256_pack4 st.[i*4] st.[i*4+1] st.[i*4+2] st.[i*4+3]).

op info_eq (w:W64.t) _tb _r8 _at =
  (w `&` (W64.of_int 255)) = W64.of_int _at /\
  (((w `>>>` 8) `&` (W64.of_int 255)) + W64.of_int 1) `<<<` 3 = W64.of_int _r8 /\
  ((w `>>>` 16) `&` (W64.of_int 255)) = W64.of_int _tb.

op state_eq (st : W64.t Array101.t) (st': W256.t Array25.t) _tb _r8 _at =
 info_eq st.[100] _tb _r8 _at /\ 
 A101u64toA25u256 st = st'.
 
op init_25_256 = Array25.init <:W256.t>.

op st4x0 = Array100.create W64.zero.

op st4x_pack (sts: state*state*state*state): state4x =
 init_25_256 (fun i => u256_pack4 sts.`1.[i] sts.`2.[i] sts.`3.[i] sts.`4.[i]).

op st4x_match st4x sts = (st4x = st4x_pack sts).

op addstate_avx2x4 (st: state4x, l0 l1 l2 l3: W8.t list): state4x.

op absorb_spec_avx2x4 (r8: int) (tb: int) (l0 l1 l2 l3: W8.t list) st4x =
 st4x_match st4x ( ABSORB1600 (W8.of_int tb) r8 l0
                 , ABSORB1600 (W8.of_int tb) r8 l1
                 , ABSORB1600 (W8.of_int tb) r8 l2
                 , ABSORB1600 (W8.of_int tb) r8 l3).

op pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 st4x: bool =
 0 < r8 <= 200 /\ size l1 = size l0 /\ size l2 = size l0 /\ size l3 = size l0 /\
 st4x_match st4x
 ( addstate (stateabsorb_iblocks (chunk r8 l0) st0) (bytes2state (chunkremains r8 l0)),
   addstate (stateabsorb_iblocks (chunk r8 l1) st0) (bytes2state (chunkremains r8 l1)),
   addstate (stateabsorb_iblocks (chunk r8 l2) st0) (bytes2state (chunkremains r8 l2)),
   addstate (stateabsorb_iblocks (chunk r8 l3) st0) (bytes2state (chunkremains r8 l3))).


(*
   ONE-SHOT (UPDSTATE) INIT
   ========================
*)

lemma init_updstate_avx2x4_ll: islossless MM.init_updstate_avx2x4.
proof.
admitted.

hoare init_updstate_avx2x4_h _tb _r8:
  MM.init_updstate_avx2x4
  : to_uint trailb = _tb /\ (r64 `<<` 3) = _r8
==> 
  state_eq res (A100u64toA25u256 st4x0) _tb _r8 0.
admitted.

phoare init_updstate_avx2x4_ph _tb _r8:
 [ MM.init_updstate_avx2x4
  : to_uint trailb = _tb /\ (r64 `<<` 3) = _r8
==> 
  state_eq res (A100u64toA25u256 st4x0) _tb _r8 0] = 1%r.
proof.
by conseq init_updstate_avx2x4_ll (init_updstate_avx2x4_h _tb _r8).
qed.

(*
   INCREMENTAL (UPDSTATE) ARRAY ABSORB
   ===================================
*)

lemma add_bcast_updstate_avx2x4_ll: islossless MM.__addstate_bcast_avx2x4.
proof.
admitted.
(*
proc.
seq 7: true => //.
 while true (32 * (aT %/ 8 + _LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
 by auto => /#.
sp; if => //.
by wp; call a_ilen_read_bcast_upto8_at_ll; auto => /#.
qed.
*)

lemma addstate_avx2x4_ll: islossless MM.__addstate_avx2x4.
proof.
admitted.
(*
proc.
seq 7: true => //.
 while true (4 * (aT %/ 8) + 4 * (_LEN %/ 8)-at).
  by move=> z; auto => /#.
 sp; if => //.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  wp; call a_ilen_read_upto8_at_ll.
  by auto => /#.
 by auto => /#.
sp; if => //.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
wp; call a_ilen_read_upto8_at_ll.
by auto => /#.
qed.
*)

lemma absorb_bcast_avx2x4_ll: islossless MM.__absorb_bcast_avx2x4.
proof.
admitted.
(*
proc.
seq 4: true => //.
 call addstate_bcast_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_bcast_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 wp; call addstate_bcast_avx2x4_ll.
 by auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.
*)

hoare ststatus_data_avx2x4 _tb _r8 _at:
  MM._ststatus_data_avx2x4
  : info_eq arg  _tb _r8 _at /\
    (* Extra condition based on the procedure definition *)
    0 <= _r8 < 200 
  ==> res = (W64.of_int _tb, _r8, _at).
admitted.


hoare absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _tb _r8 _at:
 MM.__absorb_bcast_avx2x4
 : state_eq st _st _tb _r8 _at /\ buf = _buf /\
  _at = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ 
    size _l3 = size _l0 /\ 
  pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> pabsorb_spec_avx2x4 _r8
     (_l0 ++ A.to_list _buf)
     (_l1 ++ A.to_list _buf)
     (_l2 ++ A.to_list _buf)
     (_l3 ++ A.to_list _buf)
     (A101u64toA25u256 res)
     /\ info_eq res.[100] _tb _r8 ((size _l0 + _ASIZE)%%_r8).
proof.
proc.
admitted.

phoare absorb_bcast_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf _tb _r8 _at:
 [ MM.__absorb_bcast_avx2x4
 : state_eq st _st _tb _r8 _at /\ buf = _buf /\
  _at = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ 
    size _l3 = size _l0 /\ 
  pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> pabsorb_spec_avx2x4 _r8
     (_l0 ++ A.to_list _buf)
     (_l1 ++ A.to_list _buf)
     (_l2 ++ A.to_list _buf)
     (_l3 ++ A.to_list _buf)
     (A101u64toA25u256 res)
     /\ info_eq res.[100] _tb _r8 ((size _l0 + _ASIZE)%%_r8)
  ] = 1%r.
proof.
by conseq absorb_bcast_avx2x4_ll (absorb_bcast_avx2x4_h _l0 _l1 _l2 _l3 _st _buf _tb _r8 _at).
qed.

lemma absorb_avx2x4_ll: islossless MM.__absorb_avx2x4.
proof.
admitted.
(*
proc.
seq 4: true => //.
 call addstate_avx2x4_ll.
 sp; if => //.
 wp; while true (iTERS-i).
  move => z.
  wp; call keccakf1600_avx2x4_ll.
  call addstate_avx2x4_ll.
  by auto => /#.
 wp; call keccakf1600_avx2x4_ll.
 by wp; call addstate_avx2x4_ll; auto => /#.
if => //.
by call addratebit_avx2x4_ll.
qed.
*)

hoare absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8 _at:
 MM.__absorb_avx2x4
 : state_eq st _st _tb _r8 _at /\ 
   buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
  _at = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ 
    size _l3 = size _l0 /\ 
  pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> pabsorb_spec_avx2x4 _r8
     (_l0 ++ A.to_list _buf0)
     (_l1 ++ A.to_list _buf1)
     (_l2 ++ A.to_list _buf2)
     (_l3 ++ A.to_list _buf3)
     (A101u64toA25u256 res)
     /\ info_eq res.[100] _tb _r8 ((size _l0 + _ASIZE)%%_r8).
admitted.

phoare absorb_avx2x4_ph _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8 _at:
 [ MM.__absorb_avx2x4
 : state_eq st _st _tb _r8 _at /\ 
   buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
  _at = size _l0 %% _r8 /\ size _l1 = size _l0 /\ size _l2 = size _l0 /\ 
    size _l3 = size _l0 /\
  pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st
 ==> pabsorb_spec_avx2x4 _r8
     (_l0 ++ A.to_list _buf0)
     (_l1 ++ A.to_list _buf1)
     (_l2 ++ A.to_list _buf2)
     (_l3 ++ A.to_list _buf3)
     (A101u64toA25u256 res)
     /\ info_eq res.[100] _tb _r8 ((size _l0 + _ASIZE)%%_r8)
  ] = 1%r.
proof.
by conseq absorb_avx2x4_ll (absorb_avx2x4_h _l0 _l1 _l2 _l3 _st _buf0 _buf1 _buf2 _buf3 _tb _r8 _at).
qed.

(*
   ONE-SHOT (UPDSTATE) FINISH
   ==========================
*)


lemma finish_avx2x4_ll: islossless MM.finish_updstate_avx2x4.
proof.
admitted.
print MM.

hoare finish_avx2x4_h _l0 _l1 _l2 _l3 _st _tb _r8 _at:
 MM.finish_updstate_avx2x4
 : pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st /\
   state_eq st _st _tb _r8 _at 
==> 
    absorb_spec_avx2x4 _r8 _tb _l0 _l1 _l2 _l3 (A101u64toA25u256 res).
proof.
admitted.

phoare finish_avx2x4_ph _l0 _l1 _l2 _l3 _st _tb _r8 _at:
 [MM.finish_updstate_avx2x4
 : pabsorb_spec_avx2x4 _r8 _l0 _l1 _l2 _l3 _st /\ 
   state_eq st _st _tb _r8 _at 
==> 
    absorb_spec_avx2x4 _r8 _tb _l0 _l1 _l2 _l3 (A101u64toA25u256 res)] = 1%r.
proof.
by conseq finish_avx2x4_ll (finish_avx2x4_h _l0 _l1 _l2 _l3 _st _tb _r8 _at).
qed.

(*
   ONE-SHOT (UPDSTATE) ARRAY SQUEEZE
   ====================================
*)

lemma dumpstate_avx2x4_ll: islossless MM.__dumpstate_avx2x4.
proof.
admitted.
(*
proc.
seq 3: true => //.
 while true (8 * (_LEN %/ 8)-i).
  by move=> z; auto => /#.
 while true (32 * (_LEN %/ 32)-i).
  by move=> z; inline*; auto => /#.
 by auto => /#.
if => //.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
wp; call a_ilen_write_upto8_ll.
by auto => /#.
qed.
*)

hoare dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st:
 MM.__dumpstate_avx2x4
 : st = _st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
   off = _off /\ (upto - at) = _len /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE
 ==> res.`2 = _off + _len
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`5 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`6 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3.
admitted.

phoare dumpstate_avx2x4_ph _buf0 _buf1 _buf2 _buf3 _off _len _st:
 [ MM.__dumpstate_avx2x4
 : st = _st /\ buf0=_buf0 /\ buf1=_buf1 /\ buf2=_buf2 /\ buf3=_buf3 /\
   off = _off /\ (upto - at) = _len /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE
 ==> res.`2 = _off + _len
  /\ res.`3 = A.fill (fun i=> (stbytes (st4x_get _st 0)).[i-_off]) _off _len _buf0
  /\ res.`4 = A.fill (fun i=> (stbytes (st4x_get _st 1)).[i-_off]) _off _len _buf1
  /\ res.`5 = A.fill (fun i=> (stbytes (st4x_get _st 2)).[i-_off]) _off _len _buf2
  /\ res.`6 = A.fill (fun i=> (stbytes (st4x_get _st 3)).[i-_off]) _off _len _buf3
  ] = 1%r.
proof.
by conseq dumpstate_avx2x4_ll (dumpstate_avx2x4_h _buf0 _buf1 _buf2 _buf3 _off _len _st).
qed.

lemma squeeze_avx2x4_ll: islossless MM.__squeeze_avx2x4.
proof.
admitted.
(*
proc.
seq 5: true => //.
 sp; if => //.
 while true (iTERS-i).
  move=> z.
  wp; call dumpstate_avx2x4_ll.
  wp; call keccakf1600_avx2x4_ll.
  by auto => /#. 
 by auto => /#.
if => //.
call  dumpstate_avx2x4_ll.
by call keccakf1600_avx2x4_ll; auto => /#.
qed.
*)
(* tHIS IS A SPECIFIC VALUE FOR SHAKE256 - MAKE IT GENERIC *)
op _RATE8: int = 136.

hoare squeeze_avx2x4_h _st _r8:
 MM.__squeeze_avx2x4
 : A101u64toA25u256 st = _st /\ _RATE8 = _r8 /\ 0 < _r8 <= 200
 ==>
    A101u64toA25u256 res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ res.`2 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0))
 /\ res.`3 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1))
 /\ res.`4 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2))
 /\ res.`5 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3)).
admitted.

phoare squeeze_avx2x4_ph _st _r8:
 [ MM.__squeeze_avx2x4
 : A101u64toA25u256 st = _st /\ _RATE8 = _r8 /\ 0 < _r8 <= 200
 ==>
    A101u64toA25u256 res.`1 = iter ((_ASIZE - 1) %/ _r8 + 1) keccak_f1600_x4 _st
 /\ res.`2 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 0))
 /\ res.`3 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 1))
 /\ res.`4 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 2))
 /\ res.`5 = A.of_list W8.zero (SQUEEZE1600 _r8 _ASIZE (st4x_get _st 3))
 ] = 1%r.
proof.
by conseq squeeze_avx2x4_ll (squeeze_avx2x4_h _st _r8).
qed.

end KeccakArrayAvx2x4.


