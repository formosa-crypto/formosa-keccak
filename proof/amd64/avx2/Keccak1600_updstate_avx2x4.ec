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
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccak1600_Spec Keccakf1600_Spec.

require export Keccak1600_avx2x4 Keccakf1600_avx2x4.
require import Keccak1600_subreadwrite.


(* my proposed operators - these use a lot of the fixed_size operators *)
(*
op info_eq (w:W64.t) _tb _r8 _at =
  (w `&` (W64.of_int 255)) = W64.of_int _at /\
  (((w `>>>` 8) `&` (W64.of_int 255)) + W64.of_int 1) `<<<` 3 = W64.of_int _r8 /\
  ((w `>>>` 16) `&` (W64.of_int 255)) = W64.of_int _tb.
*)
op state_word tb r8 at =
W64.bits2w (nseq 40 false ++ 
            W64.w2bits (W64.of_int tb) ++ 
            W8.w2bits (W8.of_int (r8-1)) ++ 
            W8.w2bits (W8.of_int at)).

op status_spec w tb r8 at =
 w = state_word tb r8 at.

op u256_pack4 (w0 w1 w2 w3 : W64.t) : W256.t =
   W256.init (fun i => if i < 64 then w0.[i]
                       else if i < 128 then w1.[i-64]
                       else if i < 192 then w2.[i-128]
                       else w3.[i-192]).

op A101u64toA25u256 (st: W64.t Array101.t): W256.t Array25.t = 
  Array25.init (fun i => u256_pack4 st.[i*4] st.[i*4+1] st.[i*4+2] st.[i*4+3]).

op state_eq (st : W64.t Array101.t) (st': W256.t Array25.t) _tb _r8 _at =
 status_spec st.[100] _tb _r8 _at /\ 
 A101u64toA25u256 st = st'.


(* ------------------------------------------------------------------------- *)
(* Size-independent flat layer (x4, 4-way parallel).                         *)
(*                                                                           *)
(* Only `_init_updstate_avx2x4` and `_finish_updstate_avx2x4` are            *)
(* size-independent — `_absorb_m_updstate_avx2x4` internally calls the       *)
(* array-buffer add proc, so the memory variant doesn't extract into         *)
(* `Keccak1600_Jazz` (it lives in the abstract theory's MM via the array     *)
(* `absorb_updstate_avx2x4`). Clients drive 4-way SHA3 / SHAKE via:          *)
(*                                                                           *)
(*   init_updstate_avx2x4                                                    *)
(*   absorb_updstate_avx2x4 (size-dep, in abstract theory)                   *)
(*   finish_updstate_avx2x4                                                  *)
(*   squeeze_updstate_avx2x4 (size-dep, in abstract theory)                  *)
(*                                                                           *)
(* The viewers `absorb_msg_x4` / `sponge_state_x4` are 4-tuples (one per     *)
(* lane); rate8/trailb are shared across lanes (single ststatus word).       *)
(* ------------------------------------------------------------------------- *)


(* Concrete decoder for the x4 ststatus, mirroring `_ststatus_data_avx2x4`.
   (Differs from the x1 spec only in returning `trailb` boxed as W64 to
   match the proc's signature.) *)
op ststatus_data_avx2x4_spec (s : W64.t) : W64.t * int * int =
  let raw_at  = W64.to_uint s %% 256 in
  let raw_r8  = (((W64.to_uint s %/ 256) %% 256) + 1) * 8 in
  let r8      = if 200 < raw_r8 then 200 else raw_r8 in
  let at      = if r8 <= raw_at then 0 else raw_at in
  let trailb  = W64.of_int ((W64.to_uint s %/ 65536) %% 256) in
  (trailb, r8, at).

op rate8_of_x4  (st : W64.t Array101.t) : int  = (ststatus_data_avx2x4_spec st.[100]).`2.
op trailb_of_x4 (st : W64.t Array101.t) : W8.t =
  W8.of_int (W64.to_uint (ststatus_data_avx2x4_spec st.[100]).`1).


(* Reuse the x1 ststatus packer. *)
op encode_ststatus_x4 (at r8m1 trailb : int) : W64.t =
  W64.of_int (at + 256 * r8m1 + 65536 * trailb).

(* Concrete spec for x4 init: zeros all 4 lane states (st[0..99]),
   packs ststatus into st[100]. *)
op init_updstate_avx2x4_spec
    (_st : W64.t Array101.t) (r64 : int) (trailb : W8.t)
  : W64.t Array101.t =
  Array101.init (fun i =>
    if i < 100 then W64.zero
    else encode_ststatus_x4 0 (r64 - 1) (W8.to_uint trailb)).

(* Opaque spec for x4 finish: the SoA byte indexing makes a closed-form
   body verbose; the client only relies on the `sponge_state_x4_finish`
   composition lemma below, which fully pins it down. *)
op finish_updstate_avx2x4_spec : W64.t Array101.t -> W64.t Array101.t.


(* ------------------------------------------------------------------------- *)
(* Per-lane sponge-phase viewers (opaque). Each is a 4-tuple (one entry per  *)
(* lane).                                                                     *)
(* ------------------------------------------------------------------------- *)

op absorb_msg_x4 :
  W64.t Array101.t -> W8.t list * W8.t list * W8.t list * W8.t list.

op sponge_state_x4 :
  W64.t Array101.t
  -> W64.t Array25.t * W64.t Array25.t * W64.t Array25.t * W64.t Array25.t.


(* ------------------------------------------------------------------------- *)
(* Flat (size-indep) `_ll` / `_h` / `_ph` triples for init / finish.         *)
(* ------------------------------------------------------------------------- *)

lemma init_updstate_avx2x4_ll: islossless M._init_updstate_avx2x4.
proof. admitted.

hoare init_updstate_avx2x4_h _r8 _tb:
  M._init_updstate_avx2x4
  : to_uint trailb = _tb /\ (r64 `<<` 3) = _r8
  ==> state_eq res st4x0 _tb _r8 0.
proof. admitted.

phoare init_updstate_avx2x4_ph _r8 _tb:
  [ M._init_updstate_avx2x4
  : to_uint trailb = _tb /\ (r64 `<<` 3) = _r8
  ==> state_eq res st4x0 _tb _r8 0
  ] = 1%r.
proof.
by conseq init_updstate_avx2x4_ll
       (init_updstate_avx2x4_h _r8 _tb).
qed.


lemma finish_updstate_avx2x4_ll: islossless M._finish_updstate_avx2x4.
proof. admitted.

hoare finish_updstate_avx2x4_h l0 l1 l2 l3 tb r8:
  M._finish_updstate_avx2x4
  :pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) 
  ==>
   absorb_spec_avx2x4 r8 tb l0 l1 l2 l3 (A101u64toA25u256 res).
proof. admitted.

phoare finish_updstate_avx2x4_ph l0 l1 l2 l3 tb r8:
  [ M._finish_updstate_avx2x4
  : pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) 
  ==> 
   absorb_spec_avx2x4 r8 tb l0 l1 l2 l3 (A101u64toA25u256 res)
  ] = 1%r.
proof.
by conseq finish_updstate_avx2x4_ll (finish_updstate_avx2x4_h l0 l1 l2 l3 tb r8).
qed.


(* ------------------------------------------------------------------------- *)
(* Client-facing composition lemmas (admitted) — flat half.                   *)
(* ------------------------------------------------------------------------- *)

(* (1) init produces empty absorb buffers in all 4 lanes; rate/trailb set. *)
lemma absorb_msg_x4_init _st r64 trailb:
  absorb_msg_x4 (init_updstate_avx2x4_spec _st r64 trailb) = ([], [], [], [])
  /\ rate8_of_x4  (init_updstate_avx2x4_spec _st r64 trailb) = r64 * 8
  /\ trailb_of_x4 (init_updstate_avx2x4_spec _st r64 trailb) = trailb.
proof. admitted.

(* (3) finish closes the absorb phase in all 4 lanes simultaneously: each
       lane's resulting sponge state equals ABSORB1600 over its own
       accumulated message. *)
lemma sponge_state_x4_finish _st:
  let m  = absorb_msg_x4 _st in
  let r8 = rate8_of_x4 _st in
  let tb = trailb_of_x4 _st in
  sponge_state_x4 (finish_updstate_avx2x4_spec _st) =
    ( ABSORB1600 tb r8 m.`1
    , ABSORB1600 tb r8 m.`2
    , ABSORB1600 tb r8 m.`3
    , ABSORB1600 tb r8 m.`4 )
  /\ rate8_of_x4 (finish_updstate_avx2x4_spec _st) = r8.
proof. admitted.


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

(* ststatus_data_avx2x4_spec is defined in the flat scope above (concrete body). *)

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

hoare ststatus_data_avx2x4_h _tb _r8 _at:
  MM._ststatus_data_avx2x4
  : status_spec arg _tb _r8 _at
  ==> res = (W64.of_int _tb, _r8, _at).
proof. admitted.

phoare ststatus_data_avx2x4_ph _tb _r8 _at:
  [ MM._ststatus_data_avx2x4
  : status_spec arg _tb _r8 _at
  ==> res = (W64.of_int _tb, _r8, _at) ] = 1%r.
proof. by conseq ststatus_data_avx2x4_ll (ststatus_data_avx2x4_h _tb _r8 _at). qed.


(* Did not touch the add_updstate definitions *)
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


(* Did not touch the add_bcast definitions *)
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

hoare absorb_updstate_avx2x4_h l0 l1 l2 l3 _b0 _b1 _b2 _b3 tb r8 at _len:
  MM._absorb_updstate_avx2x4
  : pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) /\ 
    status_spec st.[100] tb r8 at /\ buf0 = _b0 /\ buf1 = _b1 /\
    buf2 = _b2 /\ buf3 = _b3 /\ len = _len /\ _len <= _ASIZE
  ==> 
    status_spec res.[100] tb r8 (at+_len) /\
    if _len < _ASIZE then
      pabsorb_spec_avx2x4 r8 
      (l0 ++ take _len (A.to_list _b0))
      (l1 ++ take _len (A.to_list _b1))
      (l2 ++ take _len (A.to_list _b2))
      (l3 ++ take _len (A.to_list _b3))
      (A101u64toA25u256 res)
    else  pabsorb_spec_avx2x4 r8 
      (l0 ++ A.to_list _b0)
      (l1 ++ A.to_list _b1)
      (l2 ++ A.to_list _b2)
      (l3 ++ A.to_list _b3)
      (A101u64toA25u256 res).
proof. admitted.

phoare absorb_updstate_avx2x4_ph l0 l1 l2 l3 _b0 _b1 _b2 _b3 tb r8 at _len:
  [ MM._absorb_updstate_avx2x4
  : pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) /\ 
    status_spec st.[100] tb r8 at /\ buf0 = _b0 /\ buf1 = _b1 /\
    buf2 = _b2 /\ buf3 = _b3 /\ len = _len /\ _len <= _ASIZE
  ==> 
    status_spec res.[100] tb r8 (at+_len) /\
    if _len < _ASIZE then
      pabsorb_spec_avx2x4 r8 
      (l0 ++ take _len (A.to_list _b0))
      (l1 ++ take _len (A.to_list _b1))
      (l2 ++ take _len (A.to_list _b2))
      (l3 ++ take _len (A.to_list _b3))
      (A101u64toA25u256 res)
    else  pabsorb_spec_avx2x4 r8 
      (l0 ++ A.to_list _b0)
      (l1 ++ A.to_list _b1)
      (l2 ++ A.to_list _b2)
      (l3 ++ A.to_list _b3)
      (A101u64toA25u256 res)] = 1%r.
proof.
by conseq absorb_updstate_avx2x4_ll
       (absorb_updstate_avx2x4_h l0 l1 l2 l3 _b0 _b1 _b2 _b3 tb r8 at _len).
qed.


lemma absorb_bcast_updstate_avx2x4_ll: islossless MM._absorb_bcast_updstate_avx2x4.
proof. admitted.

hoare absorb_bcast_updstate_avx2x4_h l0 l1 l2 l3 _buf tb r8 at _len:
  MM._absorb_bcast_updstate_avx2x4
  : pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) /\ 
    status_spec st.[100] tb r8 at /\ buf = _buf /\ len = _len /\
    _len <= _ASIZE
  ==> 
    status_spec res.[100] tb r8 (at+_len) /\
    if _len < _ASIZE then
      pabsorb_spec_avx2x4 r8 
      (l0 ++ take _len (A.to_list _buf))
      (l1 ++ take _len (A.to_list _buf))
      (l2 ++ take _len (A.to_list _buf))
      (l3 ++ take _len (A.to_list _buf))
      (A101u64toA25u256 res)
    else  pabsorb_spec_avx2x4 r8 
      (l0 ++ A.to_list _buf)
      (l1 ++ A.to_list _buf)
      (l2 ++ A.to_list _buf)
      (l3 ++ A.to_list _buf)
      (A101u64toA25u256 res).
proof. admitted.

phoare absorb_bcast_updstate_avx2x4_ph l0 l1 l2 l3 _buf tb r8 at _len:
  [ MM._absorb_bcast_updstate_avx2x4
  : pabsorb_spec_avx2x4 r8 l0 l1 l2 l3 (A101u64toA25u256 st) /\ 
    status_spec st.[100] tb r8 at /\ buf = _buf /\ len = _len /\
    _len <= _ASIZE
  ==> 
    status_spec res.[100] tb r8 (at+_len) /\
    if _len < _ASIZE then
      pabsorb_spec_avx2x4 r8 
      (l0 ++ take _len (A.to_list _buf))
      (l1 ++ take _len (A.to_list _buf))
      (l2 ++ take _len (A.to_list _buf))
      (l3 ++ take _len (A.to_list _buf))
      (A101u64toA25u256 res)
    else  pabsorb_spec_avx2x4 r8 
      (l0 ++ A.to_list _buf)
      (l1 ++ A.to_list _buf)
      (l2 ++ A.to_list _buf)
      (l3 ++ A.to_list _buf)
      (A101u64toA25u256 res)] = 1%r.
proof.
by conseq absorb_bcast_updstate_avx2x4_ll
       (absorb_bcast_updstate_avx2x4_h l0 l1 l2 l3 _buf tb r8 at _len).
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

hoare squeeze_updstate_avx2x4_h _st r8 _len:
  MM._squeeze_updstate_avx2x4
  : (A101u64toA25u256 st) = _st /\ len = _len /\ _len <= _ASIZE
  ==> 
    A101u64toA25u256 res.`1 = iter ((_ASIZE - 1) %/ r8 + 1) keccak_f1600_x4 _st
 /\ res.`2 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 0))
 /\ res.`3 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 1))
 /\ res.`4 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 2))
 /\ res.`5 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 3)).
proof. admitted.

phoare squeeze_updstate_avx2x4_ph _st r8 _len:
  [ MM._squeeze_updstate_avx2x4
  : (A101u64toA25u256 st) = _st /\ len = _len /\ _len <= _ASIZE
  ==> 
    A101u64toA25u256 res.`1 = iter ((_ASIZE - 1) %/ r8 + 1) keccak_f1600_x4 _st 
 /\ res.`2 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 0))
 /\ res.`3 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 1))
 /\ res.`4 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 2))
 /\ res.`5 = A.of_list W8.zero (SQUEEZE1600 r8 _len (st4x_get _st 3))] = 1%r.
proof.
by conseq squeeze_updstate_avx2x4_ll
       (squeeze_updstate_avx2x4_h _st r8 _len).
qed.


(* ----------------------------------------------------------------------- *)
(* Client-facing composition lemmas (admitted) for the size-dependent      *)
(* absorb / absorb_bcast / squeeze procs (4-way).                          *)
(* ----------------------------------------------------------------------- *)

(* (2) absorb: each lane's absorb buffer is extended by the first `len`
       bytes of its respective input buffer. *)
lemma absorb_msg_x4_absorb _st _b0 _b1 _b2 _b3 _len:
  let m  = absorb_msg_x4 _st in
  let st' = absorb_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len in
  absorb_msg_x4 st' =
    ( m.`1 ++ take _len (A.to_list _b0)
    , m.`2 ++ take _len (A.to_list _b1)
    , m.`3 ++ take _len (A.to_list _b2)
    , m.`4 ++ take _len (A.to_list _b3) )
  /\ rate8_of_x4  st' = rate8_of_x4 _st
  /\ trailb_of_x4 st' = trailb_of_x4 _st.
proof. admitted.

(* (2') absorb_bcast: all 4 lanes absorb the same buffer slice. *)
lemma absorb_msg_x4_absorb_bcast _st _buf _len:
  let m  = absorb_msg_x4 _st in
  let st' = absorb_bcast_updstate_avx2x4_spec _st _buf _len in
  let new = m.`1 ++ take _len (A.to_list _buf) in
  absorb_msg_x4 st' = (new, new, new, new)
  /\ rate8_of_x4  st' = rate8_of_x4 _st
  /\ trailb_of_x4 st' = trailb_of_x4 _st
  /\ absorb_msg_x4 _st = (m.`1, m.`1, m.`1, m.`1).  (* pre: bcast assumes all lanes equal *)
proof. admitted.

(* (5) squeeze: each lane's output buffer (first `len` bytes) equals
       SQUEEZE1600 of that lane's sponge state. *)
lemma squeeze_yields_bytes_x4 _st _b0 _b1 _b2 _b3 _len:
  let (_, b0', b1', b2', b3') = squeeze_updstate_avx2x4_spec _st _b0 _b1 _b2 _b3 _len in
  let s  = sponge_state_x4 _st in
  let r8 = rate8_of_x4 _st in
  take _len (A.to_list b0') = SQUEEZE1600 r8 _len s.`1
  /\ take _len (A.to_list b1') = SQUEEZE1600 r8 _len s.`2
  /\ take _len (A.to_list b2') = SQUEEZE1600 r8 _len s.`3
  /\ take _len (A.to_list b3') = SQUEEZE1600 r8 _len s.`4.
proof. admitted.

end KeccakUpdstateAvx2x4.
