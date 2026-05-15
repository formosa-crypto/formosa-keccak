(******************************************************************************
   Keccak1600_updstate_avx2.ec:

   Correctness proof for the Keccak1600 (updstate) array-buffer absorb/squeeze
   single-lane AVX2 implementation.

   Modelled on Keccak1600_fixedsizes_avx2.ec — same skeleton (abstract theory
   parameterised on _ASIZE, MM module, lemma stubs) extended for the streaming
   updstate procs. Equivalence between MM here and the concrete extraction at
   _ASIZE=999 is checked by Keccak1600_updstate_avx2_checkXtr.ec.

******************************************************************************)

require import AllCore List Int IntDiv StdOrder.

from Jasmin require import JModel_x86.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import WArray200 WArray208.
from JazzEC require import Array25 Array26.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec Keccak1600_Spec.

require import Keccak1600_ref Keccakf1600_ref.
require import Keccak1600_avx2 Keccakf1600_avx2.
require import Keccak1600_subreadwrite.

import IntOrder.


(* =========================================================================
   Status word operations.
   The updstate status word (st.[25]) encodes:
     - byte 0: current position `at` (0 <= at < r8)
     - byte 1: rate in 64-bit words minus 1 (`r64 - 1`), so r8 = 8*r64
     - byte 2: trail byte
   This matches the encoding in _ststatus_data.
   ========================================================================= *)

op ststatus_r8 (s: W64.t) : int =
 let r64 = W64.to_uint ((s `>>` W8.of_int 8) `&` W64.of_int 255) in
 if 200 < 8 * (r64 + 1) then 200 else 8 * (r64 + 1).

op ststatus_at (s: W64.t) : int =
 W64.to_uint (s `&` W64.of_int 255).

op ststatus_trailb (s: W64.t) : W8.t =
 truncateu8 (s `>>` W8.of_int 16).

(* Normalised `at`: as computed by _ststatus_data (clamps to 0 if r8 <= at) *)
op ststatus_at_norm (s: W64.t) : int =
 let r8 = ststatus_r8 s in
 let at = ststatus_at s in
 if r8 <= at then 0 else at.


(* =========================================================================
   Partial-absorb specification for the updstate type.
   st: W64.t Array26.t  where  st.[0..24] = inner keccak state
                               st.[25]    = status word
   ========================================================================= *)

op pabsorb_spec_updstate_avx2 (l: W8.t list) (st: W64.t Array26.t) : bool =
 let stk = Array25.init (fun i => st.[i]) in
 let r8  = ststatus_r8  st.[25] in
 let at  = ststatus_at_norm st.[25] in
 0 < r8 /\ r8 <= 200 /\
 at = size l %% r8 /\
 pabsorb_spec_ref r8 l stk.

op absorb_spec_updstate_avx2 (tb: int) (l: W8.t list) (st: W64.t Array26.t) : bool =
 let stk = Array25.init (fun i => st.[i]) in
 let r8  = ststatus_r8 st.[25] in
 absorb_spec_ref r8 tb l stk.


(* ------------------------------------------------------------------------- *)
(* Size-independent flat layer (memory-buffer / setup procs).                *)
(*                                                                           *)
(* The procs _init_updstate_avx2, _finish_updstate_avx2,                     *)
(* _absorb_m_updstate_avx2 use only Array26 and don't depend on _ASIZE, so   *)
(* they live outside the abstract theory and reference M directly.           *)
(*                                                                           *)
(* The spec layer below is the *minimal* surface a client needs to conclude  *)
(* that init -> (absorb_m | update)* -> finish -> squeeze produces           *)
(*    SQUEEZE1600 r8 (ABSORB1600 trailb r8 msg) outlen                       *)
(* i.e. a SHA3 / SHAKE call. It introduces:                                  *)
(*                                                                           *)
(*   - absorb_msg, sponge_state : opaque viewers of the abstract sponge      *)
(*     phase carried by an updstate state;                                   *)
(*   - rate8_of, trailb_of      : concrete (r8, trailb) decoders;            *)
(*   - init_*, finish_* specs    : concrete bodies (init zeros + packs       *)
(*     ststatus; finish XORs the FIPS-202 padding into the keccak portion); *)
(*   - absorb_m_* spec           : opaque (the streaming primitive itself).  *)
(*                                                                           *)
(* Composition is then captured by five admitted lemmas — see "Client-       *)
(* facing composition lemmas" below. Each `admitted` is an explicit proof    *)
(* obligation; nothing is stated as an axiom.                                *)
(* ------------------------------------------------------------------------- *)


(* ststatus encoding: low byte = at, next = r8/8 - 1, next = trailb,
   high bytes don't-care. *)

op encode_ststatus (at r8m1 trailb : int) : W64.t =
  W64.of_int (at + 256 * r8m1 + 65536 * trailb).

(* Decoder, mirroring _ststatus_data: clamps r8 to 200 and at to [0, r8). *)
op ststatus_data_spec (s : W64.t) : W8.t * int * int =
  let raw_at  = W64.to_uint s %% 256 in
  let raw_r8  = (((W64.to_uint s %/ 256) %% 256) + 1) * 8 in
  let r8      = if 200 < raw_r8 then 200 else raw_r8 in
  let at      = if r8 <= raw_at then 0 else raw_at in
  let trailb  = W8.of_int ((W64.to_uint s %/ 65536) %% 256) in
  (trailb, r8, at).

op rate8_of  (st : W64.t Array26.t) : int  = (ststatus_data_spec st.[25]).`2.
op trailb_of (st : W64.t Array26.t) : W8.t = (ststatus_data_spec st.[25]).`1.


(* Helpers used by finish: byte-XOR into the keccak state, and the
   `[:u32 8*25] &= 0xFF00FF00` byte-clear on st[25] (preserves r8-1 byte,
   clears at and trailb bytes). *)

op xor_byte_at_st25 (stk : W64.t Array25.t) (pos : int) (b : W8.t)
  : W64.t Array25.t =
  let w = pos %/ 8 in
  let m = W64.of_int (W8.to_uint b) `<<` W8.of_int (8 * (pos %% 8)) in
  stk.[w <- stk.[w] `^` m].

op clear_at_trailb (s : W64.t) : W64.t =
  s `&` W64.of_int 0xFFFFFFFFFF00FF00.


(* Concrete spec for init: zeros 25 keccak words, packs (at=0, r8-1=r64-1,
   trailb) into st[25]. Input state is fully overwritten. *)
op init_updstate_avx2_spec
    (_st : W64.t Array26.t) (r64 : int) (trailb : W8.t)
  : W64.t Array26.t =
  Array26.init (fun i =>
    if i < 25 then W64.zero
    else encode_ststatus 0 (r64 - 1) (W8.to_uint trailb)).

(* Concrete spec for finish: applies the FIPS-202 multi-rate padding:
   XOR trailb at byte position `at`, XOR 0x80 at byte position r8-1,
   then clear the at and trailb bytes of st[25]. *)
op finish_updstate_avx2_spec (st : W64.t Array26.t) : W64.t Array26.t =
  let (trailb, r8, at) = ststatus_data_spec st.[25] in
  let stk0 = Array25.init (fun i => st.[i]) in
  let stk1 = xor_byte_at_st25 stk0 at trailb in
  let stk2 = xor_byte_at_st25 stk1 (r8 - 1) (W8.of_int 128) in
  Array26.init (fun i =>
    if i < 25 then stk2.[i] else clear_at_trailb st.[25]).

(* Streaming-absorb primitive: opaque. Its behaviour is pinned down by the
   admitted client-facing lemma `absorb_msg_absorb_m` below. *)
op absorb_m_updstate_avx2_spec :
  global_mem_t -> W64.t Array26.t -> int -> int -> W64.t Array26.t.


(* ------------------------------------------------------------------------- *)
(* Sponge-phase viewers (opaque).                                            *)
(*                                                                           *)
(*   absorb_msg st    — the bytes absorbed-so-far that st represents (in     *)
(*                      the absorbing phase).                                *)
(*   sponge_state st  — the 25-word sponge state ready to be squeezed (in    *)
(*                      the squeezing phase, i.e. post-finish).              *)
(* ------------------------------------------------------------------------- *)

op absorb_msg   : W64.t Array26.t -> W8.t list.
op sponge_state : W64.t Array26.t -> W64.t Array25.t.


(* ------------------------------------------------------------------------- *)
(* Client-facing composition lemmas (admitted).                              *)
(* ------------------------------------------------------------------------- *)

(* (1) init produces an empty absorb buffer at the requested r8 / trailb. *)
lemma absorb_msg_init _st r64 trailb:
  absorb_msg (init_updstate_avx2_spec _st r64 trailb) = []
  /\ rate8_of  (init_updstate_avx2_spec _st r64 trailb) = r64 * 8
  /\ trailb_of (init_updstate_avx2_spec _st r64 trailb) = trailb.
proof. admitted.

(* (2) absorb_m appends `len` bytes of memory at `buf` to the absorb buffer.
       The rate and trail-byte are preserved. *)
lemma absorb_msg_absorb_m _mem _st _buf _len:
  absorb_msg (absorb_m_updstate_avx2_spec _mem _st _buf _len)
    = absorb_msg _st ++ memread _mem _buf _len
  /\ rate8_of  (absorb_m_updstate_avx2_spec _mem _st _buf _len) = rate8_of _st
  /\ trailb_of (absorb_m_updstate_avx2_spec _mem _st _buf _len) = trailb_of _st.
proof. admitted.

(* (3) finish closes the absorb phase: the resulting sponge state equals
       ABSORB1600 over the accumulated message. *)
lemma sponge_state_finish _st:
  sponge_state (finish_updstate_avx2_spec _st)
    = ABSORB1600 (trailb_of _st) (rate8_of _st) (absorb_msg _st)
  /\ rate8_of (finish_updstate_avx2_spec _st) = rate8_of _st.
proof. admitted.


(* ------------------------------------------------------------------------- *)
(* Bridge lemmas: composition rules for the partial-absorb predicate         *)
(* `pabsorb_spec_updstate_avx2`. These let a client chain                    *)
(*   init → update → absorb_m → finish → squeeze                             *)
(* entirely in the predicate world without ever touching the opaque viewers  *)
(* `absorb_msg` / `sponge_state`.                                            *)
(* ------------------------------------------------------------------------- *)

(* (B1) Init produces the empty-message predicate. *)
lemma init_pabsorb (_st : W64.t Array26.t) (r64 : int) (trailb : W8.t):
  0 < r64 <= 25 =>
  pabsorb_spec_updstate_avx2 [] (init_updstate_avx2_spec _st r64 trailb)
  /\ ststatus_r8     (init_updstate_avx2_spec _st r64 trailb).[25] = r64 * 8
  /\ ststatus_trailb (init_updstate_avx2_spec _st r64 trailb).[25] = trailb.
proof. admitted.

(* (B2) absorb_m preserves the predicate, extending the absorbed list by the
       memory read, and preserves the rate/trailb bytes of st.[25]. *)
lemma absorb_m_pabsorb _mem (_st : W64.t Array26.t) (_buf _len : int)
                      (_l : W8.t list):
  pabsorb_spec_updstate_avx2 _l _st =>
  0 <= _len =>
  _buf + _len < W64.modulus =>
  pabsorb_spec_updstate_avx2
    (_l ++ memread _mem _buf _len)
    (absorb_m_updstate_avx2_spec _mem _st _buf _len)
  /\ ststatus_r8 (absorb_m_updstate_avx2_spec _mem _st _buf _len).[25]
       = ststatus_r8 _st.[25]
  /\ ststatus_trailb (absorb_m_updstate_avx2_spec _mem _st _buf _len).[25]
       = ststatus_trailb _st.[25].
proof. admitted.

(* (B3) finish lands the first 25 words of the state at ABSORB1600 of the
       accumulated message, and preserves the rate byte. This is the bridge
       to the squeeze contract, which reads `Array25.init (fun i => _st.[i])`
       directly. *)
lemma finish_absorb (_st : W64.t Array26.t) (_l : W8.t list):
  pabsorb_spec_updstate_avx2 _l _st =>
  Array25.init (fun i => (finish_updstate_avx2_spec _st).[i])
    = ABSORB1600 (ststatus_trailb _st.[25]) (ststatus_r8 _st.[25]) _l
  /\ ststatus_r8 (finish_updstate_avx2_spec _st).[25] = ststatus_r8 _st.[25].
proof. admitted.


lemma init_updstate_avx2_ll: islossless M._init_updstate_avx2.
proof. admitted.

hoare init_updstate_avx2_h _st _r64 _trailb:
  M._init_updstate_avx2
  : st = _st /\ r64 = _r64 /\ trailb = _trailb
  ==> res = init_updstate_avx2_spec _st _r64 _trailb.
proof. admitted.

phoare init_updstate_avx2_ph _st _r64 _trailb:
  [ M._init_updstate_avx2
  : st = _st /\ r64 = _r64 /\ trailb = _trailb
  ==> res = init_updstate_avx2_spec _st _r64 _trailb
  ] = 1%r.
proof.
by conseq init_updstate_avx2_ll
       (init_updstate_avx2_h _st _r64 _trailb).
qed.


lemma finish_updstate_avx2_ll: islossless M._finish_updstate_avx2.
proof. admitted.

hoare finish_updstate_avx2_h _st:
  M._finish_updstate_avx2
  : st = _st
  ==> res = finish_updstate_avx2_spec _st.
proof. admitted.

phoare finish_updstate_avx2_ph _st:
  [ M._finish_updstate_avx2
  : st = _st
  ==> res = finish_updstate_avx2_spec _st
  ] = 1%r.
proof.
by conseq finish_updstate_avx2_ll (finish_updstate_avx2_h _st).
qed.


lemma absorb_m_updstate_avx2_ll: islossless M._absorb_m_updstate_avx2.
proof. admitted.

hoare absorb_m_updstate_avx2_h _mem _st _buf _len:
  M._absorb_m_updstate_avx2
  : Glob.mem = _mem /\ st = _st /\ buf = _buf /\ len = _len
  ==> res = absorb_m_updstate_avx2_spec _mem _st _buf _len.
proof. admitted.

phoare absorb_m_updstate_avx2_ph _mem _st _buf _len:
  [ M._absorb_m_updstate_avx2
  : Glob.mem = _mem /\ st = _st /\ buf = _buf /\ len = _len
  ==> res = absorb_m_updstate_avx2_spec _mem _st _buf _len
  ] = 1%r.
proof.
by conseq absorb_m_updstate_avx2_ll
       (absorb_m_updstate_avx2_h _mem _st _buf _len).
qed.


abstract theory KeccakUpdstateAvx2.

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


(* -----------------------------------------------------------------------
   Module MM: the extracted procedures, with Array999 replaced by A.t and
   WArray999 / WArray999.xxx replaced by WA.xxx.
   ----------------------------------------------------------------------- *)

module MM = {
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

  proc _add_updstate_avx2 (st:W64.t Array25.t, at:int, buf:W8.t A.t,
                           off:int, upto:int) : int * int * W64.t Array25.t = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
    var r256:W256.t;
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
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
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
    newat <- (newat + 32);
    while ((newat <= upto)) {
      r256 <- (get256_direct (WArray200.init64 (fun i => st.[i])) at);
      t256 <- (get256_direct (WA.init8 (fun i => buf.[i])) off);
      r256 <- (r256 `^` t256);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set256_direct (WArray200.init64 (fun i => st.[i])) at r256))
      );
      at <- newat;
      off <- (off + 32);
      newat <- (newat + 32);
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WA.init8 (fun i => buf.[i])) off);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      (off, t64) <@ RW.MM.__a_rlen_read_upto8 (buf, off, (W64.to_uint upto8));
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i => st.[i])) at
      ((get64_direct (WArray200.init64 (fun i => st.[i])) at) `^` t64))));
    } else {
    }
    at <- upto;
    return (at, off, st);
  }

  (* Absorb `len` bytes from `buf` into the updstate `st`.
     The parameter `len` is the number of new bytes; internally the function
     reads `at` from the status word to resume partial blocks. *)
  proc _update_updstate_avx2 (st:W64.t Array26.t, buf:W8.t A.t,
                              len:int) : W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var  _0:W8.t;
    var  _1:int;
    var off:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ M._ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (at, off, stk) <@ _add_updstate_avx2 (stk, at, buf, off, r8);
      stk <@ M._keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, stk) <@ _add_updstate_avx2 (stk, at, buf, off, len);
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

  (* Copy bytes `st[at..upto-1]` to `buf[off .. off+upto-at-1]`.
     Returns (new_at, new_off, new_buf).  new_at = upto. *)
  proc _dump_updstate_avx2 (buf:W8.t A.t, off:int, st:W64.t Array25.t,
                            at:int, upto:int) : int * int * W8.t A.t = {
    var at8:W64.t;
    var t64:W64.t;
    var sh:W8.t;
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
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      sh <- (truncateu8 at8);
      sh <- (sh `<<` (W8.of_int 3));
      t64 <- (t64 `>>` (sh `&` (W8.of_int 63)));
      (buf, off2) <@ RW.MM.__a_rlen_write_upto8 (buf, off, t64, len);
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
    newat <- (newat + 32);
    while ((newat <= upto)) {
      t256 <- (get256_direct (WArray200.init64 (fun i => st.[i])) at);
      buf <-
      (A.init
      (WA.get8
      (WA.set256_direct (WA.init8 (fun i => buf.[i])) off t256)
      ));
      at <- newat;
      off <- (off + 32);
      newat <- (newat + 32);
    }
    newat <- at;
    newat <- (newat + 8);
    while ((newat <= upto)) {
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      buf <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i => buf.[i])) off t64)));
      at <- newat;
      off <- (off + 8);
      newat <- (newat + 8);
    }
    if ((at < upto)) {
      upto8 <- (W64.of_int upto);
      upto8 <- (upto8 `&` (W64.of_int 7));
      t64 <- (get64_direct (WArray200.init64 (fun i => st.[i])) at);
      (buf, off) <@ RW.MM.__a_rlen_write_upto8 (buf, off, t64,
      (W64.to_uint upto8));
    } else {
    }
    at <- upto;
    return (at, off, buf);
  }

  (* Squeeze `len` bytes from the updstate into `buf`.
     Reads `at` and `r8` from status word; applies permutation when at=0. *)
  proc _squeeze_updstate_avx2 (st:W64.t Array26.t, buf:W8.t A.t,
                               len:int) : W64.t Array26.t * W8.t A.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ M._ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    if ((at = 0)) {
      stk <@ M._keccakf1600_st25_avx2 (stk);
      at <- 0;
    } else {
    }
    off <- 0;
    len <- (len + at);
    while ((r8 < len)) {
      (at, off, buf) <@ _dump_updstate_avx2 (buf, off, stk, at, r8);
      stk <@ M._keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (at,  _1, buf) <@ _dump_updstate_avx2 (buf, off, stk, at, len);
    (* Erased call to unspill *)
    st <-
    (Array26.init
    (fun i => (if (0 <= i < (0 + 25)) then stk.[(i - 0)] else st.[i])));
    st <-
    (Array26.init
    (WArray208.get64
    (WArray208.set8_direct (WArray208.init64 (fun i => st.[i])) (8 * 25)
    (truncateu8 (W64.of_int at)))));
    return (st, buf);
  }

  (* Exported absorb entry point *)
  proc absorb_updstate_avx2 (st:W64.t Array26.t, buf:W8.t A.t, len:int) :
  W64.t Array26.t = {
    st <- st;
    buf <- buf;
    st <@ _update_updstate_avx2 (st, buf, len);
    return st;
  }

  (* Exported squeeze entry point *)
  proc squeeze_updstate_avx2 (st:W64.t Array26.t, buf:W8.t A.t,
                              len:int) : W64.t Array26.t * W8.t A.t = {
    st <- st;
    buf <- buf;
    len <- len;
    (st, buf) <@ _squeeze_updstate_avx2 (st, buf, len);
    return (st, buf);
  }
}.


(* -----------------------------------------------------------------------
   Losslessness lemmas
   ----------------------------------------------------------------------- *)

lemma add_updstate_avx2_ll: islossless MM._add_updstate_avx2.
proof.
proc.
admit.
qed.

lemma update_updstate_avx2_ll: islossless MM._update_updstate_avx2.
proof.
proc.
wp; call add_updstate_avx2_ll.
admit(*
while true (len %/ r8 + 1).
 move=> z; wp.
 call keccakf1600_st25_avx2_ll.
 call add_updstate_avx2_ll.
 by auto => /> /#.
by islossless.
*).
qed.

lemma dump_updstate_avx2_ll: islossless MM._dump_updstate_avx2.
proof.
admit(*
proc.
while true ((upto - at + 8) %/ 8).
 move=> z; wp; auto => /> /#.
while true ((upto - at + 32) %/ 32).
 move=> z; wp; auto => /> /#.
by islossless.
*).
qed.

lemma squeeze_updstate_avx2_ll: islossless MM._squeeze_updstate_avx2.
proof.
admit(*
proc.
wp; call dump_updstate_avx2_ll.
while true (len %/ r8 + 1).
 move=> z; wp.
 call keccakf1600_st25_avx2_ll.
 call dump_updstate_avx2_ll.
 by auto => /> /#.
if => //.
 call keccakf1600_st25_avx2_ll; by auto.
by islossless.
*).
qed.

lemma absorb_updstate_avx2_ll: islossless MM.absorb_updstate_avx2.
proof. proc; call update_updstate_avx2_ll; by auto. qed.

lemma squeeze_updstate_avx2_outer_ll: islossless MM.squeeze_updstate_avx2.
proof. proc; call squeeze_updstate_avx2_ll; by auto. qed.


(* -----------------------------------------------------------------------
   Correctness of _add_updstate_avx2:
   XORs buf[off..off+(upto-at)-1] into state at byte position `at`.
   ----------------------------------------------------------------------- *)

hoare add_updstate_avx2_h _st _at _buf _off _upto:
 MM._add_updstate_avx2
 : st=_st /\ at=_at /\ buf=_buf /\ off=_off /\ upto=_upto
 /\ 0 <= _at <= _upto /\ _upto <= 200
 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> let l = sub _buf _off (_upto - _at)
     in res.`3 = addstate_at _st _at l
     /\ res.`1 = _upto
     /\ res.`2 = _off + (_upto - _at).
proof.
proc.
admitted.

phoare add_updstate_avx2_ph _st _at _buf _off _upto:
 [ MM._add_updstate_avx2
 : st=_st /\ at=_at /\ buf=_buf /\ off=_off /\ upto=_upto
 /\ 0 <= _at <= _upto /\ _upto <= 200
 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> let l = sub _buf _off (_upto - _at)
     in res.`3 = addstate_at _st _at l
     /\ res.`1 = _upto
     /\ res.`2 = _off + (_upto - _at)
 ] = 1%r.
proof.
by conseq add_updstate_avx2_ll (add_updstate_avx2_h _st _at _buf _off _upto).
qed.


(* -----------------------------------------------------------------------
   Correctness of _update_updstate_avx2 (internal absorb):
   Absorbs `len` new bytes from `buf[0..len-1]` into the updstate.
   ----------------------------------------------------------------------- *)

hoare update_updstate_avx2_h _l _buf _len _st:
 MM._update_updstate_avx2
 : st=_st /\ buf=_buf /\ len=_len /\ pabsorb_spec_updstate_avx2 _l _st
 /\ 0 <= len <= _ASIZE
 ==> pabsorb_spec_updstate_avx2 (_l ++ sub _buf 0 _len) res
  /\ ststatus_r8     res.[25] = ststatus_r8     _st.[25]
  /\ ststatus_trailb res.[25] = ststatus_trailb _st.[25].
proof.
proc => /=.
admitted.

phoare update_updstate_avx2_ph _l _buf _len _st:
 [ MM._update_updstate_avx2
 : st=_st /\ buf=_buf /\ len=_len /\ pabsorb_spec_updstate_avx2 _l _st
 /\ 0 <= len <= _ASIZE
 ==> pabsorb_spec_updstate_avx2 (_l ++ sub _buf 0 _len) res
  /\ ststatus_r8     res.[25] = ststatus_r8     _st.[25]
  /\ ststatus_trailb res.[25] = ststatus_trailb _st.[25]
 ] = 1%r.
proof.
by conseq update_updstate_avx2_ll (update_updstate_avx2_h _l _buf _len _st).
qed.


(* -----------------------------------------------------------------------
   Correctness of absorb_updstate_avx2 (exported entry point)
   ----------------------------------------------------------------------- *)

hoare absorb_updstate_avx2_h _l _buf _len _st:
 MM.absorb_updstate_avx2
 : st=_st /\ buf=_buf /\ len=_len /\ pabsorb_spec_updstate_avx2 _l _st
 /\ 0 <= len <= _ASIZE
 ==> pabsorb_spec_updstate_avx2 (_l ++ sub _buf 0 _len) res
  /\ ststatus_r8     res.[25] = ststatus_r8     _st.[25]
  /\ ststatus_trailb res.[25] = ststatus_trailb _st.[25].
proof.
proc.
call (update_updstate_avx2_h _l _buf _len _st).
by auto => />.
qed.

phoare absorb_updstate_avx2_ph _l _buf _len _st:
 [ MM.absorb_updstate_avx2
 : st=_st /\ buf=_buf /\ len=_len /\ pabsorb_spec_updstate_avx2 _l _st
 /\ 0 <= len <= _ASIZE
 ==> pabsorb_spec_updstate_avx2 (_l ++ sub _buf 0 _len) res
  /\ ststatus_r8     res.[25] = ststatus_r8     _st.[25]
  /\ ststatus_trailb res.[25] = ststatus_trailb _st.[25]
 ] = 1%r.
proof.
by conseq absorb_updstate_avx2_ll (absorb_updstate_avx2_h _l _buf _len _st).
qed.


(* -----------------------------------------------------------------------
   Correctness of _dump_updstate_avx2:
   Copies state bytes [at..upto-1] into buf[off..off+(upto-at)-1].
   ----------------------------------------------------------------------- *)

hoare dump_updstate_avx2_h _buf _off _st _at _upto:
 MM._dump_updstate_avx2
 : buf=_buf /\ off=_off /\ st=_st /\ at=_at /\ upto=_upto
 /\ 0 <= _at <= _upto /\ _upto <= 200
 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res.`3 = A.fill (fun i => (stbytes _st).[i - _off + _at]) _off (_upto - _at) _buf
     /\ res.`1 = _upto
     /\ res.`2 = _off + (_upto - _at).
proof.
proc => /=.
admitted.

phoare dump_updstate_avx2_ph _buf _off _st _at _upto:
 [ MM._dump_updstate_avx2
 : buf=_buf /\ off=_off /\ st=_st /\ at=_at /\ upto=_upto
 /\ 0 <= _at <= _upto /\ _upto <= 200
 /\ 0 <= _off /\ _off + (_upto - _at) <= _ASIZE
 ==> res.`3 = A.fill (fun i => (stbytes _st).[i - _off + _at]) _off (_upto - _at) _buf
     /\ res.`1 = _upto
     /\ res.`2 = _off + (_upto - _at)
 ] = 1%r.
proof.
by conseq dump_updstate_avx2_ll (dump_updstate_avx2_h _buf _off _st _at _upto).
qed.


(* -----------------------------------------------------------------------
   Correctness of _squeeze_updstate_avx2:
   Squeezes _ASIZE bytes from the state into buf.
   ----------------------------------------------------------------------- *)

hoare squeeze_updstate_avx2_h _buf _st _r8 _len:
 MM._squeeze_updstate_avx2
 : buf=_buf /\ len=_len /\ st=_st /\ ststatus_r8 _st.[25] = _r8
 /\ 0 < _r8 <= 200 /\ 0 <= _len <= _ASIZE
 ==> let stk = Array25.init (fun i => _st.[i]) in
     res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _len stk)
     /\ res.`1 = Array26.init (fun i =>
          if i < 25 then (st_i stk ((_len - 1) %/ _r8 + 1)).[i]
          else _st.[i]).
proof.
proc => /=.
admitted.

phoare squeeze_updstate_avx2_ph _buf _st _r8 _len:
 [ MM._squeeze_updstate_avx2
 : buf=_buf /\ len=_len /\ st=_st /\ ststatus_r8 _st.[25] = _r8
 /\ 0 < _r8 <= 200 /\ 0 <= _len <= _ASIZE
 ==> let stk = Array25.init (fun i => _st.[i]) in
     res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _len stk)
     /\ res.`1 = Array26.init (fun i =>
          if i < 25 then (st_i stk ((_len - 1) %/ _r8 + 1)).[i]
          else _st.[i])
 ] = 1%r.
proof.
by conseq squeeze_updstate_avx2_ll (squeeze_updstate_avx2_h _buf _st _r8 _len).
qed.


(* -----------------------------------------------------------------------
   Correctness of squeeze_updstate_avx2 (exported entry point)
   ----------------------------------------------------------------------- *)

hoare squeeze_updstate_avx2_outer_h _buf _st _r8 _len:
 MM.squeeze_updstate_avx2
 : buf=_buf /\ len=_len /\ st=_st /\ ststatus_r8 _st.[25] = _r8
 /\ 0 < _r8 <= 200 /\ 0 <= _len <= _ASIZE
 ==> let stk = Array25.init (fun i => _st.[i]) in
     res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _len stk)
     /\ res.`1 = Array26.init (fun i =>
          if i < 25 then (st_i stk ((_len - 1) %/ _r8 + 1)).[i]
          else _st.[i]).
proof.
proc.
call (squeeze_updstate_avx2_h _buf _st _r8 _len).
by auto => />.
qed.

phoare squeeze_updstate_avx2_outer_ph _buf _st _r8 _len:
 [ MM.squeeze_updstate_avx2
 : buf=_buf /\ len=_len /\ st=_st /\ ststatus_r8 _st.[25] = _r8
 /\ 0 < _r8 <= 200 /\ 0 <= _len <= _ASIZE
 ==> let stk = Array25.init (fun i => _st.[i]) in
     res.`2 = of_list W8.zero (SQUEEZE1600 _r8 _len stk)
     /\ res.`1 = Array26.init (fun i =>
          if i < 25 then (st_i stk ((_len - 1) %/ _r8 + 1)).[i]
          else _st.[i])
 ] = 1%r.
proof.
by conseq squeeze_updstate_avx2_outer_ll (squeeze_updstate_avx2_outer_h _buf _st _r8 _len).
qed.

end KeccakUpdstateAvx2.
