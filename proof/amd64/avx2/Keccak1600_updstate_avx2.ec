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
from JazzEC require import Array7 Array25 Array26.

from CryptoSpecs require import JWordList.

require import Keccak1600_avx2 Keccakf1600_avx2.
require import Keccak1600_subreadwrite.

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
    ( _0, r8, at) <@ _ststatus_data (ststatus);
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
  proc _update_updstate_avx2 (st:W64.t Array26.t, buf:W8.t A.t,
                              len:int) : W64.t Array26.t = {
    var ststatus:W64.t;
    var stk:W64.t Array25.t;
    var r8:int;
    var at:int;
    var off:int;
    var  _0:W8.t;
    var  _1:int;
    stk <- witness;
    ststatus <- st.[25];
    ( _0, r8, at) <@ _ststatus_data (ststatus);
    stk <- (Array25.init (fun i => st.[(0 + i)]));
    (* Erased call to spill *)
    off <- 0;
    len <- (len + at);
    while ((r8 <= len)) {
      (at, off, stk) <@ _add_updstate_avx2 (stk, at, buf, off, r8);
      stk <@ M._keccakf1600_st25_avx2 (stk);
      len <- (len - r8);
      at <- 0;
    }
    len <- len;
    (* Erased call to unspill *)
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
}.

(* ------------------------------------------------------------------------ *)
(* Spec-side operators (placeholder declarations). Each updstate proc has a  *)
(* pure-functional companion that captures its intended result; the hoare    *)
(* lemma below relates the proc to the operator. Bodies are deferred (`op`   *)
(* without definition) until the streaming-absorb / streaming-squeeze spec   *)
(* layer is filled in.                                                        *)
(* ------------------------------------------------------------------------ *)

op ststatus_data_spec : W64.t -> W8.t * int * int.

op add_updstate_avx2_spec :
  W64.t Array25.t -> int -> W8.t A.t -> int -> int
  -> int * int * W64.t Array25.t.

op dump_updstate_avx2_spec :
  W8.t A.t -> int -> W64.t Array25.t -> int -> int
  -> int * int * W8.t A.t.

op update_updstate_avx2_spec :
  W64.t Array26.t -> W8.t A.t -> int
  -> W64.t Array26.t.

op squeeze_updstate_avx2_spec :
  W64.t Array26.t -> W8.t A.t -> int
  -> W64.t Array26.t * W8.t A.t.

(* ------------------------------------------------------------------------ *)
(* Lossless / hoare / phoare triples for each updstate proc.                 *)
(* ------------------------------------------------------------------------ *)

lemma ststatus_data_ll: islossless MM._ststatus_data.
proof. admitted.

hoare ststatus_data_h _s:
  MM._ststatus_data
  : ststatus = _s
  ==> res = ststatus_data_spec _s.
proof. admitted.

phoare ststatus_data_ph _s:
  [ MM._ststatus_data
  : ststatus = _s
  ==> res = ststatus_data_spec _s
  ] = 1%r.
proof. by conseq ststatus_data_ll (ststatus_data_h _s). qed.


lemma add_updstate_avx2_ll: islossless MM._add_updstate_avx2.
proof. admitted.

hoare add_updstate_avx2_h _st _at _buf _off _upto:
  MM._add_updstate_avx2
  : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
  ==> res = add_updstate_avx2_spec _st _at _buf _off _upto.
proof. admitted.

phoare add_updstate_avx2_ph _st _at _buf _off _upto:
  [ MM._add_updstate_avx2
  : st = _st /\ at = _at /\ buf = _buf /\ off = _off /\ upto = _upto
  ==> res = add_updstate_avx2_spec _st _at _buf _off _upto
  ] = 1%r.
proof.
by conseq add_updstate_avx2_ll
       (add_updstate_avx2_h _st _at _buf _off _upto).
qed.


lemma dump_updstate_avx2_ll: islossless MM._dump_updstate_avx2.
proof. admitted.

hoare dump_updstate_avx2_h _buf _off _st _at _upto:
  MM._dump_updstate_avx2
  : buf = _buf /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
  ==> res = dump_updstate_avx2_spec _buf _off _st _at _upto.
proof. admitted.

phoare dump_updstate_avx2_ph _buf _off _st _at _upto:
  [ MM._dump_updstate_avx2
  : buf = _buf /\ off = _off /\ st = _st /\ at = _at /\ upto = _upto
  ==> res = dump_updstate_avx2_spec _buf _off _st _at _upto
  ] = 1%r.
proof.
by conseq dump_updstate_avx2_ll
       (dump_updstate_avx2_h _buf _off _st _at _upto).
qed.


lemma update_updstate_avx2_ll: islossless MM._update_updstate_avx2.
proof. admitted.

hoare update_updstate_avx2_h _st _buf _len:
  MM._update_updstate_avx2
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = update_updstate_avx2_spec _st _buf _len.
proof. admitted.

phoare update_updstate_avx2_ph _st _buf _len:
  [ MM._update_updstate_avx2
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = update_updstate_avx2_spec _st _buf _len
  ] = 1%r.
proof.
by conseq update_updstate_avx2_ll
       (update_updstate_avx2_h _st _buf _len).
qed.


lemma squeeze_updstate_avx2_ll: islossless MM._squeeze_updstate_avx2.
proof. admitted.

hoare squeeze_updstate_avx2_h _st _buf _len:
  MM._squeeze_updstate_avx2
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = squeeze_updstate_avx2_spec _st _buf _len.
proof. admitted.

phoare squeeze_updstate_avx2_ph _st _buf _len:
  [ MM._squeeze_updstate_avx2
  : st = _st /\ buf = _buf /\ len = _len
  ==> res = squeeze_updstate_avx2_spec _st _buf _len
  ] = 1%r.
proof.
by conseq squeeze_updstate_avx2_ll
       (squeeze_updstate_avx2_h _st _buf _len).
qed.

end KeccakUpdstateAvx2.
