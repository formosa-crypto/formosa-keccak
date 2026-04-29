require import AllCore List.
from Jasmin require import JModel_x86.
from JazzEC require import Ml_dsa_65_avx2.
from Keccak require import Keccak1600_avx2.
require import Array26 Array64 Array66.
from CryptoSpecs require import JWordList.

(*
 * Abstract predicates capturing streaming SHAKE256 absorb state.
 *
 * updstate_absorbing st absorbed:
 *   `st` is a valid in-progress absorb state that has consumed `absorbed`
 *   bytes so far (SHAKE256 padding not yet applied).
 *
 * updstate_squeezable st m:
 *   `st` is a finalised (padded, permuted) state ready to produce
 *   SHAKE256(m, * ) output bytes.
 *
 * Both predicates are abstract — their proofs will eventually connect
 * the W64.t Array26.t representation to the Keccak1600 spec.
 *)
op updstate_absorbing (st : W64.t Array26.t) (absorbed : W8.t list) : bool.
op updstate_squeezable (st : W64.t Array26.t) (m : W8.t list) : bool.

(* ------------------------------------------------------------------ *)
(* _init_updstate_avx2                                                 *)
(*   Initialises a fresh streaming state for SHAKE256                  *)
(*   (rate = 17 × 8 = 136 bytes, trailing byte = 0x1f).               *)
(* ------------------------------------------------------------------ *)
lemma init_updstate_avx2_h :
  hoare [ M._init_updstate_avx2 :
    r64 = 17 /\ trailb = W8.of_int 31
    ==>
    updstate_absorbing res []
  ].
proof. admitted. 

lemma init_updstate_avx2_ll : islossless M._init_updstate_avx2.
proof. admitted. 

(* ------------------------------------------------------------------ *)
(* a66___update_updstate_avx2                                          *)
(*   Absorbs all 66 bytes of `buf` into the state.                     *)
(* ------------------------------------------------------------------ *)
lemma a66_update_updstate_avx2_h (_st : W64.t Array26.t)
                                  (_buf : W8.t Array66.t)
                                  (_so_far : W8.t list) :
  hoare [ M.a66___update_updstate_avx2 :
    st = _st /\ buf = _buf /\ len = 66 /\
    updstate_absorbing st _so_far
    ==>
    updstate_absorbing res (_so_far ++ to_list _buf)
  ].
proof. admitted. 

lemma a66_update_updstate_avx2_ll : islossless M.a66___update_updstate_avx2.
proof. admitted. 

(* ------------------------------------------------------------------ *)
(* _absorb_m_updstate_avx2                                             *)
(*   Absorbs `len` bytes from global memory at pointer `buf`.          *)
(*   The memory content at call time is fixed by the `_mem` parameter. *)
(* ------------------------------------------------------------------ *)
lemma absorb_m_updstate_avx2_h (_mem : global_mem_t)
                                (_st : W64.t Array26.t)
                                (_so_far : W8.t list)
                                (_ptr _sz : int) :
  hoare [ M._absorb_m_updstate_avx2 :
    st = _st /\ buf = _ptr /\ len = _sz /\
    updstate_absorbing st _so_far /\
    Glob.mem = _mem /\
    0 <= _sz /\ _ptr + _sz < W64.modulus
    ==>
    updstate_absorbing res (_so_far ++ memread _mem _ptr _sz)
  ].
proof. admitted. 

lemma absorb_m_updstate_avx2_ll : islossless M._absorb_m_updstate_avx2.
proof. admitted. 

(* ------------------------------------------------------------------ *)
(* _finish_updstate_avx2                                               *)
(*   Applies SHAKE256 padding and the final Keccak permutation.        *)
(*   The resulting state can only be used for squeezing.               *)
(* ------------------------------------------------------------------ *)
lemma finish_updstate_avx2_h (_st : W64.t Array26.t) (_m : W8.t list) :
  hoare [ M._finish_updstate_avx2 :
    st = _st /\
    updstate_absorbing st _m
    ==>
    updstate_squeezable res _m
  ].
proof. admitted. 

lemma finish_updstate_avx2_ll : islossless M._finish_updstate_avx2.
proof. admitted. 

(* ------------------------------------------------------------------ *)
(* a64___squeeze_updstate_avx2                                         *)
(*   Squeezes 64 bytes from a finalised state.                         *)
(*   The output equals the first 64 bytes of SHAKE256(m).              *)
(* ------------------------------------------------------------------ *)
lemma a64_squeeze_updstate_avx2_h (_st : W64.t Array26.t)
                                   (_arr : W8.t Array64.t)
                                   (_m : W8.t list) :
  hoare [ M.a64___squeeze_updstate_avx2 :
    st = _st /\ buf = _arr /\ len = 64 /\
    updstate_squeezable st _m
    ==>
    res.`2 = Array64.of_list witness (SHAKE256 _m 64)
  ].
proof. admitted. 

lemma a64_squeeze_updstate_avx2_ll : islossless M.a64___squeeze_updstate_avx2.
proof. admitted. 
