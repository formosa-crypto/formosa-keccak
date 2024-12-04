(******************************************************************************
   Keccak_f1600_Spec.ec:

   Specification of the Keccak-f1600 permutation.

   Normative reference: FIPS PUB 202
   https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf
******************************************************************************)
require import AllCore List Int IntDiv.
require BitEncoding.
import BitEncoding.BitChunking.


require export FIPS202_Keccakf1600.


(** Initial state *)
op st0 : state = Array25.create W64.zero.

(** State addition (xor) *)
op addstate = Array25.map2 W64.(`^`) .

(** Section 4 - SPONGE CONSTRUCTION 

from the spec:
"""
The construction employs the following three components:
- An underlying function on fixed-length strings, denoted by f,
- A parameter called the rate, denoted by r, and
- A padding rule, denoted by pad.
...

The function f maps strings of a single, fixed length, denoted by
b, to strings of the same length. As in Sec. 3, b is called the width
of f. The SHA-3 functions, specified in Sec. 6 are instances of the
sponge construction in which the underlying function f is invertible,
i.e., a permutation, although the sponge construction does not require
f to be invertible.

The rate r is a positive integer that is strictly less than the width
b. The capacity, denoted by c, is the positive integer br. Thus, r +
c = b.

The padding rule, pad, is a function that produces padding, i.e., a
string with an appropriate length to append to another string. In
general, given a positive integer x and a non-negative integer m, the
output pad(x, m) is a string with the property that m + len(pad(x, m))
is a positive multiple of x. Within the sponge construction, x = r and
m = len(N), so that the padded input string can be partitioned into a
sequence of r-bit strings. Algorithm 9 in Sec. 5.1 specifies the
padding rule for the KECCAK functions and, hence, the SHA-3 functions.

*)

module type SpongeParams = {
 proc f(s: state): state
 proc pad(r x: int): bool list
}.



module Sponge1600 (P: SpongeParams) = {
  (** Algorithm 8 *)
  proc sponge(r: int, m: bool list, d: int): bool list = {
    var p, pl, n, s, i, z;
    p <@ P.pad(r, size m);
    p <- m ++ p;
    pl <- chunk r p;
    n <- (size p) %/ r;
    s <- st0;
    i <- 0;
    while (i < n) { (* absorb *)
      s <- addstate s (bits2state (nth [] pl i));
      s <@ P.f(s);
      i <- i + 1;
    }
    (* squeeze *)
    z <- take r (state2bits s);
    while (size z < d) {
      s <@ P.f(s);
      z <- z ++ take r (state2bits s);
    }
    return take d z;
  }
}.

(** Section 5 - Keccak *)


(** Section 5.1 -- Specification of [pad10*1]
    Algorithm 9 *)
op pad10star1 (x: int) (m: int): bool list =
 true :: rcons (nseq ((-m-2)%%x) false) true.


module Keccakf1600_Params = {
 proc f = Keccakf1600.keccak_f1600 (* Keccak Permutation *)
 proc pad(r x: int): bool list = { (* multi-rate padding *)
  return pad10star1 r x;
 }
}.

(** Imperative specification for [Keccak-f1600]. *)
module Keccak1600 = {
  module Spng = Sponge1600(Keccakf1600_Params)
  (** Section 5.2 - Specification of KECCAK[c] *)
  proc keccak1600(c: int, m: bool list, outlen: int): bool list = {
    var z;
    z <@ Spng.sponge(keccak_b - c, m, outlen);
    return z;
  }
  (** Section 6.1 - SHA-3 Hash Functions *)
  proc sha3_224(m: bool list): bool list = {
    var z;
    z <@ keccak1600(448, m++[false; true], 224);
    return z;
  }
  proc sha3_256(m: bool list): bool list = {
    var z;
    z <@ keccak1600(512, m++[false; true], 256);
    return z;
  }
  proc sha3_384(m: bool list): bool list = {
    var z;
    z <@ keccak1600(768, m++[false; true], 384);
    return z;
  }
  proc sha3_512(m: bool list): bool list = {
    var z;
    z <@ keccak1600(1024, m++[false; true], 512);
    return z;
  }
  (** Section 6.2 - SHA-3 Extendable-Output Functions *)
  proc shake128(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(256, m++[true; true; true; true], d);
    return z;
  }
  proc shake256(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(512, m++[true; true; true; true], d);
    return z;
  }
  (** Section 6.3 - AlternateDefinitionsof SHA-3 Extendable-Output Functions *)
  proc rawSHAKE128(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(256, m++[true; true], d);
    return z;
  }
  proc rawSHAKE256(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(512, m++[true; true], d);
    return z;
  }
}.


