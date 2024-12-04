(******************************************************************************
   Keccak_f1600_Spec.ec:

   Specification of the Keccak-f1600 permutation.

   Normative reference: FIPS PUB 202
   https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf
******************************************************************************)
require import AllCore List Int IntDiv.

from Jasmin require export JWord JUtils.

require export JWordList.

(*from JExtr*) require import Array5 Array24.
(*from JExtr*) require export Array25.


(** Section 3.1 - State

  We specialise the width of the permutation to [b = 1600], leading to the related
  quantities [w = b / 25 = 64] and [l = log2 (b/25) = 6] (c.f. Table 1).

  The state [A] is organized as a matrix of 5-by-5-by 64 bits. For convenience, and
  since Jasmin does not support directly matrices, we adopt the view of an array of
  25 64bit words.

    A[x,y,z] = st.[ idx(x,y) ].[z]  , for 0 <= x,y < 5, and 0 <= z < 64

      where idx(x,y) = x * (y*5)

*)

(** Parameters (Table 1) *)
op keccak_b = 1600.
op keccak_w = 64.
op keccak_l = 6.

(** State type *)
type state = W64.t Array25.t.

(** Index access *)
op idx (xy: int*int): int = (xy.`1 %% 5) + (5 * (xy.`2 %% 5)).


(** Section 3.1.2 - Converting Strings to Arrays *) 
op state2bits (st: state): bool list =
 w64L_to_bits (to_list st).


(** Section 3.1.3 - Converting State Arrays to Strings
    obs: note that it zero-pads or truncates the bitstring *)
op bits2state (bs: bool list): state =
 Array25.of_list W64.zero (w64L_from_bits bs).


(** Section 3.2 - Step Mappings *)


(** Imperative specification for [Keccak-f1600]. *)
module Keccakf1600 = {
  (* Section 3.2.1 -- Algorithm 1 *)
  proc keccak_theta (a: state) : state = {
    var x, y: int;   
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;

    c <- witness;
    d <- witness;
    (* step 1. *)
    x <- 0;
    while (x < 5) {
      c.[x] <- W64.of_int 0;
      y <- 0;
      while (y < 5) {
        c.[x] <- c.[x] `^` a.[idx(x,y)];
        y <- y + 1;
      }
      x <- x + 1;
    }
    (* step 2. *)
    x <- 0;
    while (x < 5) {
      d.[x] <- c.[((x + 1) %% 5)];
      d.[x] <- d.[x] `|<<<|` 1;
      d.[x] <- (d.[x] `^` c.[((x + 4) %% 5)]);
      x <- x + 1;
    }
    (* step 3. *)
    x <- 0;
    while (x < 5) {
      y <- 0;
      while (y < 5) {
        a.[idx(x,y)] <- (a.[idx(x,y)] `^` d.[x]);
        y <- y + 1;
      }
      x <- x + 1;
    }
    return (a);
  }
  
  (* Section 3.2.2 - Algorithm 2 *)
  proc keccak_rho (a: state) : state = {
    var offset, x, y, t: int;
    (x,y) <- (1,0);
    t <- 0;
    while (t < 24) {
      offset <- (t+1)*(t+2) %/ 2 %% 64;
      a.[idx(x,y)] <- a.[idx(x,y)] `|<<<|` offset;
      (x,y) <- (y, (2*x+3*y)%%5);
      t <- t + 1;
    }
    return a;
  }

  (* Section 3.2.3 - Algorithm 3 *)
  proc keccak_pi (a: state) : state = {
    var b: state;
    var x, y:int;

    b <- a;
    x <- 0;
    while (x < 5) {
      y <- 0;
      while (y < 5) {
        a.[idx(x,y)] <- b.[idx((x+3*y)%%5,x)];
        y <- y + 1;
      }
      x <- x + 1;
    }
    return a;
  }

  (* Section 3.2.4 - Algorithm 4 *)
  proc keccak_chi (a: state) : state = {
    var x, y: int;
    var b: W64.t Array25.t;

    b <- witness;
    x <- 0;
    while (x < 5) {
      y <- 0;
      while (y < 5) {
        b.[idx(x,y)] <- a.[idx(x,y)]
                          `^` (invw a.[idx(x+1, y)]
                               `&` a.[idx(x+2, y)]);
        y <- y + 1;
      }
      x <- x + 1;
    }
    return b;
  }
  proc keccak_chiOLD (a: state) : state = {
    var x, y: int;
    var b: W64.t Array25.t;

    b <- witness;
    y <- 0;
    while (y < 5) {
      x <- 0;
      while (x < 5) {
        b.[idx(x,y)] <- a.[idx(x,y)]
                          `^` (invw a.[idx(x+1, y)]
                               `&` a.[idx(x+2, y)]);
        x <- x + 1;
      }
      y <- y + 1;
    }
    return b;
  }

  (* Section 3.2.5 - Algorithm 5 *)
  proc keccak_rc (t: int): bool = {
    var b, r8: bool;
    var r: W8.t;
    var i: int;
    b <- true;
    if (t %% 255 <> 0) {
      r <- W8.of_int 1;
      i <- 1;
      while (i <= t %% 255) {
        r8 <- r.[7];
        r <- r `<<<` 1;
        r.[0] <- r.[0] ^ r8;
        r.[4] <- r.[4] ^ r8;
        r.[5] <- r.[5] ^ r8;
        r.[6] <- r.[6] ^ r8;
        i <- i+1;
      }
      b <- r.[0];
    }
    return b;
  }
  (** Algorithm 6 (steps 2..3) *)
  proc keccak_RC (ir: int): W64.t = {
    var j: int;
    var rc: W64.t;
    var b: bool;
    rc <- W64.zero;
    j <- 0;
    while (j <= keccak_l) {
      b <@ keccak_rc(j + 7*ir);
      rc.[2^j-1] <- b;
      j <- j + 1;
    }
    return rc;
  }
    
  (** Algorithm 6 *)
  proc keccak_iota (a: state, ir: int) : state = {
    var rc: W64.t;
    rc <@ keccak_RC(ir);
    a.[0] <- a.[0] `^` rc;
    return a;
  }
  
  (** Section 3.3 - KECCAK-p[b,nr] *)
  proc keccak_Rnd (st: state, ir: int) : state = {
    st <@ keccak_theta  (st);
    st <@ keccak_rho    (st);
    st <@ keccak_pi     (st);
    st <@ keccak_chi    (st);
    st <@ keccak_iota   (st, ir);
    return (st);
  }
  
  (** Algorithm 7 *)
  proc keccak_p1600 (st: state, nr: int) : state = {
    var ir:int;
    ir <- 12+2*keccak_l-nr;
    while (ir < 12+2*keccak_l) {
      st <@ keccak_Rnd (st, ir);
      ir <- ir + 1;
    }
    return (st);
  }

  (** Section 3.4 - KECCAK-f[b] *)
  proc keccak_f1600 (st: state) : state = {
    st <@ keccak_p1600 (st, 12+2*keccak_l);
    return (st);
  }
}.



