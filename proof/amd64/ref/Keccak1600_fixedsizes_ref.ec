(******************************************************************************
   Keccak1600_imem_ref.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  REF implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.

from JazzEC require import WArray200.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec.


require import Keccak1600_ref Keccakf1600_ref.
require import Keccak1600_subreadwrite.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_m_ref_ll: islossless M.__addstate_m_ref.
proof.
islossless.
while true (aT %/ 8 + _LEN %/ 8 - at).
 by move=> z; auto; smt().
by auto; smt().
qed.

hoare addstate_m_ref_h _mem _st _at _buf _len _tb:
 M.__addstate_m_ref
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
  in Glob.mem=_mem
  /\ res.`1 = addstate_at _st _at l
  /\ res.`2 = _at + size l
  /\ res.`3 = _buf + _len.
proof.
admitted.

phoare addstate_m_ref_ph _mem _st _at _buf _len _tb:
 [ M.__addstate_m_ref
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
  in Glob.mem=_mem
  /\ res.`1 = addstate_at _st _at l
  /\ res.`2 = _at + size l
  /\ res.`3 = _buf + _len
 ] = 1%r.
proof.
by conseq addstate_m_ref_ll (addstate_m_ref_h _mem _st _at _buf _len _tb).
qed.

lemma absorb_m_ref_ll: islossless M.__absorb_m_ref.
proof.
proc; simplify.
seq 2: true => //.
 call addstate_m_ref_ll.
 if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ref_ll.
  call addstate_m_ref_ll.
  by auto => /#.
 wp; call keccakf1600_ref_ll.
 wp; call addstate_m_ref_ll.
 by auto => /#.
if => //.
by call addratebit_ref_ll.
qed.

hoare absorb_m_ref_h _l _mem _buf _len _r8 _tb:
 M.__absorb_m_ref
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem _buf _len)
       /\ res.`3 = _buf + _len
     else pabsorb_spec_ref _r8 (_l ++ memread _mem _buf _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + _len.
proof.
proc.
admitted.

phoare absorb_m_ref_ph _l _mem _buf _len _r8 _tb:
 [ M.__absorb_m_ref
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem _buf _len)
       /\ res.`3 = _buf + (max 0 _len)
     else pabsorb_spec_ref _r8 (_l ++ memread _mem _buf _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + _len
 ] = 1%r.
proof.
by conseq absorb_m_ref_ll (absorb_m_ref_h _l _mem _buf _len _r8 _tb) => /> /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_m_ref_ll: islossless M.__dumpstate_m_ref.
proof.
proc => /=.
seq 2: true => //.
 while true (_LEN %/ 8 - i).
  by move=> z; auto => /#. 
 by auto => /#.
by islossless.
qed.

hoare dumpstate_m_ref_h _mem _buf _len _st:
 M.__dumpstate_m_ref
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len.
proof.
proc => /=.
admitted.

phoare dumpstate_m_ref_ph _mem _buf _len _st:
 [ M.__dumpstate_m_ref
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len
 ] = 1%r.
proof.
by conseq dumpstate_m_ref_ll (dumpstate_m_ref_h _mem _buf _len _st).
qed.

lemma squeeze_m_ref_ll: islossless M.__squeeze_m_ref.
proof.
proc; simplify.
seq 2: true => //.
 while true (_LEN %/ _RATE8 - i).
  move => z; auto => />.
  call dumpstate_m_ref_ll.
  call keccakf1600_ref_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_m_ref_ll.
call keccakf1600_ref_ll.
by auto => /#.
qed.

hoare squeeze_m_ref_h _mem _buf _len _st _r8:
 M.__squeeze_m_ref
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len.
proof.
proc.
admitted.

phoare squeeze_m_ref_ph _mem _buf _len _st _r8:
 [ M.__squeeze_m_ref
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len
 ] = 1%r.
proof.
by conseq squeeze_m_ref_ll (squeeze_m_ref_h _mem _buf _len _st _r8).
qed.



abstract theory KeccakArrayRef.

op _ASIZE: int.

axiom _ASIZE_ge0: 0 <= _ASIZE.
axiom _ASIZE_u64: _ASIZE < W64.modulus.

(*
module type MParam = {
  proc keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t
  proc state_init_ref (st:W64.t Array25.t) : W64.t Array25.t
  proc addratebit_ref (st:W64.t Array25.t, _RATE8:int) : W64.t Array25.t
}.
*)

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
  proc __addstate_ref (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                       offset:int, _LEN:int, _TRAILB:int) : W64.t Array25.t *
                                                            int * int = {
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var at:int;
    dELTA <- 0;
    aT8 <- aT;
    aT <- (8 * (aT %/ 8));
    if ((aT8 <> 0)) {
      (dELTA, _LEN, _TRAILB, aT8, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, 
      offset, dELTA, _LEN, _TRAILB, aT, aT8);
      st.[(aT %/ 8)] <- (st.[(aT %/ 8)] `^` w);
      aT <- aT8;
    } else {
      
    }
    offset <- (offset + dELTA);
    at <- (aT %/ 8);
    while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
      w <- (get64_direct (WA.init8 (fun i => buf.[i])) offset);
      offset <- (offset + 8);
      st.[at] <- (st.[at] `^` w);
      at <- (at + 1);
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, offset,
      0, _LEN, _TRAILB, aT, aT);
      st.[at] <- (st.[at] `^` w);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (st, aT, offset);
  }
  proc __absorb_ref (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                     _TRAILB:int, _RATE8:int) : W64.t Array25.t * int = {
    var _LEN:int;
    var iTERS:int;
    var offset:int;
    var i:int;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    offset <- 0;
    _LEN <- _ASIZE;
    if ((_RATE8 <= (aT + _LEN))) {
      (st,  _0, offset) <@ __addstate_ref (st, aT, buf, offset,
      (_RATE8 - aT), 0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ M._keccakf1600_ref (st);
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate_ref (st, 0, buf, offset, _RATE8, 0);
        (* Erased call to spill *)
        st <@ M._keccakf1600_ref (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {
      
    }
    (st, aT,  _2) <@ __addstate_ref (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit_ref (st, _RATE8);
    } else {
      
    }
    return (st, aT);
  }
  proc __dumpstate_ref (buf:W8.t A.t, offset:int, _LEN:int,
                        st:W64.t Array25.t) : W8.t A.t * int = {
    var t:W64.t;
    var dELTA:int;
    var i:int;
    var  _0:int;
    i <- 0;
    while ((i < (_LEN %/ 8))) {
      t <- st.[i];
      buf <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf.[i_0])) 
      offset t)));
      offset <- (offset + 8);
      i <- (i + 1);
    }
    if ((0 < (_LEN %% 8))) {
      t <- st.[i];
      (buf, dELTA,  _0) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, 0, (_LEN %% 8),
      t);
      offset <- (offset + dELTA);
    } else {
      
    }
    return (buf, offset);
  }
  proc __squeeze_ref (st:W64.t Array25.t, buf:W8.t A.t, _RATE8:int) : 
  W64.t Array25.t * W8.t A.t = {
    var offset:int;
    var i:int;
    offset <- 0;
    i <- 0;
    while ((i < (_ASIZE %/ _RATE8))) {
      (* Erased call to spill *)
      st <@ M._keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, _RATE8, st);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    if ((0 < (_ASIZE %% _RATE8))) {
      (* Erased call to spill *)
      st <@ M._keccakf1600_ref (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate_ref (buf, offset, (_ASIZE %% _RATE8), st);
    } else {
      
    }
    return (st, buf);
  }
}.

lemma addstate_ref_ll: islossless MM.__addstate_ref.
proof.
islossless.
while true (aT %/ 8 + _LEN %/ 8 - at).
 by move=> z; auto; smt().
by auto; smt().
qed.

hoare addstate_ref_h _st _at _buf _off _len _tb:
 MM.__addstate_ref
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ offset + _len <= _ASIZE
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_at _st _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + _len.
proof.
proc => /=.
admitted.

phoare addstate_ref_ph _st _at _buf _off _len _tb:
 [ MM.__addstate_ref
   : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
   /\ 0 <= _at <= 200
   /\ 0 <= _len
   /\ _at + _len <= 200 - b2i (_tb<>0)
   /\ offset + _len <= _ASIZE
   ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
       in res.`1 = addstate_at _st _at l
       /\ res.`2 = _at + size l
       /\ res.`3 = _off + _len] = 1%r.
proof.
by conseq addstate_ref_ll (addstate_ref_h _st _at _buf _off _len _tb).
qed.

lemma absorb_ref_ll: islossless MM.__absorb_ref.
proof.
proc; simplify.
seq 4: true => //.
 call addstate_ref_ll.
 sp 2; if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ref_ll.
  call addstate_ref_ll.
  by auto => /#.
 wp; call keccakf1600_ref_ll.
 wp; call addstate_ref_ll.
 by auto => /#.
if => //.
by call addratebit_ref_ll.
qed.

hoare absorb_ref_h _l _buf _r8 _tb:
 MM.__absorb_ref
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8.
proof.
proc.
admitted.

phoare absorb_ref_ph _l _buf _r8 _tb:
 [ MM.__absorb_ref
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8
 ] = 1%r.
proof.
by conseq absorb_ref_ll (absorb_ref_h _l _buf _r8 _tb); smt(ge0_size).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

lemma dumpstate_ref_ll: islossless MM.__dumpstate_ref.
proof.
proc => /=.
seq 2: true => //.
 while true (_LEN %/ 8 - i).
  by move=> z; auto => /#. 
 by auto => /#.
by islossless.
qed.

hoare dumpstate_ref_h _buf _off _len _st:
 MM.__dumpstate_ref
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len.
proof.
proc.
admitted.

phoare dumpstate_ref_ph _buf _off _len _st:
 [ MM.__dumpstate_ref
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len
 ] = 1%r.
proof.
have ?:= dumpstate_ref_ll.
have ?:= (dumpstate_ref_h _buf _off _len _st).
admit (* ????? anomaly: EcLib.EcCoreGoal.InvalidGoalShape ????
by conseq dumpstate_ref_ll (dumpstate_ref_h _buf _off _len _st).
*).
qed.

lemma squeeze_ref_ll: islossless MM.__squeeze_ref.
proof.
proc; simplify.
seq 3: true => //.
 while true (_ASIZE %/ _RATE8 - i).
  move => z; auto => />.
  call dumpstate_ref_ll.
  call keccakf1600_ref_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_ref_ll.
call keccakf1600_ref_ll.
by auto => /#.
qed.

hoare squeeze_ref_h _buf _st _r8:
 MM.__squeeze_ref
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st).
proof.
proc.
admitted.

phoare squeeze_ref_ph _buf _st _r8:
 [ MM.__squeeze_ref
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st)
 ] = 1%r.
proof.
by conseq squeeze_ref_ll (squeeze_ref_h _buf _st _r8).
qed.

end KeccakArrayRef.
