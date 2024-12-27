require import AllCore IntDiv StdOrder CoreMap List.

from Jasmin require import JModel_x86.

import SLH64.
import IntOrder.

require import Array25 WArray200.
from Jasmin require import JArray.


from CryptoSpecs require import FIPS202_SHA3.
from CryptoSpecs require export Keccakf1600_Spec Keccak1600_Spec.


op addst_at (st: W64.t Array25.t) at l =
 let st200 = stbytes st in
 stwords
  (WArray200.fill 
   (fun i => st200.[i] `^` (nth W8.zero l (i-at))) at (size l) st200).





abstract theory Keccak1600_array_ref.

op aSIZE: int.
axiom aSIZE_ge0: 0 <= aSIZE.

module type MParam = {
  proc keccakf1600_ref (a:W64.t Array25.t) : W64.t Array25.t
  proc state_init_ref (st:W64.t Array25.t) : W64.t Array25.t
  proc addratebit_ref (st:W64.t Array25.t, rATE8:int) : W64.t Array25.t
}.

clone import PolyArray as A
 with op size <= aSIZE
      proof ge0_size by exact aSIZE_ge0.

clone import WArray as WA
 with op size <= aSIZE.

module M(P: MParam) = {
  proc __aread_subu64 (buf:W8.t A.t, offset:W64.t, dELTA:int, lEN:int,
                       tRAIL:int) : int * int * int * W64.t = {
    var w:W64.t;
    var iLEN:int;
    var t16:W64.t;
    var t8:W64.t;
    iLEN <- lEN;
    if ((lEN <= 0)) {
      w <- (W64.of_int (tRAIL %% 256));
      tRAIL <- 0;
    } else {
      if ((8 <= lEN)) {
        w <-
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          w <-
          (zeroextu64
          (get32_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          t16 <-
          (zeroextu64
          (get16_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA)))));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          t16 <- (W64.of_int 0);
        }
        if (((1 <= lEN) \/ (tRAIL <> 0))) {
          if ((1 <= lEN)) {
            t8 <-
            (zeroextu64
            (get8_direct (WA.init8 (fun i => buf.[i]))
            (W64.to_uint (offset + (W64.of_int dELTA)))));
            if ((tRAIL <> 0)) {
              t8 <- (t8 `|` (W64.of_int (256 * (tRAIL%%256))));
            } else {
              
            }
            dELTA <- (dELTA + 1);
            lEN <- (lEN - 1);
          } else {
            t8 <- (W64.of_int (tRAIL%%256));
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
    return (dELTA, lEN, tRAIL, w);
  }
  proc __awrite_subu64 (buf:W8.t A.t, offset:W64.t, dELTA:int,
                        lEN:int, w:W64.t) : W8.t A.t * int * int = {
    
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint (offset + (W64.of_int dELTA))) w)));
        dELTA <- (dELTA + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set32_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu32 w))));
          w <- (w `>>` (W8.of_int 32));
          dELTA <- (dELTA + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set16_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu16 w))));
          w <- (w `>>` (W8.of_int 16));
          dELTA <- (dELTA + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          buf <-
          (A.init
          (WA.get8
          (WA.set8_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))) (truncateu8 w))));
          dELTA <- (dELTA + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, dELTA, lEN);
  }
  proc __addstate_array_ref (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                             offset:W64.t, lEN:int, tRAILB:int) : W64.t Array25.t *
                                                                  int * W64.t = {
    var aLL:int;
    var lO:int;
    var at:W64.t;
    var dELTA:int;
    var t:W64.t;
    var  _0:int;
    var  _1:int;
    var  _2:int;
    var  _3:int;
    var  _4:int;
    var  _5:int;
    aLL <- (aT + lEN);
(*if (0 <= aT /\ aLL+b2i(tRAILB<>0) <= 200) {*)

    lO <- (aT %% 8);
    at <- (W64.of_int (aT %/ 8));
    dELTA <- 0;
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        (dELTA,  _2,  _3, t) <@ __aread_subu64 (buf, offset, dELTA, lEN,
        tRAILB);
        t <- (t `<<` (W8.of_int (8 * lO)));
        t <- (t `^` st.[(W64.to_uint at)]);
        st.[(W64.to_uint at)] <- t;
        lO <- 0;
        aT <- 0;
        lEN <- 0;
        tRAILB <- 0;
      } else {
        if ((8 <= lEN)) {
          t <-
          (get64_direct (WA.init8 (fun i => buf.[i]))
          (W64.to_uint (offset + (W64.of_int dELTA))));
          offset <- (offset + (W64.of_int (8 - lO)));
        } else {
          (dELTA,  _0,  _1, t) <@ __aread_subu64 (buf, offset, dELTA,
          (8 - lO), tRAILB);
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
    offset <- (offset + (W64.of_int dELTA));
    dELTA <- 0;
    if ((8 <= lEN)) {
      while ((at \ult (W64.of_int ((aT %/ 8) + (lEN %/ 8))))) {
        t <-
        (get64_direct (WA.init8 (fun i => buf.[i]))
        (W64.to_uint offset));
        t <- (t `^` st.[(W64.to_uint at)]);
        st.[(W64.to_uint at)] <- t;
        at <- (at + (W64.of_int 1));
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      (dELTA,  _4,  _5, t) <@ __aread_subu64 (buf, offset, dELTA, lO,
      tRAILB);
      offset <- (offset + (W64.of_int dELTA));
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
        tRAILB <- 0;
      } else {
        
      }
      t <- (t `^` st.[(W64.to_uint at)]);
      st.[(W64.to_uint at)] <- t;
    } else {
      
    }
(*}*)
    return (st, aLL, offset);
  }
  proc __absorb_array_ref (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                           offset:W64.t, lEN:int, rATE8:int, tRAILB:int) : 
  W64.t Array25.t * int * W64.t = {
    var aLL:int;
    var iTERS:int;
    var i:W64.t;
    var  _0:int;
    var  _1:int;
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      (st, aT, offset) <@ __addstate_array_ref (st, aT, buf, offset, 
      lEN, tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_ref (st, rATE8);
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        (st,  _0, offset) <@ __addstate_array_ref (st, aT, buf, offset,
        (rATE8 - aT), 0);
        lEN <- (lEN - (rATE8 - aT));
        st <@ P.keccakf1600_ref (st);
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int iTERS))) {
        (st,  _1, offset) <@ __addstate_array_ref (st, 0, buf, offset, 
        rATE8, 0);
        st <@ P.keccakf1600_ref (st);
        i <- (i + (W64.of_int 1));
      }
      lEN <- (aLL %% rATE8);
      (st, aT, offset) <@ __addstate_array_ref (st, 0, buf, offset, lEN,
      tRAILB);
      if ((tRAILB <> 0)) {
        st <@ P.addratebit_ref (st, rATE8);
      } else {
        
      }
    }
    return (st, aT, offset);
  }
  proc __dumpstate_array_ref (buf:W8.t A.t, offset:W64.t, lEN:int,
                              st:W64.t Array25.t) : W8.t A.t * W64.t = {
    var i:W64.t;
    var t:W64.t;
    var  _0:int;
    var  _1:int;
    i <- (W64.of_int 0);
    while ((i \slt (W64.of_int (lEN %/ 8)))) {
      t <- st.[(W64.to_uint i)];
      buf <-
      (A.init
      (WA.get8
      (WA.set64_direct (WA.init8 (fun i_0 => buf.[i_0]))
      (W64.to_uint offset) t)));
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 8));
    }
    if ((0 < (lEN %% 8))) {
      t <- st.[(W64.to_uint i)];
      (buf,  _0,  _1) <@ __awrite_subu64 (buf, offset, 0, (lEN %% 8), t);
      offset <- (offset + (W64.of_int (lEN %% 8)));
    } else {
      
    }
    return (buf, offset);
  }
  proc __squeeze_array_ref (buf:W8.t A.t, offset:W64.t, lEN:int,
                            st:W64.t Array25.t, rATE8:int) : W8.t A.t *
                                                             W64.t *
                                                             W64.t Array25.t = {
    var iTERS:int;
    var lO:int;
    var i:W64.t;
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- (W64.of_int 0);
        while ((i \ult (W64.of_int iTERS))) {
          st <@ P.keccakf1600_ref (st);
          (buf, offset) <@ __dumpstate_array_ref (buf, offset, rATE8, st);
          i <- (i + (W64.of_int 1));
        }
      } else {
        
      }
      if ((0 < lO)) {
        st <@ P.keccakf1600_ref (st);
        (buf, offset) <@ __dumpstate_array_ref (buf, offset, lO, st);
      } else {
        
      }
    } else {
      
    }
    return (buf, offset, st);
  }
}.


(****************************************************************************
                      
****************************************************************************)

section.

declare module P <: MParam.

hoare aread_subu64_h _buf _off _dlt _len _trail:
 M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail]).
proof.
proc => /=.
auto => />.
split.
 (* _len <= 0 *)
 move=> Hlen_le0.
 split; first smt().
 split; first smt().
 split; first smt().
 rewrite ler_maxl 1:// ler_minl 1:// /sub mkseq0 /=.
 admit.
move=> Hlen_gt0; split.
 (* 8 <= _len *)
 move=> Hlen_le0.
 split; first smt().
 split; first smt().
 split; first smt().
 rewrite ler_maxr 1:/# ler_minr 1://.
 admit.
move=> Hlen_lt8.
have: _len \in iotared 1 7 by smt().
clear Hlen_gt0 Hlen_lt8; move: _len.
apply/List.allP; rewrite /max /min => /=.
split.
+ (* 1 *) split => Htrail.
  - admit.
  - admit.
split.
+ (* 2 *) split => Htrail.
  - admit.
  - admit.
split.
+ (* 3 *) split => Htrail.
  - admit.
  - admit.
split.
+ (* 4 *) split => Htrail.
  - admit.
  - admit.
split.
+ (* 5 *) split => Htrail.
  - admit.
  - admit.
split.
+ (* 6 *) split => Htrail.
  - admit.
  - admit.
+ (* 7 *) split => Htrail.
  - admit.
  - admit.
qed.

lemma  aread_subu64_ll: islossless M(P).__aread_subu64
by islossless.

phoare aread_subu64_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu64_ll (aread_subu64_h _buf _off _dlt _len _trail).
qed.

hoare awrite_subu64_h _buf _off _dlt _len _w:
 M(P).__awrite_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W8u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8.
proof.
proc => /=.
auto => /> &m; split.
 move=> Hlen_gt0; split.
  move=> Hlen_ge8.
  rewrite ler_maxr 1:/# ler_minr 1:/# /=.
  admit.
 move=> Hlen_lt8.
 have: _len \in iotared 1 7 by smt().
 clear Hlen_gt0 Hlen_lt8; move: _len.
 apply/List.allP; rewrite /max /min => /=.
 admit.
move=> Hlen_lt0.
rewrite ler_maxl 1:/# /min /= fillE tP => i Hi.
rewrite initiE 1://; beta.
by rewrite ifF /#.
qed.

lemma  awrite_subu64_ll: islossless M(P).__awrite_subu64
by islossless.

phoare awrite_subu64_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W8u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8
 ] = 1%r.
proof.
by conseq awrite_subu64_ll (awrite_subu64_h _buf _off _dlt _len _w).
qed.

hoare addstate_array_ref_h _st _at _buf _off _len _tb:
 M(P).__addstate_array_ref
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= aT <= aT + lEN <= 200 - b2i (tRAILB<>0)
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addst_at _st _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + (W64.of_int _len).
proof.
proc => /=.
admitted.

lemma addstate_array_ref_ll:
 phoare [ M(P).__addstate_array_ref
        : 0 <= aT <= aT + lEN <= 200 - b2i (tRAILB<>0)
        ==> true ] = 1%r.
proof.
proc => /=.
seq 7: (#pre) => //=.
  sp; if => //>.
   if => //=.
    by wp; call aread_subu64_ll; auto => />.
   if; auto => />.
    by move=> &m /#.
   by call aread_subu64_ll; auto => /> &m * /#.
  by auto => /> &m * /#.
 if.
  seq 2: true => //=.
   exlim aT => _at.
   wp; while (_at+lEN <= 200) (_at %/ 8 + lEN %/ 8 - to_uint at).
    move=> z; auto => &m; rewrite ultE of_uintK => /> _?.
    by rewrite to_uintD_small /#.
   auto => /> &m ????; split.
    smt().
   by move=> /> at; rewrite ultE of_uintK /#.
  by islossless.
 by islossless.
hoare.
sp; if.
 if.
  by wp; call (:true); auto.
 if.
  by auto => /> /#.
 by wp; call (:true); auto => /> /#.
by auto => /#.
qed.

phoare addstate_array_ref_ph _st _at _buf _off _len _tb:
 [ M(P).__addstate_array_ref
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= aT <= aT + lEN <= 200 - b2i (tRAILB<>0)
 ==> let l = sub _buf (to_uint _off) _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addst_at _st _at l
     /\ res.`2 = _at + size l
     /\ res.`3 = _off + (W64.of_int _len)
 ] = 1%r.
proof.
by conseq addstate_array_ref_ll (addstate_array_ref_h _st _at _buf _off _len _tb).
qed.

hoare dumpstate_array_ref_h _buf _off _len _st:
 M(P).__dumpstate_array_ref
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len.
proc.
admitted.

lemma dumpstate_array_ref_ll _off _len:
 phoare [ M(P).__dumpstate_array_ref
        : offset=_off /\ lEN=_len
        /\ 0 <= _len <= 200
        /\ to_uint _off + _len <= aSIZE
        ==> true ] = 1%r.
proof.
proc => /=.
seq 2: true => //.
 while (#{~_off}pre /\ 0 <= to_sint i <= _len%/8) (_len %/ 8 - to_sint i).
  move=> z; auto => /> &m; rewrite sltE /= => Hlen0 Hlen1 Hi0 _.
  rewrite of_sintK /smod ifF 1:/# modz_small 1:/# => Hi1.
  have E: to_sint W64.one = 1 by rewrite to_sintE /smod.
  do split. 
  + by rewrite to_sintD_small E /#.
  + by rewrite to_sintD_small E /#.
  + by rewrite to_sintD_small E /#.
 auto => /> &m; rewrite to_sintE /= => *.
 split.
  by rewrite /smod /= /#.
 by move=> i ???; rewrite sltE of_sintK /smod ifF 1:/# modz_small 1:/# /#.
by islossless.
qed.

phoare dumpstate_array_ref_ph _buf _off _len _st:
 [ M(P).__dumpstate_array_ref
 : buf=_buf /\ offset=_off /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len
 ] = 1%r.
proof.
by conseq (dumpstate_array_ref_ll _off _len) (dumpstate_array_ref_h _buf _off _len _st).
qed.

declare axiom P_ok:
 islossless P.keccakf1600_ref
 /\ islossless P.state_init_ref
 /\ islossless P.addratebit_ref
 /\ (forall _st,
     hoare [ P.keccakf1600_ref
           : a = _st
           ==> res = keccak_f1600_op _st
           ])
 /\ hoare [ P.state_init_ref
          : true
          ==> res = st0
          ]
 /\ (forall _st _rate8,
     hoare [ P.addratebit_ref
           : st=_st /\ rATE8=_rate8
           /\ 0 < _rate8 <= 200
           ==> res = addratebit _rate8 _st
           ]).

lemma absorb_array_ref_ll:
 phoare [ M(P).__absorb_array_ref
        : 0 <= aT < 200
        /\ 0 <= lEN
        /\ 0 < rATE8 <= 200
        ==> true ] = 1%r.
proof.
move: P_ok => [# F_ll init_ll addrb_ll F_h init_h addrb_h].
proc => /=.
sp; if.
 case: (tRAILB=0) => //=.
  rcondf 2.
   ecall (addstate_array_ref_h st aT buf offset lEN tRAILB).
   by auto => /> &m /#.
  call addstate_array_ref_ll.
  by auto => /> &m /#.
 rcondt 2.
  ecall (addstate_array_ref_h st aT buf offset lEN tRAILB).
  by auto => /> &m /#.
 call addrb_ll.
 call addstate_array_ref_ll.
 by auto => /> &m /#.
if.
 admit.
sp; exlim iTERS => n.
seq 3: true => //=.
 call addstate_array_ref_ll => /=.
 wp; while (#post) (n-to_uint i).
  move=> z.
  wp; call F_ll.
 call addstate_array_ref_ll => /=.
 auto => /> &m *.
 rewrite to_uintD_small of_uintK /=.
  admit.
 split.
  admit.
 smt().
 auto => /> *.
 admit.
islossless.
qed.

lemma squeeze_array_ref_ll _off _len _rate8:
 phoare [ M(P).__squeeze_array_ref
        : offset=_off /\ lEN=_len /\ rATE8=_rate8
        /\ 0 <= _len
        /\ to_uint _off + _len <= aSIZE
        /\ 0 < _rate8 <= 200
        ==> true
        ] = 1%r.
proof.
move: P_ok => [# F_ll init_ll addrb_ll F_h init_h addrb_h].
proc => /=.
sp; if => //=.
seq 1: #[/:]{~offset}pre => //=.
  admit.
 if => //=.
 exlim lO => lo.
 exlim offset => off.
 call (dumpstate_array_ref_ll off lo).
 call F_ll; auto => /> *.
 split; first smt().
 admit (* adjust *).
hoare => /=.
if => //=.
while (#post).
 wp; ecall (dumpstate_array_ref_h buf offset rATE8 st).
 call (:true); auto => /> *.
 admit.
by auto => /=.
qed.

hoare squeeze_array_ref_h _buf _off _len _st _rate8:
 M(P).__squeeze_array_ref
 : buf=_buf /\ offset=_off /\ lEN=_len
 /\ st=_st /\ rATE8=_rate8
 /\ 0 <= _len
 /\ to_uint _off + _len <= aSIZE
 /\ 0 < _rate8 <= 200
 ==> res.`1 = A.fill (fun i => (SQUEEZE1600 _rate8 _len _st).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len.
proof.
move: P_ok => [# F_ll init_ll addrb_ll F_h init_h addrb_h].
proc => /=.
admitted.

phoare squeeze_array_ref_ph _buf _off _len _st _rate8:
 [ M(P).__squeeze_array_ref
 : buf=_buf /\ offset=_off /\ lEN=_len
 /\ st=_st /\ rATE8=_rate8
 /\ 0 <= _len
 /\ to_uint _off + _len <= aSIZE
 /\ 0 < _rate8 <= 200
 ==> res.`1 = A.fill (fun i => (SQUEEZE1600 _rate8 _len _st).[i-to_uint _off]) (to_uint _off) _len _buf
  /\ res.`2 = _off + W64.of_int _len
 ] = 1%r.
proof.
by conseq (squeeze_array_ref_ll _off _len _rate8) 
     (squeeze_array_ref_h _buf _off _len _st _rate8).
qed.

hoare absorb_array_ref_h _st _buf _off _len _rate8 _tb:
 M(P).__absorb_array_ref
 : st = _st /\ buf=_buf /\ rATE8=_rate8
 /\ offset=_off /\ lEN=_len /\ tRAILB=_tb
 /\ to_uint _off + _len <= aSIZE
 ==> res.`1 = ABSORB1600 (W8.of_int _tb) _rate8 (sub _buf (to_uint _off) _len).
proof.
move: P_ok => [# F_ll init_ll addrb_ll F_h init_h addrb_h].
proc => /=.
admitted.

end section.
