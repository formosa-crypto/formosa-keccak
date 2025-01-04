(******************************************************************************
   Keccak1600_imem_avx2.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

from JazzEC require import Jazz_avx2.

from JazzEC require import WArray200.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec.


require import Keccak1600_avx2 Keccakf1600_avx2.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

(*
addstate_imem_avx2
*)
lemma addstate_imem_avx2_ll: islossless M.__addstate_imem_avx2
 by islossless.

hoare addstate_imem_avx2_h _st _buf _len _trailb:
 M.__addstate_imem_avx2
 : st=_st /\ buf=_buf /\ lEN=_len /\ tRAILB=_trailb
 ==> true.
proof.
admit.
qed.

(*
absorb_imem_avx2
*)
phoare absorb_imem_avx2_ll:
 [ M.__absorb_imem_avx2
 : 0 < rATE8 <= 200 /\ to_uint buf + lEN < W64.modulus
 ==> true
 ] = 1%r.
proof.
proc.
seq 3: (0 < rATE8 <=200 /\ iTERS < W64.modulus) => //=.
  sp; if => //=.
   while (iTERS=lEN %/ rATE8 /\ to_uint i <= iTERS < W64.modulus) (iTERS-to_uint i).
    move=> z; wp.
    call keccakf1600_avx2_ll.
    call addstate_imem_avx2_ll.
    auto => /> &m ??; rewrite ultE of_uintK modz_small. 
     smt(W64.to_uint_cmp).
    by move => H; rewrite to_uintD_small /= /#. 
   auto => /> &m *.
   split; first smt(W64.to_uint_cmp).
   by move=> i *; rewrite ultE of_uintK modz_small; smt(W64.to_uint_cmp).
  auto => /> /#.
 by islossless.
hoare => /=.
sp; if => //=.
 while #post.
 wp; call (:true) => //=.
 call (:true) => //=.
 auto => /> *.
 smt(W64.to_uint_cmp).
auto => /> *.
smt().
qed.


hoare absorb_imem_avx2_h _mem _st _buf _len _r8 _tb:
 M.__absorb_imem_avx2
 : st=_st /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
   /\ Glob.mem=_mem /\ 0 < rATE8 <= 200 /\ to_uint buf + lEN < W64.modulus
 ==> Glob.mem = _mem
  /\ absorb_spec_avx2 _r8 _tb (memread _mem (to_uint _buf) _len) res.`1
  /\ res.`2 = _buf + W64.of_int _len.
proof.
proc.
admit.
qed.

phoare absorb_imem_avx2_ph _mem _st _buf _len _r8 _tb:
 [ M.__absorb_imem_avx2
 : st=_st /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
   /\ Glob.mem=_mem /\ 0 < rATE8 <= 200 /\ to_uint buf + lEN < W64.modulus
 ==> Glob.mem = _mem
  /\ absorb_spec_avx2 _r8 _tb (memread _mem (to_uint _buf) _len) res.`1
  /\ res.`2 = _buf + W64.of_int _len
 ] = 1%r.
proof.
by conseq absorb_imem_avx2_ll (absorb_imem_avx2_h _mem _st _buf _len _r8 _tb).
qed.


(*
   INCREMENTAL (FIXED-SIZE) MEMORY ABSORB
   ======================================
*)

(*
pstate_imem_avx2
*)
phoare pstate_imem_avx2_ll: 
 [ M.__pstate_imem_avx2
 : 0 <= aT <= aT + lEN + b2i (tRAILB<>0) <= 200
 ==> true
 ] = 1%r.
proof.
proc => /=.
sp; if => //.
 admit.
if => //.
 admit.
by islossless.
qed.

hoare pstate_imem_avx2_h _mem _pst _at _buf _len _tb:
 M.__pstate_imem_avx2
 : Glob.mem=_mem /\ pst=_pst /\ aT=_at /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= aT <= aT + lEN + b2i (_tb<>0) <= 200
 /\ to_uint buf + lEN < W64.modulus
 ==> Glob.mem = _mem
  /\ res.`1 = fillpst_at _pst _at (memread _mem (to_uint _buf) _len ++ if _tb<>0 then [W8.of_int _tb] else [])
  /\ res.`2 = _at + _len
  /\ res.`3 = _buf + W64.of_int _len.
proof.
proc.
admitted.

phoare pstate_imem_avx2_ph _mem _pst _at _buf _len _tb:
 [ M.__pstate_imem_avx2
 : Glob.mem=_mem /\ pst=_pst /\ aT=_at /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= aT <= aT + lEN + b2i (_tb<>0) <= 200
 /\ to_uint buf + lEN < W64.modulus
 ==> Glob.mem = _mem
  /\ res.`1 = fillpst_at _pst _at (memread _mem (to_uint _buf) _len ++ if _tb<>0 then [W8.of_int _tb] else [])
  /\ res.`2 = _at + _len
  /\ res.`3 = _buf + W64.of_int _len
 ] = 1%r.
proof.
by conseq pstate_imem_avx2_ll (pstate_imem_avx2_h _mem _pst _at _buf _len _tb).
qed.

(*
pabsorb_imem_avx2
*)
phoare pabsorb_imem_avx2_ll:
 [ M.__pabsorb_imem_avx2
 : 0 <= aT < 200
 /\ 0 < rATE8 <= 200
 /\ to_uint buf + lEN < W64.modulus
 ==> true
 ] = 1%r.
proof.
proc => /=.
sp; if => //.
 admit.
if => //.
 admit.
admit.
qed.

hoare pabsorb_imem_avx2_h _mem _l _buf _len _r8 _tb:
 M.__pabsorb_imem_avx2
 : Glob.mem=_mem /\ aT = size _l %% _r8 /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l1 pst st
 /\ 0 <= _len
 /\ to_uint _buf + _len < W64.modulus
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l1 ++ memread _mem (to_uint _buf) _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l1 ++ memread _mem (to_uint _buf) _len) res.`1 res.`3
          /\ res.`2 = (size _l1 + _len) %% _r8
          /\ res.`4 = _buf + W64.of_int _len).
proof.
proc => /=.
admitted.

phoare pabsorb_imem_avx2_ph _mem _l1 _l2 _buf _len _r8 _tb:
 [ M.__pabsorb_imem_avx2
 : Glob.mem=_mem /\ aT = size _l %% _r8 /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ pabsorb_spec_avx2 _r8 _l1 pst st
 /\ 0 <= _len
 /\ to_uint _buf + _len < W64.modulus
 ==> if _tb <> 0
     then absorb_spec_avx2 _r8 _tb (_l1 ++ memread _mem (to_uint _buf) _len) res.`3
     else pabsorb_spec_avx2 _r8 (_l1 ++ memread _mem (to_uint _buf) _len) res.`1 res.`3
          /\ res.`2 = (size _l1 + _len) %% _r8
          /\ res.`4 = _buf + W64.of_int _len)
 ] = 1%r.
proof.
conseq pabsorb_imem_avx2_ll (pabsorb_imem_avx2_h _mem _l1 _l2 _buf _len _r8 _tb) => |> &m ->.
by rewrite /pabsorb_spec_avx2 => [#] /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

(*
dumpstate_imem_avx2
*)
lemma dumpstate_imem_avx2_ll: islossless M.__dumpstate_imem_avx2
 by islossless.

hoare dumpstate_imem_avx2_h _mem _buf _len _st:
 M.__dumpstate_imem_avx2
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (sub (stbytes (stavx2_to_st25 _st)) 0 _len)
  /\ res = _buf + W64.of_int _len.
proof.
proc => /=.
admitted.

phoare dumpstate_imem_avx2_ph _mem _buf _len _st:
 [ M.__dumpstate_imem_avx2
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (sub (stbytes (stavx2_to_st25 _st)) 0 _len)
  /\ res = _buf + W64.of_int _len
 ] = 1%r.
proof.
by conseq dumpstate_imem_avx2_ll (dumpstate_imem_avx2_h _mem _buf _len _st).
qed.

(*
squeeze_imem_avx2
*)
lemma squeeze_imem_avx2_ll: islossless M.__squeeze_imem_avx2.
proof.
proc; sp; if=> //.
seq 1: true => //.
 if => //.
 while (0 < iTERS) (iTERS-to_uint i).
  move=> z.
  wp; call dumpstate_imem_avx2_ll.
  call keccakf1600_avx2_ll.
  auto => /> &m; rewrite ultE of_uintK => /= *.
  by rewrite to_uintD_small /= /#.
 auto => /> &m i ?H; rewrite ultE of_uintK /#.
if => //.
call  dumpstate_imem_avx2_ll.
call keccakf1600_avx2_ll.
by auto.
qed.

hoare squeeze_imem_avx2_h _mem _buf _len _st _r8:
 M.__squeeze_imem_avx2
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st))
  /\ res.`1 = _buf + W64.of_int _len
  /\ res.`2 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1)).
proof.
proc.
admitted.

phoare squeeze_imem_avx2_ph _mem _buf _len _st _r8:
 [ M.__squeeze_imem_avx2
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (SQUEEZE1600 _r8 _len (stavx2_to_st25 _st))
  /\ res.`1 = _buf + W64.of_int _len
  /\ res.`2 = stavx2_from_st25 (st_i (stavx2_to_st25 _st) ((_len-1) %/ _r8 + 1))
 ] = 1%r.
proof.
by conseq squeeze_imem_avx2_ll (squeeze_imem_avx2_h _mem _buf _len _st _r8).
qed.

