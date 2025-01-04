(******************************************************************************
   Keccak1600_imem_ref.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  REF implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require export Keccakf1600_Spec.

from JazzEC require import Jazz_ref.

from JazzEC require import WArray200.
from JazzEC require import Array25.

from CryptoSpecs require import JWordList.
from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import FIPS202_SHA3_Spec Keccakf1600_Spec.


require import Keccak1600_ref Keccakf1600_ref.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

phoare addstate_imem_ref_ll: 
 [ M.__addstate_imem_ref
 : 0 <= aT <= 200
 /\ 0 <= lEN
 /\ aT+lEN <= 200 - b2i (tRAILB<>0)
 ==> true
 ] = 1%r.
proof.
proc.
admitted.

hoare addstate_imem_ref_h _mem _st _at _buf _len _tb:
 M.__addstate_imem_ref
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ to_uint _buf + _len < W64.modulus
 ==> let l = memread _mem (to_uint _buf) _len ++ if _tb<>0 then [W8.of_int _tb] else []
  in Glob.mem=_mem
  /\ res.`1 = addstate_at _st _at l
  /\ res.`2 = _at + size l
  /\ res.`3 = _buf + W64.of_int _len.
proof.
admit.
qed.

phoare addstate_imem_ref_ph _mem _st _at _buf _len _tb:
 [ M.__addstate_imem_ref
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ lEN=_len /\ tRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ res.`1 = addstate_at _st _at (memread _mem (to_uint _buf) _len)
  /\ res.`2 = _at + _len + b2i (_tb<>0)
  /\ res.`3 = _buf + W64.of_int (max 0 _len)
 ] = 1%r.
proof.
by conseq addstate_imem_ref_ll (addstate_imem_ref_h _mem _st _at _buf _len _tb).
qed.

phoare absorb_imem_ref_ll:
 [ M.__absorb_imem_ref
 : 0 < rATE8 <= 200
 /\ 0 <= aT <= rATE8
 /\ 0 <= lEN
 ==> true
 ] = 1%r.
proof.
proc.
sp; if => //=.
 case: (tRAILB<>0).
  rcondt 2; first by call (: true) => //.
  call addratebit_ref_ll.
  by call addstate_imem_ref_ll; auto => /> &m * /#.
 rcondf 2; first by call (: true) => //.
 by call addstate_imem_ref_ll; auto => /> &m * /#.
seq 1: #[/:-2]{~aLL}pre => //.
 if => //.
  wp; call keccakf1600_ref_ll.
  wp; call addstate_imem_ref_ll; auto => /> &m *; split; first smt().
  by move=> ??? /#.
 seq 5: true => //.
  call addstate_imem_ref_ll => /=.
  wp; while #pre (iTERS - to_uint i).
   move=> z.
   wp; call keccakf1600_ref_ll.
   call addstate_imem_ref_ll; auto => /> &m Hr1 Hr2 Hat1 Hat2 Hlen0; rewrite ultE of_uintK.
   move=> /= Hi; split; first smt().
   by move=> ?; rewrite to_uintD_small /=; smt(W64.to_uint_cmp).
  by auto => /> &m ????? i; rewrite ultE of_uintK /=; smt(W64.to_uint_cmp).
 by islossless.
hoare => /=.
if => //.
wp; call (: true) => //.
wp; call (: true) => //.
by auto => /> /#.
qed.

hoare absorb_imem_ref_h _l _mem _buf _len _r8 _tb:
 M.__absorb_imem_ref
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem (to_uint _buf) _len)
       /\ res.`3 = _buf + W64.of_int _len
     else pabsorb_spec_ref _r8 (_l ++ memread _mem (to_uint _buf) _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + W64.of_int _len.
proof.
proc.
admit.
qed.

phoare absorb_imem_ref_ph _l _mem _buf _len _r8 _tb:
 [ M.__absorb_imem_ref
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ lEN=_len /\ rATE8=_r8 /\ tRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _len
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = _mem
  /\ if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ memread _mem (to_uint _buf) _len)
       /\ res.`3 = _buf + W64.of_int (max 0 _len)
     else pabsorb_spec_ref _r8 (_l ++ memread _mem (to_uint _buf) _len) res.`1
       /\ res.`2 = (size _l + _len) %% _r8
       /\ res.`3 = _buf + W64.of_int _len
 ] = 1%r.
proof.
by conseq absorb_imem_ref_ll (absorb_imem_ref_h _l _mem _buf _len _r8 _tb) => /> /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

phoare dumpstate_imem_ref_ll: 
 [ M.__dumpstate_imem_ref
 : 0 <= lEN <= 200
 ==> true
 ] = 1%r.
proof.
proc => /=.
seq 2: true => //.
 while (#pre /\ 0 <= to_sint i <= lEN%/8) (lEN %/ 8 - to_sint i).
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

hoare dumpstate_imem_ref_h _mem _buf _len _st:
 M.__dumpstate_imem_ref
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (sub (stbytes _st) 0 _len)
  /\ res = _buf + W64.of_int _len.
proof.
proc => /=.
admitted.

phoare dumpstate_imem_ref_ph _mem _buf _len _st:
 [ M.__dumpstate_imem_ref
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (sub (stbytes _st) 0 _len)
  /\ res = _buf + W64.of_int _len
 ] = 1%r.
proof.
by conseq dumpstate_imem_ref_ll (dumpstate_imem_ref_h _mem _buf _len _st).
qed.


phoare squeeze_imem_ref_ll: 
 [ M.__squeeze_imem_ref
 : 0 < rATE8 <= 200
 ==> true
 ] = 1%r.
proof.
proc; sp; if=> //=.
seq 1: #pre => //.
  if => //.
  while #pre (iTERS - to_uint i).
   move => z.
   wp; call dumpstate_imem_ref_ll.
   call keccakf1600_ref_ll; auto => /> &m ????.
   by rewrite ultE of_uintK => /= Hi; rewrite to_uintD_small /= /#.
  by auto => /> &m ???? i Hi; rewrite ultE of_uintK /#.
 if => //.
 call dumpstate_imem_ref_ll.
 call keccakf1600_ref_ll.
 by auto => /#.
hoare => /=.
if => //.
by while true; auto.
qed.

hoare squeeze_imem_ref_h _mem _buf _len _st _r8:
 M.__squeeze_imem_ref
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (SQUEEZE1600 _r8 _len _st)
  /\ res.`1 = _buf + W64.of_int _len
  /\ res.`2 = st_i _st ((_len-1) %/ _r8 + 1).
proof.
proc.
admitted.

phoare squeeze_imem_ref_ph _mem _buf _len _st _r8:
 [ M.__squeeze_imem_ref
 : Glob.mem=_mem /\ buf=_buf /\ lEN=_len /\ st=_st /\ rATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ to_uint _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem (to_uint _buf) (SQUEEZE1600 _r8 _len _st)
  /\ res.`1 = _buf + W64.of_int _len
  /\ res.`2 = st_i _st ((_len-1) %/ _r8 + 1)
 ] = 1%r.
proof.
by conseq squeeze_imem_ref_ll (squeeze_imem_ref_h _mem _buf _len _st _r8).
qed.

