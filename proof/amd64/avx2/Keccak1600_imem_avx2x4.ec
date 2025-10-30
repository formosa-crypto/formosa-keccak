(******************************************************************************
   Keccak1600_imem_avx2.ec:

   Correctness proof for the Keccak (fixed-sized) memory absorb/squeeze
  4-way AVX2 implementation



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


require export Keccak1600_avx2x4 Keccakf1600_avx2x4.

(* TODO: Move this to a new file *)
lemma  mread_subu64_ll: islossless M.__mread_subu64
 by islossless.

(*
hoare aread_subu64_h _buf _off _dlt _len _trail:
 M(P).__aread_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 8
  /\ res.`2 = _len - min (max 0 _len) 8
  /\ res.`3 = (if _len < 8 then 0 else _trail)
  /\ res.`4 = W8u8.pack8 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 8) ++ [W8.of_int _trail]).
admitted.

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
*)

lemma  mread_subu128_ll: islossless M.__mread_subu128
 by islossless.

(*
hoare aread_subu128_h _buf _off _dlt _len _trail:
 M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail]).
admitted.

phoare aread_subu128_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 16
  /\ res.`2 = _len - min (max 0 _len) 16
  /\ res.`3 = (if _len < 16 then 0 else _trail)
  /\ res.`4 = W16u8.pack16 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 16) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu128_ll (aread_subu128_h _buf _off _dlt _len _trail).
qed.
*)

lemma  mread_subu256_ll: islossless M.__mread_subu256
 by islossless.

(*
hoare aread_subu256_h _buf _off _dlt _len _trail:
 M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail]).
admitted.

phoare aread_subu256_ph _buf _off _dlt _len _trail:
 [ M(P).__aread_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len /\ tRAIL=_trail
 ==> res.`1 = _dlt + min (max 0 _len) 32
  /\ res.`2 = _len - min (max 0 _len) 32
  /\ res.`3 = (if _len < 32 then 0 else _trail)
  /\ res.`4 = W32u8.pack32 (sub _buf (to_uint _off+_dlt) (min (max 0 _len) 32) ++ [W8.of_int _trail])
 ] = 1%r.
proof.
by conseq aread_subu256_ll (aread_subu256_h _buf _off _dlt _len _trail).
qed.
*)

lemma mwrite_subu64_ll: islossless M.__mwrite_subu64
 by islossless.

(*
hoare awrite_subu64_h _buf _off _dlt _len _w:
 M(P).__awrite_subu64
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W8u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 8) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 8
  /\ res.`3 = _len - min (max 0 _len) 8.
proof.
admitted.

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
*)

lemma mwrite_subu128_ll: islossless M.__mwrite_subu128
 by islossless.

(*
hoare awrite_subu128_h _buf _off _dlt _len _w:
 M(P).__awrite_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W16u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16.
proof.
admitted.

phoare awrite_subu128_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu128
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W16u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 16) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 16
  /\ res.`3 = _len - min (max 0 _len) 16
 ] = 1%r.
proof.
by conseq awrite_subu128_ll (awrite_subu128_h _buf _off _dlt _len _w).
qed.
*)

lemma mwrite_subu256_ll: islossless M.__mwrite_subu256
 by islossless.

(*
hoare awrite_subu256_h _buf _off _dlt _len _w:
 M(P).__awrite_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W32u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 32) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 32
  /\ res.`3 = _len - min (max 0 _len) 32.
proof.
admitted.

phoare awrite_subu256_ph _buf _off _dlt _len _w:
 [ M(P).__awrite_subu256
 : buf=_buf /\ offset=_off /\ dELTA=_dlt /\ lEN=_len
 ==> res.`1 = A.fill (nth W8.zero (W32u8.to_list _w)) (to_uint _off + _dlt) (min (max 0 _len) 32) _buf
  /\ res.`2 = _dlt + min (max 0 _len) 32
  /\ res.`3 = _len - min (max 0 _len) 32
 ] = 1%r.
proof.
by conseq awrite_subu256_ll (awrite_subu256_h _buf _off _dlt _len _w).
qed.
*)


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

phoare addstate_imem_avx2x4_ll: 
 [ M.__addstate_imem_avx2x4
 : 0 <= aT <= 200
 /\ 0 <= lEN
 /\ aT+lEN <= 200 - b2i (tRAILB<>0)
 ==> true
 ] = 1%r.
proof.
proc.
admitted.

phoare addstate_bcast_imem_avx2x4_ll: 
 [ M.__addstate_bcast_imem_avx2x4
 : 0 <= aT <= 200
 /\ 0 <= lEN
 /\ aT+lEN <= 200 - b2i (tRAILB<>0)
 ==> true
 ] = 1%r.
proof.
proc.
admitted.

phoare absorb_imem_avx2x4_ll:
 [ M.__absorb_imem_avx2x4
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
  call addratebit_avx2x4_ll.
  by call addstate_imem_avx2x4_ll; auto => /> &m * /#.
 rcondf 2; first by call (: true) => //.
 by call addstate_imem_avx2x4_ll; auto => /> &m * /#.
seq 1: #[/:-2]{~aLL}pre => //.
 if => //.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_imem_avx2x4_ll; auto => /> &m *; split; first smt().
  by move=> ??? /#.
 seq 5: true => //.
  call addstate_imem_avx2x4_ll => /=.
  wp; while #pre (iTERS - to_uint i).
   move=> z.
   wp; call keccakf1600_avx2x4_ll.
   call addstate_imem_avx2x4_ll; auto => /> &m Hr1 Hr2 Hat1 Hat2 Hlen0; rewrite ultE of_uintK.
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

phoare absorb_bcast_imem_avx2x4_ll:
 [ M.__absorb_bcast_imem_avx2x4
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
  call addratebit_avx2x4_ll.
  by call addstate_bcast_imem_avx2x4_ll; auto => /> &m * /#.
 rcondf 2; first by call (: true) => //.
 by call addstate_bcast_imem_avx2x4_ll; auto => /> &m * /#.
seq 1: #[/:-2]{~aLL}pre => //.
 if => //.
  wp; call keccakf1600_avx2x4_ll.
  wp; call addstate_bcast_imem_avx2x4_ll; auto => /> &m *; split; first smt().
  by move=> ??? /#.
 seq 5: true => //.
  call addstate_bcast_imem_avx2x4_ll => /=.
  wp; while #pre (iTERS - to_uint i).
   move=> z.
   wp; call keccakf1600_avx2x4_ll.
   call addstate_bcast_imem_avx2x4_ll; auto => /> &m Hr1 Hr2 Hat1 Hat2 Hlen0; rewrite ultE of_uintK.
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


(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)

phoare dumpstate_imem_avx2x4_ll: 
 [ M.__dumpstate_imem_avx2x4
 : 0 <= lEN <= 200
 ==> true
 ] = 1%r.
proof.
proc => /=.
seq 2: true => //.
 while (#pre /\ 0 <= to_sint i <= 32*(lEN%/32)) (32*(lEN %/ 32) - to_sint i).
  move=> z; inline*; auto => /> &m; rewrite !sltE /= => Hlen0 Hlen1 Hi0 _.
  rewrite of_sintK /smod ifF 1:/# modz_small 1:/# => Hi1.
  have E: to_sint (W64.of_int 32) = 32 by rewrite to_sintE /smod.
  do split. 
  + by rewrite to_sintD_small E /#.
  +  rewrite to_sintD_small E. smt(). admit.
  + by rewrite to_sintD_small E /#.
 auto => /> &m; rewrite to_sintE /= => *.
 split.
  by rewrite /smod /= /#.
 by move=> i ???; rewrite sltE of_sintK /smod ifF 1:/# modz_small 1:/# /#.
islossless.
admit.
qed.

lemma squeeze_imem_avx2x4_ll: islossless M.__squeeze_imem_avx2x4.
proof.
proc; sp; if=> //.
seq 1: true => //.
 if => //.
 while (0 < iTERS) (iTERS-to_uint i).
  move=> z.
  wp; call dumpstate_imem_avx2x4_ll.
  call keccakf1600_avx2x4_ll.
  auto => /> &m; rewrite ultE of_uintK => /= *.
  rewrite to_uintD_small /=.
   admit.
  admit.
 by auto => /> &m i ?H; rewrite ultE of_uintK /#.
if => //.
call  dumpstate_imem_avx2x4_ll.
call keccakf1600_avx2x4_ll.
admit.
qed.

