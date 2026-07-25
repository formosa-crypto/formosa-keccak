require import AllCore List Int IntDiv.

from Jasmin require import JModel_x86.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

require import Keccakf1600_ref.
require import Keccak1600_ref.
require import Keccak1600_avx2x4.

require import Keccak_bindings.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array1 Array100 WArray200 WArray800.

require import Avx2_extra.


op regs_fetch (st: W256.t Array25.t) =
 (st.[7], st.[8], st.[11], st.[12], st.[15], st.[18], st.[21], st.[22], st.[24]).

op regs_unfetch (st: W256.t Array25.t) (regs: _*_*_*_*_*_*_*_*_) =
 st.[7<-regs.`1].[8<-regs.`2].[11<-regs.`3].[12<-regs.`4].[15<-regs.`5]
   .[18<-regs.`6].[21<-regs.`7].[22<-regs.`8].[24<-regs.`9].

lemma regs_unfetchK st regs: regs_fetch (regs_unfetch st regs) = regs
by circuit.

lemma regs_fetch_iota st rc: regs_fetch (st4x_keccak_iota rc st) = regs_fetch st
by circuit.

lemma regs_fetchK st:
 regs_unfetch st (regs_fetch st) = st
by circuit.

hoare regs_unfetch_h _st (_regs:_*_*_*_*_*_*_*_*_):
 M.__regs_unfetch
 : st=_st /\ y10=_regs.`1 /\ y14=_regs.`2 /\ y8=_regs.`3 /\ y15=_regs.`4 /\
   y9=_regs.`5 /\ y13=_regs.`6 /\ y3=_regs.`7 /\ y7=_regs.`8 /\ y2=_regs.`9
 ==> res=regs_unfetch _st _regs
by proc; circuit.

hoare regs_fetch_h _st:
 M.__regs_fetch : st=_st ==> res=regs_fetch _st
by proc; circuit.

hoare loopbody_nat_h _st _regs _i _rc:
 M.__f1600_loopbody_native
 : st=_st /\ (y10,y14,y8,y15,y9,y13,y3,y7,y2)=_regs /\ rol8=rOL8 /\ rol56=rOL56 /\ rC.[i]=_rc /\ i=_i 
  /\ 0 <= _i < 24
 ==> regs_unfetch res.`1 (res.`2,res.`3,res.`4,res.`5,res.`6,res.`7,res.`8,res.`9,res.`10)
     = st4x_map (keccak_round_op _rc) (regs_unfetch _st _regs).
proof.
proc; simplify.
do 24! cfold 1.
wp 220.
proc change 72: {y15 <- VPBROADCAST_4u64 (_rc); }.
 by auto => /> &m; rewrite of_uintK /= /#.
conseq (: st = _st /\ (y10,y14,y8,y15,y9,y13,y3,y7,y2)=_regs /\  rol8 = rOL8 /\  rol56 = rOL56 
  /\ (y10,y14,y8,y15,y9,y13,y3,y7,y2)=_regs
  ==> _); first done.
by circuit.
qed.

lemma f1600_loopbody_nat_ll: islossless M.__f1600_loopbody_native
by islossless.

hoare __keccakf1600_avx2x4_nat_h _a:
 M.__keccakf1600_avx2x4_nat :
 st = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof.
proc.
ecall (regs_unfetch_h st (y10, y14, y8, y15, y9, y13, y3, y7, y2)).
while (0 <= i <= 24 /\
       rc = rc_spec /\
       rol8 = rOL8 /\
       rol56 = rOL56 /\
       regs_unfetch st (y10, y14, y8, y15, y9, y13, y3, y7, y2) = st4x_map (keccak_round_i i) _a).
 wp; ecall (loopbody_nat_h st (y10, y14, y8, y15, y9, y13, y3, y7, y2) i rc_spec.[i]).
 auto => &m /> Hi1 _ H Hi2 [st y10 y14 y8 y15 y9 y13 y3 y7 y2] /= ->; split; first smt().
 rewrite /keccak_round_op iotaSr 1:/# /= H st4x_map_comp; congr.
 rewrite fun_ext => a /=.
 rewrite foldl_rcons /= /#.
wp; ecall (loopbody_nat_h st (y10, y14, y8, y15, y9, y13, y3, y7, y2) i rc_spec.[i]).
wp; ecall (regs_fetch_h st).
auto => |> ? [st0 r00 r01 r02 r03 r04 r05 r06 r07 r08] /= ->; split.
 rewrite /keccak_round_op iota1 /=; congr. 
 by rewrite eq_sym -{1}(regs_fetchK _a); congr; smt().
move=> i st1 r10 r11 r12 r13 r14 r15 r16 r17 r18 /= ???.
have ->: i=24 by smt().
by move=> _ ->; smt().
qed.

lemma __keccakf1600_avx2x4_nat_ll: islossless M.__keccakf1600_avx2x4_nat.
proof.
proc.
inline __regs_unfetch __regs_fetch.
wp; while (true) (24-i).
 move=> z.
 wp; call f1600_loopbody_nat_ll.
 by auto => /> &m ? /#.
wp; call f1600_loopbody_nat_ll.
by inline*; auto => /#.
qed.

phoare __keccakf1600_avx2x4_nat_ph _a:
 [ M.__keccakf1600_avx2x4_nat
 : st = _a
 ==> res = st4x_map keccak_f1600_op _a
 ] = 1%r.
proof. 
by conseq __keccakf1600_avx2x4_nat_ll (__keccakf1600_avx2x4_nat_h _a).
qed.

hoare keccakf1600_avx2x4_nat_h _a:
 M._keccakf1600_avx2x4_nat :
 st = _a
 ==> res = st4x_map keccak_f1600_op _a.
proof. by proc; ecall (__keccakf1600_avx2x4_nat_h st). qed.

lemma keccakf1600_avx2x4_nat_ll: islossless M._keccakf1600_avx2x4_nat.
proof. by proc; call __keccakf1600_avx2x4_nat_ll. qed.
