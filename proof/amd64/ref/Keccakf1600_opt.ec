(******************************************************************************
   Keccakf1600_opt.ec:

   Correctness proof for the Keccak OPT implementation
******************************************************************************)
require import List Real Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_Keccakf1600 Keccakf1600_Spec.

from JazzEC require import Keccak1600_Jazz.
from JazzEC require import Array5 Array24 Array25.

require import Keccak_bindings.

op read_regs (st: W64.t Array25.t) =
 (st.[0],st.[10],st.[12],st.[18],st.[19],st.[20],st.[21],st.[22],st.[24]).

hoare read_regs_opt_h _a:
 M.read_regs_opt
 : a=_a ==> res = read_regs _a
by proc; circuit.

op store_regs st (x:_*_*_*_*_*_*_*_*_): W64.t Array25.t =
 st.[0<-x.`1].[10<-x.`2].[12<-x.`3].[18<-x.`4].[19<-x.`5].[20<-x.`6].[21<-x.`7].[22<-x.`8].[24<-x.`9].

hoare store_regs_opt_h _a _regs:
 M.store_regs_opt
 : a=_a /\ (rbp, rdi, r13, r10, r11, r8, rsi, r15, rbx)=_regs
 ==> res = store_regs _a _regs
by proc; circuit.

lemma read_regsK st:
 store_regs st (read_regs st) = st
by circuit.

lemma store_regsK st regs:
 read_regs (store_regs st regs) = regs
by circuit.

lemma store_regsI st regs1 regs2:
 store_regs (store_regs st regs1) regs2 = store_regs st regs2
by circuit.


op keccak_dround_opt rc1 rc2 (Aregs:_*_): W64.t Array25.t =
 keccak_round_op rc2 (keccak_round_op rc1 (store_regs Aregs.`1 Aregs.`2)).


lemma keccak_dround_optE i st:
 keccak_dround_opt rc_spec.[i] rc_spec.[i+1] (st,read_regs st) =
 keccak_round_op rc_spec.[i+1] (keccak_round_op rc_spec.[i] st).
proof. by rewrite /keccak_dround_opt /= read_regsK. qed.

from JazzEC require import Array1.

lemma keccakf1600_dround_opt_ll: islossless  M.keccakf1600_opt_loop_body
by islossless.

bind array Array1."_.[_]" Array1."_.[_<-_]" Array1.to_list Array1.of_list Array1.t 1.
realize tolistP by done.
realize get_setP by smt(Array1.get_setE). 
realize eqP by smt(Array1.tP).
realize get_out by smt(Array1.get_out).
realize gt0_size by done.
realize oflistP by smt(Array1.get_of_list).

op init_1_64 = Array1.init <:W64.t>.

bind op [W64.t & Array1.t] init_1_64 "ainit".
realize bvainitP.
proof.
rewrite /init_1_64 => f.
rewrite BVA_Top_Array1_Array1_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array1.initE).
qed.

(*pragma +Circuit:timing.*)

lemma keccakf1600_dround_opt_h rc1 rc2 (xx:_*(_*_*_*_*_*_*_*_*_)) c:
 rc1 = rc_spec.[to_uint c] => rc2 = rc_spec.[to_uint c + 1] =>
 hoare [ 
 M.keccakf1600_opt_loop_body
 : rax=c /\ 0 <= to_uint c < 24 /\
   rbp=xx.`2.`1 /\
   rdi=xx.`2.`2 /\
   r13=xx.`2.`3 /\
   r10=xx.`2.`4 /\
   r11=xx.`2.`5 /\
    r8=xx.`2.`6 /\
   rsi=xx.`2.`7 /\
   r15=xx.`2.`8 /\
   rbx=xx.`2.`9 /\
     a=xx.`1
 ==> res.`1 = c + (W64.of_int 2)
     /\ store_regs res.`11 (res.`2,res.`3,res.`4,res.`5,res.`6,res.`7,res.`8,res.`9,res.`10)
        = keccak_dround_opt rc1 rc2 xx
 ].
proof.
move => Erc1 Erc2.
proc; simplify.
swap 4 -2.
swap 68 -66.
cfold 69.
alias 252 with rC2.
swap 252 -249.
cfold 252; cfold 252.
seq 4: (#pre /\ rC=rc_spec /\ rC2=rc_spec /\ cnt=c); first by auto => />.
proc change 66: { r12 <- r12 `^` rc1; }; first by auto => /> /#.
proc change 248: { rbp <- rbp `^` rc2; }; first by auto => |> &2 *; rewrite to_uintD_small /#.
by circuit.
qed.

lemma keccakf1600_dround_opt_ph rc1 rc2 (xx:_*(_*_*_*_*_*_*_*_*_)) c:
 rc1 = rc_spec.[to_uint c] => rc2 = rc_spec.[to_uint c + 1] =>
 phoare [ 
 M.keccakf1600_opt_loop_body
 : rax=c /\ 0 <= to_uint c < 24 /\
   rbp=xx.`2.`1 /\
   rdi=xx.`2.`2 /\
   r13=xx.`2.`3 /\
   r10=xx.`2.`4 /\
   r11=xx.`2.`5 /\
    r8=xx.`2.`6 /\
   rsi=xx.`2.`7 /\
   r15=xx.`2.`8 /\
   rbx=xx.`2.`9 /\
     a=xx.`1
 ==> res.`1 = c + (W64.of_int 2)
     /\ store_regs res.`11 (res.`2,res.`3,res.`4,res.`5,res.`6,res.`7,res.`8,res.`9,res.`10)
        = keccak_dround_opt rc1 rc2 xx
 ] = 1%r.
proof. 
move=> H1 H2.
by conseq keccakf1600_dround_opt_ll (keccakf1600_dround_opt_h rc1 rc2 xx c H1 H2).
qed.

lemma keccak_dround_optP a regs c:
 0 <= c <= 22 =>
 foldl
  (fun st i => keccak_round_op rc_spec.[i] st)
  (store_regs a regs)
  (range c 24) =
 foldl
  (fun st i => keccak_round_op rc_spec.[i] st)
  (keccak_dround_opt rc_spec.[c] rc_spec.[c + 1] (a,regs))
  (range (c+2) 24).
proof.
move=> Hc; rewrite (range_cat (c+2)) 1..2:/# foldl_cat.
have ->/=: range c (c+2) = [c; c+1].
 by rewrite (:2=1+1) 1:/# addzA rangeSr 1:/# rangeSr 1:/# range_geq 1:/# -!cats1 /=.
rewrite -keccak_dround_optE store_regsK.
by congr; rewrite /keccak_dround_opt /= store_regsI.
qed.

hoare __keccakf1600_opt_h _a:
 M.__keccakf1600_opt :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc.
ecall (store_regs_opt_h a (rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) => /=.
while (2 <= to_uint rax <= 24 /\ 2 %| to_uint rax /\
       keccak_f1600_op _a =
       foldl (fun s i => keccak_round_op rc_spec.[i] s) (store_regs a (rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) (range (to_uint rax) 24)).
 wp; ecall (keccakf1600_dround_opt_h rc_spec.[to_uint rax] rc_spec.[to_uint rax+1] (a,(rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) rax); last 2 smt().
 auto => /> &m Hc1 _ Hc_2 IH; rewrite ultE of_uintK /= => Hc2; split; first smt().
 move => _ _ [rax rbp rdi r13 r10 r11 r8 rsi r15 rbx a e] /=.
 rewrite to_uint_eq to_uintD_small of_uintK 1:/# /= => Erax H.
 split; first smt().
 split; first smt().
 by rewrite H IH Erax keccak_dround_optP /#.
ecall (keccakf1600_dround_opt_h rc_spec.[to_uint rax] rc_spec.[to_uint rax+1] (a,(rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) rax); last 2 smt().
wp; ecall (read_regs_opt_h a); auto => />.
move=> [rax rbp rdi r13 r10 r11 r8 rsi r15 rbx a e] /= -> H; split.
 rewrite of_uintK; split; first smt().
 split; first smt().
 rewrite H /keccak_dround_opt /= /keccak_f1600_op /range -iotaredE /=.
 do 24! congr.
 by clear; circuit.
move => ra ?????c????.
rewrite ultE of_uintK /= => ????; have ->: to_uint c=24 by smt().
rewrite range_geq 1:/# /= /#.
qed.

lemma __keccakf1600_opt_ll: islossless M.__keccakf1600_opt.
proof.
proc.
inline store_regs_opt read_regs_opt.
wp; while true (24 - to_uint rax).
 move=> z.
 wp; ecall (keccakf1600_dround_opt_ph rc_spec.[to_uint rax] rc_spec.[to_uint rax+1] (a,(rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) rax); last 2 smt().
 auto => /> &m; rewrite ultE of_uintK /= => /> *. 
 split; first smt(W64.to_uint_cmp).
 move => _ [rax rbp rdi r13 r10 r11 r8 rsi r15 rbx a e] /=.
 by rewrite to_uint_eq to_uintD_small of_uintK /= 1:/# => -> _ /#.
ecall (keccakf1600_dround_opt_ph rc_spec.[to_uint rax] rc_spec.[to_uint rax+1] (a,(rbp,rdi,r13,r10,r11,r8,rsi,r15,rbx)) rax); last 2 smt().
auto => /> &m [rax rbp rdi r13 r10 r11 r8 rsi r15 rbx a e] /=.
by rewrite to_uint_eq of_uintK /= => ? _ c; rewrite ultE of_uintK /= /#.
qed.

phoare __keccakf1600_opt_ph _a:
 [ M.__keccakf1600_opt
 : a = _a
 ==> res = keccak_f1600_op _a
 ] = 1%r.
proof. by conseq __keccakf1600_opt_ll (__keccakf1600_opt_h _a). qed.

lemma keccakf1600_opt_ll: islossless M._keccakf1600_opt.
proof.
proc; inline _keccakf1600_opt.
by call __keccakf1600_opt_ll.
qed.

hoare keccakf1600_opt_h _a:
 M._keccakf1600_opt :
  a = _a ==> res = keccak_f1600_op _a.
proof.
proc; inline _keccakf1600_opt.
by call (__keccakf1600_opt_h _a).
qed.
