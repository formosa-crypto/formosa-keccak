(******************************************************************************
   Keccak1600_Spec.ec:

   Properties of the Keccak1600 specification.

    - functionol (bit-oriented) specification
    - correctness wrt imperative spec [FIPS202_SHA3.ec]

******************************************************************************)
require import AllCore List Int IntDiv.

require export FIPS202_SHA3.

require import Keccakf1600_Spec.

import EclibExtra JWordList.



require StdOrder.
import StdOrder.IntOrder.

require BitEncoding.
import BitEncoding.BitChunking.


(** Auxiliary defs *)

lemma size_state2bits s:
 size (state2bits s) = 1600.
proof.
by rewrite /state2bits size_w64L_to_bits size_to_list /#.
qed.

lemma bits2state_cat l1 l2:
 bits2state (l1++l2)
 = addstate (bits2state l1)
            (bits2state (nseq (size l1) false ++ l2)).
proof.
apply Array25.ext_eq => i Hi.
rewrite map2iE // !get_of_list //.
rewrite !nth_w64L_from_bits 1..3:/#.
apply W64.wordP => k Hk.
rewrite xorE map2iE // !get_bits2w //.
rewrite !nth_take 1..6:/# !nth_drop 1..6:/#.
rewrite !nth_cat size_nseq ler_maxr; 1:smt(size_ge0).
case: (64*i+k < size l1) => C.
 by rewrite nth_nseq /#.
by rewrite (nth_out _ l1) /#.
qed.

lemma addstateA (s1 s2 s3: state):
 addstate s1 (addstate s2 s3) = addstate (addstate s1 s2) s3.
proof.
rewrite /addstate; apply ext_eq => i Hi.
by rewrite !map2iE // W64.WRing.AddMonoid.addmA. 
qed.


(**************************************************************
    Functional Bit-oriented specification of KECCAK1600
***************************************************************)

lemma pad10star1P r m:
 0 < r =>
 r %| size (m ++ pad10star1 r (size m)).
proof.
move=> Hr; rewrite dvdzE size_cat /pad10star1 /= size_rcons size_nseq.
by rewrite ler_maxr 1:/# (addzC 1) /= -(addzC 2) addzA modzDmr /#.
qed.

lemma size_pad10star1 r len:
 0 < r =>
 0 <= len %% r <= r-2 =>
 size (pad10star1 r len)
 = r - (len %% r).
proof.
move=> Hr Hlen.
rewrite /pad10star1 /= size_rcons size_nseq lez_maxr 1:/#.
by rewrite -modzDml -modzNm -modzDl /#.
qed.

abbrev split_padded r m =
 chunk r (m ++ pad10star1 r (size m)).

op keccak1600_absorb_op (r: int, m: bits): state =
 foldl
  (fun s b => keccak_f1600_op (addstate s b))
  st0
  (map bits2state (split_padded r m)).

(** Iterates [KECCAK_F1600] on [st] *)
op st_i st i = iter i keccak_f1600_op st.

op keccak1600_squeeze_op (r: int, st: state, outlen: int): bits =
 take outlen 
      (flatten
        (List.map (take r \o state2bits \o st_i st)
                  (iota_ 0 ((outlen-1) %/ r + 1)))).

op keccak1600_sponge_op (r: int, m: bits, outlen: int): bits =
 keccak1600_squeeze_op r (keccak1600_absorb_op r m) outlen.

op keccak1600_op (c: int, m:bits, outlen: int): bits =
 keccak1600_sponge_op (1600-c) m outlen.

op SHA_DS_BITS = [false; true].
op SHAKE_DS_BITS = [true; true; true; true].
op RAWSHAKE_DS_BITS = [true; true].

op sha3_224_op (m: bits): bits =
 keccak1600_op 448 (m++SHA_DS_BITS) 224.
op sha3_256_op (m: bits): bits =
 keccak1600_op 512 (m++SHA_DS_BITS) 256.
op sha3_384_op (m: bits): bits =
 keccak1600_op 768 (m++SHA_DS_BITS) 384.
op sha3_512_op (m: bits): bits =
 keccak1600_op 1024 (m++SHA_DS_BITS) 512.
op shake128_op (m: bits, outlen:int): bits =
 keccak1600_op 256 (m++SHAKE_DS_BITS) outlen.
op shake256_op (m: bits, outlen:int): bits =
 keccak1600_op 512 (m++SHAKE_DS_BITS) outlen.
op rawshake128_op (m: bits, outlen:int): bits =
 keccak1600_op 256 (m++RAWSHAKE_DS_BITS) outlen.
op rawshake256_op (m: bits, outlen:int): bits =
 keccak1600_op 512 (m++RAWSHAKE_DS_BITS) outlen.

(** A more convenient version of the sponge construction *)
module SpongeBits = {
  proc absorb(r: int, m: bits): state = {
    var p, pl, n, s, i;
    
    p <- pad10star1 r (size m);
    p <- m ++ p;
    pl <- chunk r p;
    n <- size p %/ r;
    s <- st0;
    i <- 0;
    while (i < n){
      s <- addstate s (bits2state (nth [] pl i));
      s <- keccak_f1600_op(s);
      i <- i + 1;
    }
    return s;
  }
  proc squeeze(r: int, s: state, d: int) = {
    var z, i;
    z <- take r (state2bits s);
    i <- 1;
    while (r*i < d){
      s <- keccak_f1600_op(s);
      z <- z ++ take r (state2bits s);
      i <- i + 1;
    }
    
    return take d z;
  }
  proc sponge(r:int, m: bits, d: int): bits = {
    var s, o;
    s <@ absorb(r, m);
    o <@ squeeze(r, s, d);
    return o;
  }
}.

equiv keccak1600_sponge_eq:
 Sponge1600(Keccakf1600_Params).sponge ~ SpongeBits.sponge
 : ={r, m, d} /\ 0 <= r{2} <= 1600 ==> ={res}.
proof.
proc; inline absorb squeeze; simplify.
wp; while (#pre /\ (z,s){1}=(z,s1){2} /\ (d0=d /\ r1=r /\ r*i0=size z){2}).
 wp; ecall{1} (keccak_f1600_ph s{1}); auto => /> &1 &2 *.
 by rewrite size_cat size_take' 1:/# !size_state2bits /#. 
wp.
while (#pre /\ (pl,n,i,s){1}=(pl,n,i,s0){2}).
 by wp; ecall{1} (keccak_f1600_ph s{1}); auto => /> &1 &2 *.
inline*; auto => /> &m *.
by rewrite size_take' 1:/# size_state2bits /#.
qed.

phoare keccak1600_absorb_ll: 
 [ SpongeBits.absorb
 : 0 < r <= 1600 ==> true
 ] = 1%r.
proof.
proc; wp; while (0<=i) (n-i).
 by move=> z; auto => /> &m * /#.
by auto => /> &m ??i /#.
qed.

phoare keccak1600_squeeze_ll: 
 [ SpongeBits.squeeze
 : 0 < r <= 1600 ==> true
 ] = 1%r.
proof.
proc; wp; while (0<r /\ 0<=i) (d-r*i).
 by move=> z; auto => /> &m * /#.
by auto => /> &m ??i /#.
qed.

phoare keccak1600_sponge_ll: 
 [ SpongeBits.sponge
 : 0 < r <= 1600 ==> true
 ] = 1%r.
proof.
proc; call keccak1600_squeeze_ll.
by call keccak1600_absorb_ll.
qed.

phoare keccak1600_ll: 
 [ Keccak1600.keccak1600
 : 0 <= c < 1600 ==> true
 ] = 1%r.
proof.
proc; simplify.
call (: 0 < r && r <= 1600 ==> true).
 conseq keccak1600_sponge_eq keccak1600_sponge_ll => /> &m *.
 by exists (r{m},m{m},d{m}) => /> /#.
by auto => /> /#.
qed.

hoare keccak1600_absorb_h _r _m:
 SpongeBits.absorb
 : r=_r /\ m=_m /\ 0<_r<=1600 ==> res = keccak1600_absorb_op _r _m.
proof.
proc; simplify.
while (#pre /\ pl=split_padded r m /\ n=size pl /\ 0<=i<=n /\
       keccak1600_absorb_op r m
       = foldl (fun s b => keccak_f1600_op (addstate s b)) s (drop i (map bits2state pl))).
 auto => /> &m ????H?; split; 1:smt().
 rewrite H (foldl_dropS st0) /=.
  by rewrite size_map /#.
 congr; congr; congr.
 by rewrite (nth_map []) 1:/#.
auto => /> *; rewrite size_chunk 1:/#.
split; 1:smt(drop0 size_ge0).
move=> i s ?_?? ->; have ->: i=size (split_padded _r _m).
 by rewrite size_chunk /#.
by rewrite drop_oversize // size_map.
qed.

phoare keccak1600_absorb_ph _r _m:
 [ SpongeBits.absorb
 : r=_r /\ m=_m /\ 0<_r<=1600 ==> res = keccak1600_absorb_op _r _m
 ] = 1%r.
proof. by conseq keccak1600_absorb_ll (keccak1600_absorb_h _r _m). qed.

hoare keccak1600_squeeze_h _r _s _d:
 SpongeBits.squeeze
 : r=_r /\ s=_s /\ d=_d /\ 0<_r<=1600
 ==> res = keccak1600_squeeze_op _r _s _d.
proof.
proc; simplify.
case: (d <= 0).
 while (d=_d).
  by auto => />.
 by auto => /> *; rewrite /keccak1600_squeeze_op !take_le0 //.
while (r=_r /\ d=_d /\ 0<_r<=1600 /\ 1<=i /\ r*i=size z /\ r*(i-1) < d /\
       s = st_i _s (i-1) /\
       z = flatten (map (take r \o state2bits \o st_i _s) (iota_ 0 i))).
 auto => /> &m ???H??; rewrite !size_cat.
 rewrite !size_take' 1:/#.
 rewrite ifT.
  rewrite size_state2bits /#.
 split; 1:smt().
 split; 1:smt().
 split.
  by rewrite {-1}(:i{m}=i{m}-1+1) 1:/# /st_i iterS 1:/# //.
 rewrite iotaSr 1:/# map_rcons flatten_rcons; congr.
 rewrite /(\o) /=; congr; congr.
 by rewrite /st_i -iterS /#.
auto => /> ???; split.
 rewrite size_take' 1:/# size_state2bits ifT 1:/# /st_i iter0 1:/# => />.
 by rewrite -iotaredE /(\o) /flatten /= iter0 1:/# cats0 /#.
move=> i *; rewrite /keccak1600_sponge_op /keccak1600_squeeze_op.
by congr; congr; congr; congr; smt().
qed.

phoare keccak1600_squeeze_ph _r _s _d:
 [ SpongeBits.squeeze
 : r=_r /\ s=_s /\ d=_d /\ 0<_r<=1600
 ==> res = keccak1600_squeeze_op _r _s _d
 ] = 1%r.
proof. by conseq keccak1600_squeeze_ll (keccak1600_squeeze_h _r _s _d). qed.

(** Standard spec. vs Functional spec. *)
hoare keccak1600_h _c _m _outlen:
 Keccak1600.keccak1600
 : c = _c /\ m = _m /\ outlen = _outlen
   /\ 0 <= _c < 1600
 ==> res = keccak1600_sponge_op (1600-_c) _m _outlen.
proof.
bypr => /> &m' *.
have ->: Pr[Keccak1600.keccak1600(c{m'}, m{m'}, outlen{m'}) @ &m' : res <> keccak1600_sponge_op (1600-c{m'}) m{m'} outlen{m'}] = Pr[SpongeBits.sponge(1600-c{m'}, m{m'}, outlen{m'}) @ &m' : res <> keccak1600_sponge_op (1600-c{m'}) m{m'} outlen{m'}]. 
 byequiv => //.
 proc*; inline keccak1600.
 by wp; call keccak1600_sponge_eq; auto => /> /#.
byphoare (: r=1600-c{m'} /\ m=m{m'} /\ d=outlen{m'} ==> _) => //; hoare; simplify.
proc; inline sponge; simplify.
ecall (keccak1600_squeeze_h r s d).
ecall (keccak1600_absorb_h r m).
by auto => /> /#.
qed.

phoare keccak1600_ph _c _m _outlen:
 [ Keccak1600.keccak1600
 : c = _c /\ m = _m /\ outlen = _outlen
   /\ 0 < _c < 1600
 ==> res = keccak1600_sponge_op (1600-_c) _m _outlen
 ] = 1%r.
proof.
by conseq keccak1600_ll (keccak1600_h _c _m _outlen) => /> /#.
qed.

hoare sha3_224_h _m:
 Keccak1600.sha3_224
 : m = _m ==> res = sha3_224_op _m.
proof.
proc.
by call (keccak1600_h 448 (_m ++ [false; true]) 224).
qed.

phoare sha3_224_ph _m:
 [ Keccak1600.sha3_224
 : m = _m ==> res = sha3_224_op _m
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_224 by proc; call keccak1600_ll.
by conseq Hll (sha3_224_h _m).
qed.

hoare sha3_256_h _m:
 Keccak1600.sha3_256
 : m = _m ==> res = sha3_256_op _m.
proof.
proc.
by call (keccak1600_h 512 (_m ++ [false; true]) 256).
qed.

phoare sha3_256_ph _m:
 [ Keccak1600.sha3_256
 : m = _m ==> res = sha3_256_op _m
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_256 by proc; call keccak1600_ll.
by conseq Hll (sha3_256_h _m).
qed.

hoare sha3_384_h _m:
 Keccak1600.sha3_384
 : m = _m ==> res = sha3_384_op _m.
proof.
proc.
by call (keccak1600_h 768 (_m ++ [false; true]) 384).
qed.

phoare sha3_384_ph _m:
 [ Keccak1600.sha3_384
 : m = _m ==> res = sha3_384_op _m
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_384 by proc; call keccak1600_ll.
by conseq Hll (sha3_384_h _m).
qed.

hoare sha3_512_h _m:
 Keccak1600.sha3_512
 : m = _m ==> res = sha3_512_op _m.
proof.
proc.
by call (keccak1600_h 1024 (_m ++ [false; true]) 512).
qed.

phoare sha3_512_ph _m:
 [ Keccak1600.sha3_512
 : m = _m ==> res = sha3_512_op _m
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_512 by proc; call keccak1600_ll.
by conseq Hll (sha3_512_h _m).
qed.

hoare shake128_h _m _d:
 Keccak1600.shake128
 : m = _m /\ d = _d ==> res = shake128_op _m _d.
proof.
proc.
by call (keccak1600_h 256 (_m ++ [true; true; true; true]) _d).
qed.

phoare shake128_ph _m _d:
 [ Keccak1600.shake128
 : m = _m /\ d = _d ==> res = shake128_op _m _d
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.shake128 by proc; call keccak1600_ll.
by conseq Hll (shake128_h _m _d).
qed.

hoare shake256_h _m _d:
 Keccak1600.shake256
 : m = _m /\ d = _d ==> res = shake256_op _m _d.
proof.
proc.
by call (keccak1600_h 512 (_m ++ [true; true; true; true]) _d).
qed.

phoare shake256_ph _m _d:
 [ Keccak1600.shake256
 : m = _m /\ d = _d ==> res = shake256_op _m _d
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.shake256 by proc; call keccak1600_ll.
by conseq Hll (shake256_h _m _d).
qed.

hoare rawshake128_h _m _d:
 Keccak1600.rawSHAKE128
 : m = _m /\ d = _d ==> res = rawshake128_op _m _d.
proof.
proc.
by call (keccak1600_h 256 (_m ++ [true; true]) _d).
qed.

phoare rawshake128_ph _m _d:
 [ Keccak1600.rawSHAKE128
 : m = _m /\ d = _d ==> res = rawshake128_op _m _d
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.rawSHAKE128 by proc; call keccak1600_ll.
by conseq Hll (rawshake128_h _m _d).
qed.

hoare rawshake256_h _m _d:
 Keccak1600.rawSHAKE256
 : m = _m /\ d = _d ==> res = rawshake256_op _m _d.
proof.
proc.
by call (keccak1600_h 512 (_m ++ [true; true]) _d).
qed.

phoare rawshake256_ph _m _d:
 [ Keccak1600.rawSHAKE256
 : m = _m /\ d = _d ==> res = rawshake256_op _m _d
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.rawSHAKE256 by proc; call keccak1600_ll.
by conseq Hll (rawshake256_h _m _d).
qed.

