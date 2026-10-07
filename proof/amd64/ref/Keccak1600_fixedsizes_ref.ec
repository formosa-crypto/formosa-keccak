(******************************************************************************
   Keccak1600_fixedsizes_ref.ec:

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
require import Keccakf1600.
require import Keccak1600_statebytes.
require import Keccak1600_subreadwrite.

require import StdOrder.
import IntOrder.

require import BitEncoding.
import BitEncoding.BitChunking.


(*
   ONE-SHOT (FIXED-SIZE) MEMORY ABSORB
   ===================================
*)

lemma addstate_m_ll: islossless M.__addstate_m.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc.
swap 1 1.
seq 1: true => />; 1:auto; 1:islossless; last by hoare; auto.
seq 1: #pre => //; first inline*; auto.
if => //.
 seq 3: true => />; 1,4:auto; 2: islossless.
 while true (_LEN %/ 32 - i).
  by move=> z; auto; smt().
 by auto; smt().
seq 2: true => />; 1,4:auto; 2: islossless.
while true (aT + _LEN %/ 8 *8 - at).
 by move=> z; auto; smt().
by auto => /> /#.
qed.


hoare addstate_m_h _mem _st _at _buf _len _tb:
 M.__addstate_m
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 /\ 0 <= _tb < 256
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
     in Glob.mem=_mem
        /\ res.`1 = addstate_at _st _at l
        /\ res.`2 = _at + _len + b2i (_tb<>0)
        /\ res.`3 = _buf + _len.
proof.
(* On the shared read-step layer (input `memread _mem _buf _len`, cursor `buf`):
   the alignment prefix and the final word are addstate_msubread_u64 /
   addstate_spec_finish steps, every plain load is one addstate_spec_fullword
   step.  The array addstate_h has the same structure. *)
proc; simplify.
(* stmts 1-2 : __HAS_FEATURE (hAS_AVX2 kept symbolic) + the alignment prefix. *)
pose base:= 8 * (_at %/ 8).
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
seq 2: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb nbase _buf buf st aT _LEN _TRAILB).
+ seq 1: (#pre); first by inline*; auto.
  if => //.
   wp; ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB aT8 aT); auto => |> &m ???????.
   move=> [buf0 len0 tb0 at0 w0] /=.
   move => H; rewrite set64_addstate_at 1:/#.
(* prefix word = one step from the initial spec at base; nbase = base + 8
   since _at is not 8-aligned in this branch. *)
   apply (addstate_msubread_u64 _mem w0 (8 * (_at %/ 8)) _st _at _buf _len _tb _st _at _buf _len _tb nbase at0 buf0 len0 tb0) => //;
    [smt() | by rewrite /nbase; smt() | by apply addstate_spec_init => //; smt(size_memread)].
  auto => |> *.
  have ->@/base: nbase = base by smt().
  by apply addstate_spec_init; smt(size_memread).
(* stmt 3 : if hAS_AVX2 — both branches consume `8*(_LEN%/8)` further aligned bytes. *)
seq 1: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+8*(_LEN%/8)) _buf buf st (aT+8*(_LEN%/8)) (_LEN-8*(_LEN%/8)) _TRAILB /\ 0 <= _LEN).
 if => //.
 - seq 3: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+32*(_LEN%/32)) _buf buf st (aT+32*(_LEN%/32)) (_LEN-32*(_LEN%/32)) _TRAILB /\ 0 <= _LEN).
   while (#[/1:8]pre /\ inc = _LEN%/32 /\
          0 <= i <= _LEN%/32 /\ 
          addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+32*i) _buf buf st (aT+32*i) (_LEN-32*i) _TRAILB).
    auto => |> &m ????????? IH Hb; split; first smt().
    rewrite xorwC set256_addstate_at 1:/#.
    (* u256 step: one shared full-word step. *)
    apply (addstate_spec_fullword _ _ (nbase + 32 * i{m}) _st _at _tb st{m} _buf buf{m} (aT{m} + 32 * i{m}) (_LEN{m} - 32 * i{m}) _TRAILB{m}) => //; rewrite ?size_to_list; 1..5: smt().
    by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) //; apply loadW256_memread; smt().
   auto => |> &m ??????? H ?; split. 
have ?: 0<= _LEN{m}.
 move: H; rewrite /addstate_spec => />. smt(size_ge0).
    smt().
   move => buf1 i st1 ???; have ->: i=_LEN{m} %/ 32 by smt().
   by move=> Hs; split => //; smt().
   seq 1: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ addstate_spec _st _at (memread _mem _buf _len) _tb (nbase+16*(_LEN%/16)) _buf buf st (aT+16*(_LEN%/16)) (_LEN-16*(_LEN%/16)) _TRAILB /\ 0 <= _LEN).
   if => //.
     auto => |> &m ??????? IH HL Hb.
     (* u128 16-tail step: one shared full-word step. *)
     rewrite xorwC set128_addstate_at 1:/# (_: aT{m} + _LEN{m} %/ 32 * 32 = aT{m} + 32 * (_LEN{m} %/ 32)) 1:/#.
     apply (addstate_spec_fullword _ _ (nbase + 32 * (_LEN{m} %/ 32)) _st _at _tb st{m} _buf buf{m} (aT{m} + 32 * (_LEN{m} %/ 32)) (_LEN{m} - 32 * (_LEN{m} %/ 32)) _TRAILB{m}) => //; rewrite ?size_to_list; 1..5: smt().
     by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ IH) //; apply loadW128_memread; smt().
    auto => |> ??????? H Hb HL.
    (* 16-tail skipped: 16*(_LEN%/16) = 32*(_LEN%/32) when _LEN%%32 < 16. *)
    move => Hc; have E: forall n, !16 <= n %% 32 => 16 * (n %/ 16) = 32 * (n %/ 32) by smt().
    by rewrite !(E _ Hc); exact Hb.
   if => //.
     (* u64 8-tail step: one shared full-word step. *)
     auto => |> &m ??????? H HL Hb.
     rewrite set64_addstate_at 1:/# (_: aT{m} + _LEN{m} %/ 16 * 16 = aT{m} + 16 * (_LEN{m} %/ 16)) 1:/#.
     have Hs: size (u64bytes (loadW64 _mem buf{m})) = 8 by rewrite /u64bytes size_to_list.
     apply (addstate_spec_fullword _ _ (nbase + 16 * (_LEN{m} %/ 16)) _st _at _tb st{m} _buf buf{m} (aT{m} + 16 * (_LEN{m} %/ 16)) (_LEN{m} - 16 * (_LEN{m} %/ 16)) _TRAILB{m}) => //; rewrite ?Hs; 1..5: smt().
     by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ H) //; apply loadW64_memread; smt().
    auto => |> ???????? H HL Hb.
    (* 8-tail skipped: 8*(_LEN%/8) = 16*(_LEN%/16) when _LEN%%16 < 8. *)
    have E: forall n, !8 <= n %% 16 => 8 * (n %/ 8) = 16 * (n %/ 16) by smt().
    by rewrite !(E _ Hb); exact H.
 - (* scalar branch: invariant = spec advanced by the (at - aT) bytes consumed. *)
   while (#[/1:8]pre /\ 0 <= _LEN /\ aT <= at <= aT + _LEN %/ 8 * 8 /\ (at - aT) %% 8 = 0 /\
           addstate_spec _st _at (memread _mem _buf _len) _tb (nbase + (at - aT)) _buf buf st at (_LEN - (at - aT)) _TRAILB).
   + auto => |> &m ??????? HL H1 H2 Hm H Hb.
     split; first smt().
     split; first smt().
     (* u64 scalar step: one shared full-word step. *)
     rewrite set64_addstate_at 1:/#.
     have Hs: size (u64bytes (loadW64 _mem buf{m})) = 8 by rewrite /u64bytes size_to_list.
     apply (addstate_spec_fullword _ _ (nbase + (at{m} - aT{m})) _st _at _tb st{m} _buf buf{m} at{m} (_LEN{m} - (at{m} - aT{m})) _TRAILB{m}) => //; rewrite ?Hs; 1..4: smt().
     by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ H) //; apply loadW64_memread; smt().
   + auto => |> &m ??????? H Hn.
     have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H; smt().
     split; first smt().
     move=> at0 buf0 st0 Hex _ H1 H2 Hm Hs.
     have E: at0 = aT{m} + 8 * (_LEN{m} %/ 8) by smt().
     by move: Hs; rewrite E (_: aT{m} + 8 * (_LEN{m} %/ 8) - aT{m} = 8 * (_LEN{m} %/ 8)) 1:/#.
(* stmts 4-5 : aT += 8*(_LEN/8); _LEN %%= 8 -- pure bookkeeping, the spec carries
   over with sz = nbase + 8*(_LEN/8) (kept existential: not expressible in the new
   _LEN).  stmt 6: the final word is one more step that finishes the stream. *)
seq 2: (Glob.mem=_mem /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ _buf + _len < W64.modulus
       /\ 0 <= _LEN < 8
       /\ exists sz, _at <= sz /\ addstate_spec _st _at (memread _mem _buf _len) _tb sz _buf buf st aT _LEN _TRAILB).
+ auto => |> &m ??????? H HL.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
if.
+ (* final word: one shared finishing step *)
  wp; ecall (m_ilen_read_upto8_at_h buf _LEN _TRAILB aT aT); auto => |> &m ??????? HL0 HL1 sz Hsz H Hg [buf1 len1 tb1 at1 w] /= Hsub.
  have Hs: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
  have Ha: 0 <= aT{m} by move: H; rewrite /addstate_spec => [#] _ _ _ Ea _ _; smt().
  rewrite set64_addstate_at //.
  move: Hsub; rewrite /msubread Hs => [#] Hsr Eat Ebuf _ _.
  apply (addstate_spec_finish (memread _mem _buf _len) (u64bytes w) _len sz _st _at _tb st{m} _buf buf{m} aT{m} _LEN{m} _TRAILB{m} at1 buf1) => //.
  + by rewrite size_memread.
  + smt().
  by rewrite (addstate_spec_drop_memread _ _ _ _ _ _ _ _ _ _ _ _ _ H).
(* nothing left: the stream and the trailing byte are already absorbed *)
auto => |> &m ??????? HL0 HL1 sz Hsz H Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec_done (memread _mem _buf _len) _len sz _st _at _tb st{m} _buf buf{m} aT{m} _TRAILB{m}) => //; [rewrite size_memread | smt()].
qed.

phoare addstate_m_ph _mem _st _at _buf _len _tb:
 [ M.__addstate_m
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 /\ 0 <= _tb < 256 
 ==> let l = memread _mem _buf _len ++ if _tb<>0 then [W8.of_int _tb] else []
     in Glob.mem=_mem
        /\ res.`1 = addstate_at _st _at l
        /\ res.`2 = _at + size l
        /\ res.`3 = _buf + _len
 ] = 1%r.
proof.
by conseq addstate_m_ll (addstate_m_h _mem _st _at _buf _len _tb) => />; smt(size_memread size_cat).
qed.

lemma absorb_m_ll: islossless M.__absorb_m.
proof.
proc; simplify.
seq 2: true => //.
 call addstate_m_ll.
 if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ll.
  call addstate_m_ll.
  by auto => /#.
 wp; call keccakf1600_ll.
 wp; call addstate_m_ll.
 by auto => /#.
if => //.
by call addratebit_ll.
qed.


(* addstate_m_h in the shape of addstate_m_avx2_h (trailing byte always present). *)
hoare addstate_m_h2 _mem _st _at _buf _len _tb:
 M.__addstate_m
 : Glob.mem=_mem /\ st=_st /\ aT=_at /\ buf=_buf /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at+_len <= 200 - b2i (_tb<>0)
 /\ _buf + _len < W64.modulus
 /\ 0 <= _tb < 256
 ==> Glob.mem=_mem
     /\ res.`1 = addstate _st (bytes2state (u8zeros _at ++ memread _mem _buf _len ++ [W8.of_int _tb]))
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _buf + _len.
proof.
conseq (addstate_m_h _mem _st _at _buf _len _tb) => /> &m ??????? r -> _ _.
rewrite addstate_atE // catA; case: (_TRAILB{m} <> 0) => [//|/= ->].
by rewrite cats0 -nseq1 bytes2state_zext.
qed.

hoare absorb_m_h _l _mem _buf _len _tb _r8:
 M.__absorb_m
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _tb < 256
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
(* `buf - _buf` bytes of the input are absorbed; each block is closed by the shared
   pabsorb_fill and the last one by pabsorb_last (as in absorb_h). *)
proc => /=.
seq 1: (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ 0 <= _len /\ _buf + _len < W64.modulus
       /\ _buf <= buf <= _buf + _len /\ _LEN = _len - (buf - _buf)
       /\ aT = (size _l + (buf - _buf)) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb_spec_ref _r8 (_l ++ take (buf - _buf) (memread _mem _buf _len)) st).
+ if => //; last first.
   auto => |> &m.
   move=> H Htb0 Htb1 Hlen Hbuf Hg.
   have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec_ref => [#].
   split; first smt().
   split; first smt().
   split; first smt().
   by rewrite take0 cats0.
  wp; while (Glob.mem = _mem /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200 /\
             0 <= _len /\ _buf + _len < W64.modulus /\
             iTERS = (_len - (_r8 - size _l %% _r8)) %/ _r8 /\ 0 <= i <= iTERS /\
             buf = _buf + (_r8 - size _l %% _r8 + i * _r8) /\
             pabsorb_spec_ref _r8 (_l ++ take (_r8 - size _l %% _r8 + i * _r8) (memread _mem _buf _len)) st).
  + wp; ecall (keccakf1600_h st); ecall (addstate_m_h2 Glob.mem st 0 buf _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hlen Hbuf Hi0 Hi1 IH Hb.
    have Hm: 0 <= i{m} * _r8 by apply mulr_ge0 => /#.
    have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by rewrite ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_len - (_r8 - size _l %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ??? [st' at' buf'] /= Est _ Ebuf.
    split; first smt().
    split; first smt().
    have Ed: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
    have Ha0: (size _l + (_r8 - size _l %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have Hf := pabsorb_fill _r8 _l (memread _mem _buf _len) (_r8 - size _l %% _r8 + i{m} * _r8) st{m}.
    move: Hf; rewrite Ha0 /= => Hf.
    rewrite (_: _r8 - size _l %% _r8 + (i{m} + 1) * _r8 = _r8 - size _l %% _r8 + i{m} * _r8 + _r8) 1:/#.
    rewrite Est -(slice_memread _mem _buf _len (_r8 - size _l %% _r8 + i{m} * _r8) _r8) 1..3:/#.
    by apply Hf => //; rewrite ?size_memread //; smt().
  wp; ecall (keccakf1600_h st); wp; ecall (addstate_m_h2 Glob.mem st aT buf (_RATE8 - aT) 0); auto => |> &m.
  move=> H Htb0 Htb1 Hlen Hbuf Hg.
  have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec_ref => [#].
  have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ????? [st' at' buf'] /= Est _ Ebuf.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   have Hf := pabsorb_fill _r8 _l (memread _mem _buf _len) 0 st{m}.
   move: Hf => /=; rewrite take0 drop0 cats0 => Hf.
   rewrite Est -(take_memread' _mem _buf _len (_r8 - size _l %% _r8)) 1:/#.
   by apply Hf => //; rewrite ?size_memread //; smt().
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs.
  have Ei: i0 = (_len - (_r8 - size _l %% _r8)) %/ _r8 by smt().
  have Ed: _len - (_r8 - size _l %% _r8) = (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 + (_len - (_r8 - size _l %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
  have Hq: 0 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by apply mulr_ge0 => /#.
  have Hmd: 0 <= (_len - (_r8 - size _l %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  move: Hs; rewrite Ei => Hs.
  rewrite (_: _buf + (_r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) - _buf = _r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) 1:/#.
  split; first smt().
  split; first smt().
  split.
   by rewrite (_: size _l + (_r8 - size _l %% _r8 + (_len - (_r8 - size _l %% _r8)) %/ _r8 * _r8) = (size _l %/ _r8 + 1 + (_len - (_r8 - size _l %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
  by split; first smt().
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_h _RATE8 st); ecall (addstate_m_h2 Glob.mem st aT buf _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Hlen Hbuf Hb0 Hb1 Hfit H Htb.
  split; first smt().
  move=> ????? [st' at' buf'] /= Est _ Ebuf.
  have Hk: 0 <= buf{m} - _buf <= size (memread _mem _buf _len) by rewrite size_memread //; smt().
  have Hfit': (size _l + (buf{m} - _buf)) %% _r8 + (size (memread _mem _buf _len) - (buf{m} - _buf)) < _r8 by rewrite size_memread.
  have [Hl1 _] := pabsorb_last _r8 _l (memread _mem _buf _len) (buf{m} - _buf) st{m} _tb Hk Hfit' H.
  split; last smt().
  by rewrite Est -(drop_memread_cur _mem _buf _len buf{m}) 1:/# Hl1.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_m_h2 Glob.mem st aT buf _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Hlen Hbuf Hb0 Hb1 Hfit H.
split; first smt().
move=> ????? [st' at' buf'] /= Est Eat Ebuf.
have Hk: 0 <= buf{m} - _buf <= size (memread _mem _buf _len) by rewrite size_memread //; smt().
have Hfit': (size _l + (buf{m} - _buf)) %% _r8 + (size (memread _mem _buf _len) - (buf{m} - _buf)) < _r8 by rewrite size_memread.
have [_ Hl0] := pabsorb_last _r8 _l (memread _mem _buf _len) (buf{m} - _buf) st{m} 0 Hk Hfit' H.
split.
 by rewrite pabsorb_spec_refE; move: (Hl0 (eq_refl 0)) => /=; rewrite Est -(drop_memread_cur _mem _buf _len buf{m}) 1:/#.
split; last smt().
rewrite Eat b2i0 /=.
have E: (size _l + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf)) = (size _l + _len) + (- (size _l + (buf{m} - _buf)) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l + (buf{m} - _buf)) %% _r8 + (_len - (buf{m} - _buf))) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_m_ph _l _mem _buf _len _tb _r8:
 [ M.__absorb_m
 : Glob.mem=_mem /\ aT=size _l %% _r8 /\ buf=_buf /\ _LEN=_len /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _tb < 256
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
by conseq absorb_m_ll (absorb_m_h _l _mem _buf _len _tb _r8) => /> /#.
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)


lemma dumpstate_m_ll: islossless M.__dumpstate_m.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc => /=.
seq 1: #pre => //; first by inline*; auto.
if => //.
 seq 3: true => //.
  wp; while true (inc - j).
   by move=> z; auto => /#.
  by auto => /#.
 by islossless.
seq 2: true => //.
 while true (_LEN %/ 8 - i).
  by move=> z; auto => /#.
 by auto => /#.
by islossless.
qed.

hoare dumpstate_m_h _mem _buf _len _st:
 M.__dumpstate_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len.
proof.
proc => /=.
seq 1: #pre; first by inline *; auto.
(* the first [8*(_len%/8)] bytes (whole words) are written *)
seq 1: (msubwrite _mem Glob.mem (sub (stbytes _st) 0 (8*(_len%/8))) _buf _len buf (_len - 8*(_len%/8))
        /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200).
 if => //.
  (* AVX2: 32-byte loop, then 16- and 8-byte tails *)
  seq 3: (msubwrite _mem Glob.mem (sub (stbytes _st) 0 (32*(_len%/32))) _buf _len buf (_len - 32*(_len%/32))
          /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200).
   while (0 <= j <= inc /\ inc = _len %/ 32 /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200
          /\ msubwrite _mem Glob.mem (sub (stbytes _st) 0 (32*j)) _buf _len buf (_len - 32*j)).
    auto => |> &m Hj0 Hj1 Hl0 Hl1 Hsw Hj.
    split; first smt().
    apply (msubwrite_dump_step (stbytes _st) _mem Glob.mem{m} _ _buf _len (32*j{m}) 32 (u256bytes (get256_direct (stbytes _st) (32*j{m}))) buf{m} (buf{m}+32)
             (32*(j{m}+1)) (_len - 32*j{m}) (_len - 32*(j{m}+1)) _ _ _ _ _ _ Hsw); 1..6: smt().
     by rewrite u256bytes_get256.
    by apply msubwrite_storeW256; smt().
   auto => |> &hr Hl0 Hl1 _ _; split; first by split; [smt(divz_ge0) | apply msubwrite_dump0].
   move=> mem buf j Hj0 Hj1 Hj2 Hsw.
   by have <-: j = _len %/ 32 by smt().
  seq 1: (msubwrite _mem Glob.mem (sub (stbytes _st) 0 (16*(_len%/16))) _buf _len buf (_len - 16*(_len%/16))
          /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200).
   if => //.
    auto => |> &m Hsw Hl0 Hl1 C.
    apply (msubwrite_dump_step (stbytes _st) _mem Glob.mem{m} _ _buf _len (32*(_len%/32)) 16 (u128bytes (get128_direct (stbytes _st) (_len %/ 32 * 32))) buf{m} (buf{m}+16)
             (16*(_len%/16)) (_len - 32*(_len%/32)) (_len - 16*(_len%/16)) _ _ _ _ _ _ Hsw); 1..6: smt().
     by rewrite u128bytes_get128 mulzC.
    by apply msubwrite_storeW128; smt().
   by auto => |> &m Hsw Hl0 Hl1 C; rewrite (_: 16 * (_len %/ 16) = 32*(_len%/32)) 1:/#.
  if => //.
   auto => |> &m Hsw Hl0 Hl1 C.
   apply (msubwrite_dump_step (stbytes _st) _mem Glob.mem{m} _ _buf _len (16*(_len%/16)) 8 (u64bytes (get64_direct (stbytes _st) (_len %/ 16 * 16))) buf{m} (buf{m}+8)
            (8*(_len%/8)) (_len - 16*(_len%/16)) (_len - 8*(_len%/8)) _ _ _ _ _ _ Hsw); 1..6: smt().
    by rewrite u64bytes_get64 mulzC.
   by apply msubwrite_storeW64; smt().
  by auto => |> &m Hsw Hl0 Hl1 C; rewrite (_: 8 * (_len %/ 8) = 16*(_len%/16)) 1:/#.
 (* scalar: 8-byte loop *)
 while (0 <= i <= _len %/ 8 /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200
        /\ msubwrite _mem Glob.mem (sub (stbytes _st) 0 (8*i)) _buf _len buf (_len - 8*i)).
  auto => |> &m Hi0 Hi1 Hl0 Hl1 Hsw Hi.
  split; first smt().
  apply (msubwrite_dump_step (stbytes _st) _mem Glob.mem{m} _ _buf _len (8*i{m}) 8 (u64bytes _st.[i{m}]) buf{m} (buf{m}+8)
           (8*(i{m}+1)) (_len - 8*i{m}) (_len - 8*(i{m}+1)) _ _ _ _ _ _ Hsw); 1..6: smt().
   by rewrite u64bytes_stword /#.
  by apply msubwrite_storeW64; smt().
 auto => |> &hr Hl0 Hl1 _ _; split; first by split; [smt(divz_ge0) | apply msubwrite_dump0].
 move=> mem buf i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _len %/ 8 by smt().
(* last (partial) word *)
if => //.
 wp; ecall (m_ilen_write_upto8_h Glob.mem buf (_LEN %% 8) t); auto => |> &m Hsw Hl0 Hl1 C [buf2 len2] mem2 /= H2.
 apply (msubwrite_dump_last (stbytes _st) _mem Glob.mem{m} mem2 _buf _len (8*(_len%/8)) 8 (u64bytes _st.[_len %/ 8]) buf{m} buf2
          (_len - 8*(_len%/8)) len2 _ _ _ Hsw _ _); 1..3: smt().
  by rewrite u64bytes_stword /#.
 by rewrite (_: _len - 8 * (_len %/ 8) = _len %% 8) 1:/#.
auto => |> &m Hsw Hl0 Hl1 C.
apply (msubwrite_dump_fin (stbytes _st) _mem Glob.mem{m} _buf _len buf{m}) => //.
by move: Hsw; rewrite (_: 8 * (_len %/ 8) = _len) 1:/#.
qed.

phoare dumpstate_m_ph _mem _buf _len _st:
 [ M.__dumpstate_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (sub (stbytes _st) 0 _len)
  /\ res = _buf + _len
 ] = 1%r.
proof.
by conseq dumpstate_m_ll (dumpstate_m_h _mem _buf _len _st).
qed.

lemma squeeze_m_ll: islossless M.__squeeze_m.
proof.
proc; simplify.
seq 2: true => //.
 while true (_LEN %/ _RATE8 - i).
  move => z; auto => />.
  call dumpstate_m_ll.
  call keccakf1600_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_m_ll.
call keccakf1600_ll.
by auto => /#.
qed.

hoare squeeze_m_h _mem _buf _len _st _r8:
 M.__squeeze_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len.
proof.
proc.
seq 2: (0 <= _len /\ 0 < _r8 <= 200 /\ _buf + _len < W64.modulus /\ _LEN = _len /\ _RATE8 = _r8
        /\ st = st_i _st (_len %/ _r8) /\ buf = _buf + _r8 * (_len %/ _r8)
        /\ msubwrite _mem Glob.mem (squeezeblocks _r8 _st (_len %/ _r8)) _buf _len buf (_len - _r8 * (_len %/ _r8))).
 while (0 <= i <= _len %/ _r8 /\ 0 <= _len /\ 0 < _r8 <= 200 /\ _buf + _len < W64.modulus
        /\ _LEN = _len /\ _RATE8 = _r8 /\ st = st_i _st i /\ buf = _buf + _r8 * i
        /\ msubwrite _mem Glob.mem (squeezeblocks _r8 _st i) _buf _len buf (_len - _r8 * i)).
  wp; ecall (dumpstate_m_h Glob.mem buf _RATE8 st); ecall (keccakf1600_h st).
  auto => |> &m Hi0 Hi1 Hl Hr0 Hr1 Hb Hsw Hi; split.
   split; first smt().
   have: _r8 * (i{m} + 1) <= _len by apply mul_divz_le => /#.
   smt().
  move=> _ _ _; split; first smt().
  have Est: keccak_f1600_op (st_i _st i{m}) = st_i _st (i{m}+1) by rewrite /st_i iterS 1:/#.
  rewrite Est /=; split; first smt().
  rewrite squeezeblocks_step 1:/# 1:/#.
  apply (msubwrite_app _ _ _ _ _ _ _ _ _ _ _ _ _ Hsw).
  + rewrite size_squeezeblocks 1,2:/# size_sub 1:/#.
    by have := mul_divz_le _r8 _len (i{m}+1) _ _; smt().
  + by rewrite size_sub /#.
  + by rewrite size_sub /#.
 auto => |> Hl Hr0 Hr1 Hb; split.
  split; first smt(divz_ge0).
  split; first by rewrite /st_i iter0.
  by rewrite /squeezeblocks iota0 //= flatten_nil /msubwrite store0 /#.
 move=> mem i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _len %/ _r8 by smt().
if => //.
 ecall (dumpstate_m_h Glob.mem buf (_LEN %% _RATE8) st); ecall (keccakf1600_h st).
 auto => |> &m Hl Hr0 Hr1 Hb Hsw C.
 have Est: keccak_f1600_op (st_i _st (_len %/ _r8)) = st_i _st (_len %/ _r8 + 1).
  by rewrite /st_i iterS 1:divz_ge0 /#.
 split; first smt().
 move=> _ _ _; rewrite Est; split.
  by apply (msubwrite_squeeze_last _ _ _ _ _ _ _ _ _ _ _ Hsw).
 split; first by rewrite divz_pred_pos 1,2:/#.
 smt().
auto => |> &m Hl Hr0 Hr1 Hb Hsw C.
split; first by apply (msubwrite_squeeze_fin _ _ _ _ _ _ _ _ _ _ _ Hsw).
split; first by rewrite divz_pred_zero 1,2:/#.
smt().
qed.

phoare squeeze_m_ph _mem _buf _len _st _r8:
 [ M.__squeeze_m
 : Glob.mem=_mem /\ buf=_buf /\ _LEN=_len /\ st=_st /\ _RATE8=_r8
 /\ 0 <= _len
 /\ 0 < _r8 <= 200
 /\ _buf + _len < W64.modulus
 ==> Glob.mem = stores _mem _buf (SQUEEZE1600 _r8 _len _st)
     /\ res.`1 = st_i _st ((_len-1) %/ _r8 + 1)
     /\ res.`2 = _buf + _len
 ] = 1%r.
proof.
by conseq squeeze_m_ll (squeeze_m_h _mem _buf _len _st _r8).
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
  proc __addstate (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
                   offset:int, _LEN:int, _TRAILB:int) : W64.t Array25.t *
                                                        int * int = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var aT8:int;
    var w:W64.t;
    var t256:W256.t;
    var i:int;
    var t128:W128.t;
    var at:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, 1+2+4);
    dELTA <- 0;
    if (((aT %% 8) <> 0)) {
      aT8 <- (8 * (aT %/ 8));
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, offset,
      dELTA, _LEN, _TRAILB, aT8, aT);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
      aT8 ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0])) aT8) `^` w)
      )));
    } else {

    }
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      i <- 0;
      while ((i < inc)) {
        t256 <-
        (get256_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 32);
        t256 <-
        (t256 `^`
        (get256_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + (32 * i))));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set256_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + (32 * i)) t256)));
        i <- (i + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        t128 <-
        (get128_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 16);
        t128 <-
        (t128 `^`
        (get128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 32) * 32))));
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 32) * 32)) t128)));
      } else {

      }
      if ((8 <= (_LEN %% 16))) {
        w <-
        (get64_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA));
        dELTA <- (dELTA + 8);
        st <-
        (Array25.init
        (WArray200.get64
        (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        (aT + ((_LEN %/ 16) * 16))
        ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
         (aT + ((_LEN %/ 16) * 16))) `^`
        w))));
      } else {

      }
    } else {
      at <- (aT %/ 8);
      offset <- (offset + dELTA);
      dELTA <- 0;
      while ((at < ((aT %/ 8) + (_LEN %/ 8)))) {
        w <- (get64_direct (WA.init8 (fun i_0 => buf.[i_0])) offset);
        offset <- (offset + 8);
        st.[at] <- (st.[at] `^` w);
        at <- (at + 1);
      }
    }
    aT <- (aT + (8 * (_LEN %/ 8)));
    _LEN <- (_LEN %% 8);
    if (((0 < _LEN) \/ ((_TRAILB %% 256) <> 0))) {
      aT8 <- aT;
      (dELTA, _LEN, _TRAILB, aT, w) <@ RW.MM.__a_ilen_read_upto8_at (buf, offset,
      dELTA, _LEN, _TRAILB, aT, aT);
      st <-
      (Array25.init
      (WArray200.get64
      (WArray200.set64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
      aT8 ((get64_direct (WArray200.init64 (fun i_0 => st.[i_0])) aT8) `^` w)
      )));
    } else {

    }
    offset <- (offset + dELTA);
    return (st, aT, offset);
  }
  proc __absorb (st:W64.t Array25.t, aT:int, buf:W8.t A.t,
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
      (st,  _0, offset) <@ __addstate (st, aT, buf, offset, (_RATE8 - aT),
      0);
      _LEN <- (_LEN - (_RATE8 - aT));
      aT <- 0;
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      iTERS <- (_LEN %/ _RATE8);
      i <- 0;
      while ((i < iTERS)) {
        (st,  _1, offset) <@ __addstate (st, 0, buf, offset, _RATE8, 0);
        (* Erased call to spill *)
        st <@ M._keccakf1600 (st);
        (* Erased call to unspill *)
        i <- (i + 1);
      }
      _LEN <- (_LEN %% _RATE8);
    } else {

    }
    (st, aT,  _2) <@ __addstate (st, aT, buf, offset, _LEN, _TRAILB);
    if ((_TRAILB <> 0)) {
      st <@ M.__addratebit (st, _RATE8);
    } else {

    }
    return (st, aT);
  }
  proc __dumpstate (buf:W8.t A.t, offset:int, _LEN:int,
                    st:W64.t Array25.t) : W8.t A.t * int = {
    var inc:int;
    var hAS_AVX2:bool;
    var dELTA:int;
    var t:W64.t;
    var j:int;
    var t256:W256.t;
    var t128:W128.t;
    var i:int;
    var  _0:int;
    hAS_AVX2 <@ M.__HAS_FEATURE (4, 1+2+4);
    dELTA <- 0;
    if (hAS_AVX2) {
      inc <- (_LEN %/ 32);
      j <- 0;
      while ((j < inc)) {
        t256 <-
        (get256_direct (WArray200.init64 (fun i_0 => st.[i_0])) (32 * j));
        buf <-
        (A.init
        (WA.get8
        (WA.set256_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t256)));
        dELTA <- (dELTA + 32);
        j <- (j + 1);
      }
      if ((16 <= (_LEN %% 32))) {
        t128 <-
        (get128_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        ((_LEN %/ 32) * 32));
        buf <-
        (A.init
        (WA.get8
        (WA.set128_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t128)));
        dELTA <- (dELTA + 16);
      } else {

      }
      if ((8 <= (_LEN %% 16))) {
        t <-
        (get64_direct (WArray200.init64 (fun i_0 => st.[i_0]))
        ((_LEN %/ 16) * 16));
        buf <-
        (A.init
        (WA.get8
        (WA.set64_direct (WA.init8 (fun i_0 => buf.[i_0]))
        (offset + dELTA) t)));
        dELTA <- (dELTA + 8);
      } else {

      }
    } else {
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
    }
    if ((0 < (_LEN %% 8))) {
      t <- st.[(_LEN %/ 8)];
      (buf, dELTA,  _0) <@ RW.MM.__a_ilen_write_upto8 (buf, offset, dELTA,
      (_LEN %% 8), t);
    } else {

    }
    offset <- (offset + dELTA);
    return (buf, offset);
  }
  proc __squeeze (st:W64.t Array25.t, buf:W8.t A.t, _RATE8:int) :
  W64.t Array25.t * W8.t A.t = {
    var offset:int;
    var i:int;
    offset <- 0;
    i <- 0;
    while ((i < (_ASIZE %/ _RATE8))) {
      i <- (i + 1);
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate (buf, offset, _RATE8, st);
    }
    if ((0 < (_ASIZE %% _RATE8))) {
      (* Erased call to spill *)
      st <@ M._keccakf1600 (st);
      (* Erased call to unspill *)
      (buf, offset) <@ __dumpstate (buf, offset, (_ASIZE %% _RATE8), st);
    } else {

    }
    return (st, buf);
  }
}.


lemma addstate_ll: islossless MM.__addstate.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc.
seq 4: true => //; last by islossless.
seq 2: true => //; first by inline*; auto.
seq 1: true => //; first by islossless.
if => //.
 seq 3: true => //; last by islossless.
 wp; while true (inc - i).
  by move=> z; auto => /#.
 by auto => /#.
while true ((aT %/ 8) + (_LEN %/ 8) - at).
 by move=> z; auto => /#.
by auto => /#.
qed.

hoare addstate_h _st _at _buf _off _len _tb:
 MM.__addstate
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _off /\ _off + _len <= _ASIZE
 /\ 0 <= _tb < 256
 ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
     in res.`1 = addstate_at _st _at l
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _off + _len.
proof.
(* Same structure as addstate_m_h, on the shared read-step layer: the input is
   `sub _buf _off _len` and the cursor is `offset + dELTA`. *)
proc => /=.
pose base:= 8 * (_at %/ 8).
pose nbase:= 8 * ((_at-1) %/ 8 + 1).
(* stmts 1-3 : __HAS_FEATURE, dELTA <- 0 and the alignment prefix. *)
seq 3: (buf = _buf /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec _st _at (sub _buf _off _len) _tb nbase _off (offset + dELTA) st aT _LEN _TRAILB
       /\ 0 <= offset /\ 0 <= dELTA).
+ seq 2: (#pre /\ dELTA = 0); first by inline*; auto.
  if => //.
   wp; ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB aT8 aT); auto => |> &m ????????.
   move=> [dlt0 len0 tb0 at0 w0] /=.
   move => H; rewrite set64_addstate_at 1:/#.
   split; last by move: H; rewrite /asubread => [#] _ _ -> _ _; rewrite /srincr; smt(size_ge0).
   apply (addstate_asubread_u64 _buf w0 (8 * (_at %/ 8)) _st _at _off _len _tb _st _at 0 _len _tb nbase at0 dlt0 len0 tb0) => //;
    [smt() | by rewrite /nbase; smt() | by apply addstate_spec_init => //; smt(size_sub')].
  auto => |> *.
  have ->@/base: nbase = base by smt().
  by apply addstate_spec_init; smt(size_sub').
(* stmt 3 : if hAS_AVX2 — both branches consume `8*(_LEN%/8)` further aligned bytes. *)
seq 1: (buf = _buf /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec _st _at (sub _buf _off _len) _tb (nbase+8*(_LEN%/8)) _off (offset + dELTA) st (aT+8*(_LEN%/8)) (_LEN-8*(_LEN%/8)) _TRAILB /\ 0 <= _LEN /\ 0 <= offset /\ 0 <= dELTA).
 if => //.
 - seq 3: (buf = _buf /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec _st _at (sub _buf _off _len) _tb (nbase+32*(_LEN%/32)) _off (offset + dELTA) st (aT+32*(_LEN%/32)) (_LEN-32*(_LEN%/32)) _TRAILB /\ 0 <= _LEN /\ 0 <= offset /\ 0 <= dELTA).
   while (#[/1:9]pre /\ inc = _LEN%/32 /\
          0 <= i <= _LEN%/32 /\ 0 <= dELTA /\
          addstate_spec _st _at (sub _buf _off _len) _tb (nbase+32*i) _off (offset + dELTA) st (aT+32*i) (_LEN-32*i) _TRAILB).
    auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz ?? Hd IH Hb; split; first smt().
    split; first smt().
    rewrite xorwC set256_addstate_at 1:/#.
    have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz IH.
    apply (addstate_spec_fullword _ _ (nbase + 32 * i{m}) _st _at _tb st{m} _off (offset{m} + dELTA{m}) (aT{m} + 32 * i{m}) (_LEN{m} - 32 * i{m}) _TRAILB{m}) => //; rewrite ?size_to_list; 1..6: smt().
    by rewrite Erem; apply getW256_bytearray; smt().
   auto => |> &m ???????? H Ho Hd Hh; split.
    have ?: 0<= _LEN{m}.
     move: H; rewrite /addstate_spec => />. smt(size_ge0).
    smt().
   move => dlt1 i st1 ????; have ->: i=_LEN{m} %/ 32 by smt().
   by move=> Hs; split => //; smt().
   seq 1: (buf = _buf /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ addstate_spec _st _at (sub _buf _off _len) _tb (nbase+16*(_LEN%/16)) _off (offset + dELTA) st (aT+16*(_LEN%/16)) (_LEN-16*(_LEN%/16)) _TRAILB /\ 0 <= _LEN /\ 0 <= offset /\ 0 <= dELTA).
   if => //.
     auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz IH HL Ho Hd Hb.
     split; last smt().
     rewrite xorwC set128_addstate_at 1:/# (_: aT{m} + _LEN{m} %/ 32 * 32 = aT{m} + 32 * (_LEN{m} %/ 32)) 1:/#.
     have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz IH.
     apply (addstate_spec_fullword _ _ (nbase + 32 * (_LEN{m} %/ 32)) _st _at _tb st{m} _off (offset{m} + dELTA{m}) (aT{m} + 32 * (_LEN{m} %/ 32)) (_LEN{m} - 32 * (_LEN{m} %/ 32)) _TRAILB{m}) => //; rewrite ?size_to_list; 1..6: smt().
     by rewrite Erem; apply getW128_bytearray; smt().
    auto => |> ???????? H Hb HL Ho Hd.
    move => Hc; have E: forall n, !16 <= n %% 32 => 16 * (n %/ 16) = 32 * (n %/ 32) by smt().
    by rewrite !(E _ Hc); exact Hb.
   if => //.
     auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz H HL Ho Hd Hb.
     split; last smt().
     rewrite set64_addstate_at 1:/# (_: aT{m} + _LEN{m} %/ 16 * 16 = aT{m} + 16 * (_LEN{m} %/ 16)) 1:/#.
     have Hs: size (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) (offset{m} + dELTA{m}))) = 8 by rewrite /u64bytes size_to_list.
     have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz H.
     apply (addstate_spec_fullword _ _ (nbase + 16 * (_LEN{m} %/ 16)) _st _at _tb st{m} _off (offset{m} + dELTA{m}) (aT{m} + 16 * (_LEN{m} %/ 16)) (_LEN{m} - 16 * (_LEN{m} %/ 16)) _TRAILB{m}) => //; rewrite ?Hs; 1..6: smt().
     by rewrite Erem; apply getW64_bytearray; smt().
    auto => |> ????????? H HL Ho Hd Hb.
    have E: forall n, !8 <= n %% 16 => 8 * (n %/ 8) = 16 * (n %/ 16) by smt().
    by rewrite !(E _ Hb); exact H.
 - (* scalar branch: word-indexed loop; the spec is advanced by 8*(at - aT%/8) bytes. *)
   while (#[/1:9]pre /\ 0 <= _LEN /\ dELTA = 0 /\ 0 <= offset /\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\
          addstate_spec _st _at (sub _buf _off _len) _tb (nbase + 8 * (at - aT %/ 8)) _off offset st (aT + 8 * (at - aT %/ 8)) (_LEN - 8 * (at - aT %/ 8)) _TRAILB).
   + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL Ho H1 H2 H Hb.
     split; first smt().
     split; first smt().
     have Ea: aT{m} + 8 * (at{m} - aT{m} %/ 8) = nbase + 8 * (at{m} - aT{m} %/ 8).
      by apply (addstate_spec_sz _st _at (sub _buf _off _len) _tb (nbase + 8 * (at{m} - aT{m} %/ 8)) _off offset{m} st{m} (aT{m} + 8 * (at{m} - aT{m} %/ 8)) (_LEN{m} - 8 * (at{m} - aT{m} %/ 8)) _TRAILB{m}) => //; smt().
     have Hal8: aT{m} + 8 * (at{m} - aT{m} %/ 8) = 8 * at{m} by move: Ea; rewrite /nbase; smt().
     have Hfit: aT{m} + 8 * (at{m} - aT{m} %/ 8) + (_LEN{m} - 8 * (at{m} - aT{m} %/ 8)) = _at + size (sub _buf _off _len).
      by apply (addstate_spec_fit _st _at (sub _buf _off _len) _tb (nbase + 8 * (at{m} - aT{m} %/ 8)) _off offset{m} st{m} (aT{m} + 8 * (at{m} - aT{m} %/ 8)) (_LEN{m} - 8 * (at{m} - aT{m} %/ 8)) _TRAILB{m}) => //; smt().
     rewrite setw_addstate_at; first smt(size_sub').
     rewrite -Hal8.
     have Hs: size (u64bytes (get64_direct (WA.init8 ("_.[_]" _buf)) offset{m})) = 8 by rewrite /u64bytes size_to_list.
     have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz H.
     apply (addstate_spec_fullword _ _ (nbase + 8 * (at{m} - aT{m} %/ 8)) _st _at _tb st{m} _off offset{m} (aT{m} + 8 * (at{m} - aT{m} %/ 8)) (_LEN{m} - 8 * (at{m} - aT{m} %/ 8)) _TRAILB{m}) => //; rewrite ?Hs; 1..5: smt().
     by rewrite Erem; apply getW64_bytearray; smt().
   + auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz H Ho Hd Hn.
     have HL: 0 <= _LEN{m} by have := addstate_spec_len _ _ _ _ _ _ _ _ _ _ _ H; smt().
     split; first smt().
     move=> at0 off0 st0 Hex _ _ H1 H2 Hs.
     have E: at0 = aT{m} %/ 8 + _LEN{m} %/ 8 by smt().
     by move: Hs; rewrite E (_: aT{m} %/ 8 + _LEN{m} %/ 8 - aT{m} %/ 8 = _LEN{m} %/ 8) 1:/#.
(* stmts 4-5 : bookkeeping (existential sz, as in addstate_m_h); stmt 6 and the
   final `offset <- offset + dELTA`: the shared finishing step. *)
seq 2: (buf = _buf /\ 0 <= _tb < 256 /\ 0 <= _at <= 200
       /\ 0 <= _len /\ _at + _len <= 200 - b2i (_tb<>0) /\ 0 <= _off /\ _off + _len <= _ASIZE
       /\ 0 <= _LEN < 8 /\ 0 <= offset /\ 0 <= dELTA
       /\ exists sz, _at <= sz /\ addstate_spec _st _at (sub _buf _off _len) _tb sz _off (offset + dELTA) st aT _LEN _TRAILB).
+ auto => |> &m ???????? H HL Ho Hd.
  split; first smt().
  exists (nbase + 8 * (_LEN{m} %/ 8)); split; first smt().
  by rewrite (_: _LEN{m} %% 8 = _LEN{m} - 8 * (_LEN{m} %/ 8)) 1:/#.
wp; if.
+ wp; ecall (a_ilen_read_upto8_at_h buf offset dELTA _LEN _TRAILB aT aT); auto => |> &m Htb0 Htb1 Hat0 Hat1 Hlen Hal Hoff Hosz HL0 HL1 Ho Hd sz Hsz H Hg [dlt1 len1 tb1 at1 w] /= Hsub.
  have Hs: size (u64bytes w) = 8 by rewrite /u64bytes size_to_list.
  have Ha: 0 <= aT{m} by move: H; rewrite /addstate_spec => [#] _ _ _ Ea _ _; smt().
  rewrite set64_addstate_at //.
  have [Erem [Hc0 Hc1]] := addstate_spec_sub_rem _ _ _ _ _ _ _ _ _ _ _ _ Hoff Hlen Hosz H.
  move: Hsub; rewrite /asubread Hs => [#] Hsr Eat Edlt _ _.
  apply (addstate_spec_finish (sub _buf _off _len) (u64bytes w) _len sz _st _at _tb st{m} _off (offset{m} + dELTA{m}) aT{m} _LEN{m} _TRAILB{m} at1 (offset{m} + dlt1)) => //.
  + by rewrite size_sub.
  + smt().
  + smt().
  by rewrite Erem; apply Hsr; smt().
(* nothing left: the stream and the trailing byte are already absorbed *)
auto => |> &m ???????? HL0 HL1 Ho Hd sz Hsz H Hg.
have Hl: _LEN{m} = 0 by smt().
move: H; rewrite Hl => H.
by apply (addstate_spec_done (sub _buf _off _len) _len sz _st _at _tb st{m} _off (offset{m} + dELTA{m}) aT{m} _TRAILB{m}) => //; [rewrite size_sub | smt()].
qed.

phoare addstate_ph _st _at _buf _off _len _tb:
 [ MM.__addstate
   : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
   /\ 0 <= _at <= 200
   /\ 0 <= _len
   /\ _at + _len <= 200 - b2i (_tb<>0)
   /\ 0 <= _off /\ _off + _len <= _ASIZE
   /\ 0 <= _tb < 256
   ==> let l = sub _buf _off _len ++ if _tb <> 0 then [W8.of_int _tb] else []
       in res.`1 = addstate_at _st _at l
       /\ res.`2 = _at + _len + b2i (_tb<>0)
       /\ res.`3 = _off + _len] = 1%r.
proof.
by conseq addstate_ll (addstate_h _st _at _buf _off _len _tb).
qed.


(* addstate_h with the trailing byte made explicit (the shape used by absorb_h). *)
hoare addstate_h2 _st _at _buf _off _len _tb:
 MM.__addstate
 : st=_st /\ aT=_at /\ buf=_buf /\ offset=_off /\ _LEN=_len /\ _TRAILB=_tb
 /\ 0 <= _at <= 200
 /\ 0 <= _len
 /\ _at + _len <= 200 - b2i (_tb<>0)
 /\ 0 <= _off /\ _off + _len <= _ASIZE
 /\ 0 <= _tb < 256
 ==> res.`1 = addstate _st (bytes2state (u8zeros _at ++ sub _buf _off _len ++ [W8.of_int _tb]))
     /\ res.`2 = _at + _len + b2i (_tb<>0)
     /\ res.`3 = _off + _len.
proof.
conseq (addstate_h _st _at _buf _off _len _tb) => /> &m ???????? r -> _ _.
by rewrite addstate_at_bytes.
qed.

lemma absorb_ll: islossless MM.__absorb.
proof.
proc; simplify.
seq 4: true => //.
 call addstate_ll.
 sp 2; if => //.
 wp; while true (iTERS-i).
  move=> z; auto.
  call keccakf1600_ll.
  call addstate_ll.
  by auto => /#.
 wp; call keccakf1600_ll.
 wp; call addstate_ll.
 by auto => /#.
if => //.
by call addratebit_ll.
qed.

hoare absorb_h _l _buf _tb _r8:
 MM.__absorb
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8.
proof.
(* `offset` bytes of the input are absorbed; each block is closed by the shared
   pabsorb_fill and the last one by pabsorb_last (as in absorb_m_h). *)
proc => /=.
have HA := _ASIZE_ge0.
seq 3: (buf = _buf /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200
       /\ 0 <= offset <= _ASIZE /\ _LEN = _ASIZE - offset
       /\ aT = (size _l + offset) %% _r8 /\ aT + _LEN < _r8
       /\ pabsorb_spec_ref _r8 (_l ++ take offset (to_list _buf)) st).
+ sp; if => //; last first.
   auto => |> &m.
   move=> H Htb0 Htb1 Hg.
   have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec_ref => [#].
   split; first smt().
   split; first smt().
   by rewrite take0 cats0.
  wp; while (buf = _buf /\ _RATE8 = _r8 /\ _TRAILB = _tb /\ 0 <= _tb < 256 /\ 0 < _r8 <= 200 /\
             iTERS = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 /\ 0 <= i <= iTERS /\
             offset = _r8 - size _l %% _r8 + i * _r8 /\
             pabsorb_spec_ref _r8 (_l ++ take offset (to_list _buf)) st).
  + wp; ecall (keccakf1600_h st); ecall (addstate_h2 st 0 buf offset _RATE8 0); auto => |> &m.
    move=> Htb0 Htb1 Hr0 Hr1 Hi0 Hi1 IH Hb.
    have Hm: 0 <= i{m} * _r8 by apply mulr_ge0 => /#.
    have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
    have h1: (i{m} + 1) * _r8 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by rewrite ler_pmul2r 1:/#; smt().
    have h2:= lez_floor (_ASIZE - (_r8 - size _l %% _r8)) _r8 _; first smt().
    split; first smt().
    move=> ???? [st' at' off'] /= Est _ Eoff.
    split; first smt().
    split; first smt().
    have Ed: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
    have Ha0: (size _l + (_r8 - size _l %% _r8 + i{m} * _r8)) %% _r8 = 0.
     by apply modz_fill_blocks.
    have Hf := pabsorb_fill _r8 _l (to_list _buf) (_r8 - size _l %% _r8 + i{m} * _r8) st{m}.
    move: Hf; rewrite Ha0 /= => Hf.
    rewrite Eoff Est -(slice_to_list _buf (_r8 - size _l %% _r8 + i{m} * _r8) _r8) 1..3:/#.
    by apply Hf => //; rewrite ?size_to_list; smt().
  wp; ecall (keccakf1600_h st); wp; ecall (addstate_h2 st aT buf offset (_RATE8 - aT) 0); auto => |> &m.
  move=> H Htb0 Htb1 Hg.
  have Hr8: 0 < _r8 <= 200 by move: H; rewrite /pabsorb_spec_ref => [#].
  have Hat: 0 <= size _l %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  split; first smt().
  move=> ????? [st' at' off'] /= Est _ Eoff.
  split.
   split; first smt().
   split; first smt(divz_ge0).
   have Hf := pabsorb_fill _r8 _l (to_list _buf) 0 st{m}.
   move: Hf => /=; rewrite take0 drop0 cats0 => Hf.
   rewrite Eoff Est -(take_to_list _buf (_r8 - size _l %% _r8)) 1:/#.
   by apply Hf => //; rewrite ?size_to_list; smt().
  move=> i0 st0 Hex _ _ Hi0 Hi1 Hs.
  have Ei: i0 = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 by smt().
  have Ed: _ASIZE - (_r8 - size _l %% _r8) = (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 + (_ASIZE - (_r8 - size _l %% _r8)) %% _r8 by exact divz_eq.
  have Ed2: size _l = size _l %/ _r8 * _r8 + size _l %% _r8 by exact divz_eq.
  have Hq: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 by smt(divz_ge0).
  have Hqm: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8 by apply mulr_ge0 => /#.
  have Hmd: 0 <= (_ASIZE - (_r8 - size _l %% _r8)) %% _r8 < _r8 by smt(modz_ge0 ltz_pmod).
  rewrite Ei; split; first smt().
  split; first smt().
  split; last smt().
  by rewrite (_: size _l + (_r8 - size _l %% _r8 + (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8 * _r8) = (size _l %/ _r8 + 1 + (_ASIZE - (_r8 - size _l %% _r8)) %/ _r8) * _r8) 1:/# modzMl.
case: (_TRAILB <> 0).
+ rcondt 2; first by call (: true ==> true) => //.
  ecall (addratebit_h _RATE8 st); ecall (addstate_h2 st aT buf offset _LEN _TRAILB); auto => |> &m.
  move=> Htb0 Htb1 Hr0 Hr1 Ho0 Ho1 Hfit H Htb.
  split; first smt().
  move=> ????? [st' at' off'] /= Est _ _.
  have Hk: 0 <= offset{m} <= size (to_list _buf) by rewrite size_to_list.
  have Hfit': (size _l + offset{m}) %% _r8 + (size (to_list _buf) - offset{m}) < _r8 by rewrite size_to_list.
  have [Hl1 _] := pabsorb_last _r8 _l (to_list _buf) offset{m} st{m} _tb Hk Hfit' H.
  by rewrite Est -(drop_to_list _buf offset{m}) 1:/# Hl1.
rcondf 2; first by call (: true ==> true) => //.
ecall (addstate_h2 st aT buf offset _LEN _TRAILB); auto => |> &m.
move=> Hr0 Hr1 Ho0 Ho1 Hfit H.
split; first smt().
move=> ????? [st' at' off'] /= Est Eat _.
have Hk: 0 <= offset{m} <= size (to_list _buf) by rewrite size_to_list.
have Hfit': (size _l + offset{m}) %% _r8 + (size (to_list _buf) - offset{m}) < _r8 by rewrite size_to_list.
have [_ Hl0] := pabsorb_last _r8 _l (to_list _buf) offset{m} st{m} 0 Hk Hfit' H.
split.
 by rewrite pabsorb_spec_refE; move: (Hl0 (eq_refl 0)) => /=; rewrite Est -(drop_to_list _buf offset{m}) 1:/#.
rewrite Eat b2i0 /=.
have E: (size _l + offset{m}) %% _r8 + (_ASIZE - offset{m}) = (size _l + _ASIZE) + (- (size _l + offset{m}) %/ _r8) * _r8 by smt(divz_eq).
rewrite -(modz_small ((size _l + offset{m}) %% _r8 + (_ASIZE - offset{m})) _r8); first smt(modz_ge0).
by rewrite E modzMDr.
qed.

phoare absorb_ph _l _buf _tb _r8:
 [ MM.__absorb
 : aT=size _l %% _r8 /\ buf=_buf /\ _RATE8=_r8 /\ _TRAILB=_tb
 /\ pabsorb_spec_ref _r8 _l st
 /\ 0 <= _tb < 256
 ==> if _tb <> 0
     then res.`1 = ABSORB1600 (W8.of_int _tb) _r8 (_l ++ to_list _buf)
     else pabsorb_spec_ref _r8 (_l ++ to_list _buf) res.`1
       /\ res.`2 = (size _l + _ASIZE) %% _r8
 ] = 1%r.
proof.
by conseq absorb_ll (absorb_h _l _buf _tb _r8); smt(ge0_size).
qed.

(*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*)


lemma dumpstate_ll: islossless MM.__dumpstate.
proof.
(* This proof script is independent of selected `KECCAK_FEATURES` *)
proc => /=.
seq 2: true => //; first by inline*; auto.
if => //.
 seq 3: true => //; last by islossless.
 wp; while true (inc - j).
  by move=> z; auto => /#.
 by auto => /#.
seq 2: true => //; last by islossless.
while true (_LEN %/ 8 - i).
 by move=> z; auto => /#.
by auto => /#.
qed.

hoare dumpstate_h _buf _off _len _st:
 MM.__dumpstate
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len.
proof.
proc.
seq 2: (#pre /\ dELTA = 0); first by inline *; auto.
(* the first [8*(_len%/8)] bytes (whole words) are written *)
seq 1: (asubwrite _buf buf _off (sub (stbytes _st) 0 (8*(_len%/8))) 0 _len (8*(_len%/8)) (_len - 8*(_len%/8))
        /\ offset + dELTA = _off + 8*(_len%/8)
        /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE).
 if => //.
  (* AVX2: 32-byte loop, then 16- and 8-byte tails (advance [dELTA]) *)
  seq 3: (asubwrite _buf buf _off (sub (stbytes _st) 0 (32*(_len%/32))) 0 _len (32*(_len%/32)) (_len - 32*(_len%/32))
          /\ offset = _off /\ dELTA = 32*(_len%/32)
          /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE).
   while (0 <= j <= inc /\ inc = _len %/ 32 /\ offset = _off /\ dELTA = 32*j
          /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE
          /\ asubwrite _buf buf _off (sub (stbytes _st) 0 (32*j)) 0 _len (32*j) (_len - 32*j)).
    auto => |> &m Hj0 Hj1 Hl0 Hl1 Hoff Hsw Hj.
    do 2!(split; first smt()).
    apply (asubwrite_dump_step (stbytes _st) _buf buf{m} _ _off _len (32*j{m}) 32
             (u256bytes (get256_direct (stbytes _st) (32*j{m}))) (32*j{m}) (32*(j{m}+1))
             (32*(j{m}+1)) (_len - 32*j{m}) (_len - 32*(j{m}+1)) _ _ _ _ _ _ Hsw); 1..6: smt().
     by rewrite u256bytes_get256.
    by apply asubwrite_set256; smt().
   auto => |> &hr Hl0 Hl1 Hoff _; split; first by split; [smt(divz_ge0) | apply asubwrite_dump0].
   move=> buf j Hj0 Hj1 Hj2 Hsw.
   by have <-: j = _len %/ 32 by smt().
  seq 1: (asubwrite _buf buf _off (sub (stbytes _st) 0 (16*(_len%/16))) 0 _len (16*(_len%/16)) (_len - 16*(_len%/16))
          /\ offset = _off /\ dELTA = 16*(_len%/16)
          /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE).
   if => //.
    auto => |> &m Hsw Hl0 Hl1 Hoff C.
    split; last smt().
    apply (asubwrite_dump_step (stbytes _st) _buf buf{m} _ _off _len (32*(_len%/32)) 16
             (u128bytes (get128_direct (stbytes _st) (_len %/ 32 * 32))) (32*(_len%/32)) (16*(_len%/16))
             (16*(_len%/16)) (_len - 32*(_len%/32)) (_len - 16*(_len%/16)) _ _ _ _ _ _ Hsw); 1..6: smt().
     by rewrite u128bytes_get128 mulzC.
    by apply asubwrite_set128; smt().
   by auto => |> &m Hsw Hl0 Hl1 Hoff C; rewrite (_: 16 * (_len %/ 16) = 32*(_len%/32)) 1:/#.
  if => //.
   auto => |> &m Hsw Hl0 Hl1 Hoff C.
   split; last smt().
   apply (asubwrite_dump_step (stbytes _st) _buf buf{m} _ _off _len (16*(_len%/16)) 8
            (u64bytes (get64_direct (stbytes _st) (_len %/ 16 * 16))) (16*(_len%/16)) (8*(_len%/8))
            (8*(_len%/8)) (_len - 16*(_len%/16)) (_len - 8*(_len%/8)) _ _ _ _ _ _ Hsw); 1..6: smt().
    by rewrite u64bytes_get64 mulzC.
   by apply asubwrite_set64; smt().
  by auto => |> &m Hsw Hl0 Hl1 Hoff C; rewrite (_: 8 * (_len %/ 8) = 16*(_len%/16)) 1:/#.
 (* scalar: 8-byte loop (advances [offset]) *)
 while (0 <= i <= _len %/ 8 /\ offset = _off + 8*i /\ dELTA = 0
        /\ _LEN = _len /\ st = _st /\ 0 <= _len <= 200 /\ _off + _len <= _ASIZE
        /\ asubwrite _buf buf _off (sub (stbytes _st) 0 (8*i)) 0 _len (8*i) (_len - 8*i)).
  auto => |> &m Hi0 Hi1 Hl0 Hl1 Hoff Hsw Hi.
  do 2!(split; first smt()).
  apply (asubwrite_dump_step (stbytes _st) _buf buf{m} _ _off _len (8*i{m}) 8
           (u64bytes _st.[i{m}]) (8*i{m}) (8*(i{m}+1))
           (8*(i{m}+1)) (_len - 8*i{m}) (_len - 8*(i{m}+1)) _ _ _ _ _ _ Hsw); 1..6: smt().
   by rewrite u64bytes_stword /#.
  by apply asubwrite_set64; smt().
 auto => |> &hr Hl0 Hl1 Hoff _; split; first by split; [smt(divz_ge0) | apply asubwrite_dump0].
 move=> buf i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _len %/ 8 by smt().
(* last (partial) word, written at [offset + dELTA] *)
if => //.
 wp; ecall (a_ilen_write_upto8_h buf offset dELTA (_LEN %% 8) t); auto => |> &m Hsw Hod Hl0 Hl1 Hoff C [buf2 dlt2 len2] /= H2.
 have H2' := asubwrite_rebase _ _ _ _off _ _ _ _ _ H2.
 have [-> Hd] := asubwrite_dump_last (stbytes _st) _buf buf{m} buf2 _off _len (8*(_len%/8)) 8
                   (u64bytes _st.[_len %/ 8]) (8*(_len%/8)) (dlt2 + (offset{m} - _off))
                   (_len - 8*(_len%/8)) len2 _ _ _ Hsw _ _; 1..3: smt().
  by rewrite u64bytes_stword /#.
  by rewrite (_: _len - 8 * (_len %/ 8) = _len %% 8) 1:/# (_: 8 * (_len %/ 8) = dELTA{m} + (offset{m} - _off)) 1:/#.
 smt().
auto => |> &m Hsw Hod Hl0 Hl1 Hoff C.
have [-> _] := asubwrite_dump_fin (stbytes _st) _buf buf{m} _off _len (8*(_len%/8)) _ _ => //.
 by move: Hsw; rewrite (_: 8 * (_len %/ 8) = _len) 1:/#.
smt().
qed.

phoare dumpstate_ph _buf _off _len _st:
 [ MM.__dumpstate
 : buf=_buf /\ offset=_off /\ _LEN=_len /\ st=_st
 /\ 0 <= _len <= 200
 /\ _off + _len <= _ASIZE
 ==> res.`1 = A.fill (fun i=>(stbytes _st).[i-_off]) _off _len _buf
  /\ res.`2 = _off + _len
 ] = 1%r.
proof.
by conseq dumpstate_ll (dumpstate_h _buf _off _len _st).
qed.

lemma squeeze_ll: islossless MM.__squeeze.
proof.
proc; simplify.
seq 3: true => //.
 while true (_ASIZE %/ _RATE8 - i).
  move => z.
  call dumpstate_ll.
  call keccakf1600_ll.
  by auto => /#.
 by auto => /#.
if => //.
call dumpstate_ll.
call keccakf1600_ll.
by auto => /#.
qed.

hoare squeeze_h _buf _st _r8:
 MM.__squeeze
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st).
proof.
proc.
seq 3: (0 < _r8 <= 200 /\ _RATE8 = _r8 /\ st = st_i _st (_ASIZE %/ _r8) /\ offset = _r8 * (_ASIZE %/ _r8)
        /\ asubwrite _buf buf 0 (squeezeblocks _r8 _st (_ASIZE %/ _r8)) 0 _ASIZE offset (_ASIZE - offset)).
 while (0 <= i <= _ASIZE %/ _r8 /\ 0 < _r8 <= 200 /\ _RATE8 = _r8 /\ st = st_i _st i /\ offset = _r8 * i
        /\ asubwrite _buf buf 0 (squeezeblocks _r8 _st i) 0 _ASIZE offset (_ASIZE - offset)).
  wp; ecall (dumpstate_h buf offset _RATE8 st); ecall (keccakf1600_h st).
  auto => |> &m Hi0 Hi1 Hr0 Hr1 Hsw Hi; split.
   split; first smt().
   by have := mul_divz_le _r8 _ASIZE (i{m}+1) _ _; smt().
  move=> _ _ _ [buf2 off2] /= Hbuf2 Hoff2.
  have Est: keccak_f1600_op (st_i _st i{m}) = st_i _st (i{m}+1) by rewrite /st_i iterS 1:/#.
  rewrite Hoff2 Hbuf2 Est /=; do 2!(split; first smt()).
  rewrite squeezeblocks_step 1:/# 1:/#.
  apply (asubwrite_app_dump _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsw); 2..5: smt().
  rewrite size_squeezeblocks 1,2:/#.
  by have := mul_divz_le _r8 _ASIZE (i{m}+1) _ _; smt().
 auto => |> Hr0 Hr1; split.
  split; first smt(divz_ge0 _ASIZE_ge0).
  split; first by rewrite /st_i iter0.
  rewrite /squeezeblocks iota0 //= flatten_nil /asubwrite /=; split; last smt().
  by rewrite tP => i Hi; rewrite filliE // /#.
 move=> buf i Hi0 Hi1 Hi2 Hsw.
 by have <-: i = _ASIZE %/ _r8 by smt().
if => //.
 ecall (dumpstate_h buf offset (_ASIZE %% _RATE8) st); ecall (keccakf1600_h st).
 auto => |> &m Hr0 Hr1 Hsw C.
 have Est: keccak_f1600_op (st_i _st (_ASIZE %/ _r8)) = st_i _st (_ASIZE %/ _r8 + 1).
  by rewrite /st_i iterS 1:divz_ge0 1:/# 1:_ASIZE_ge0.
 split.
  split; first smt().
  smt(mul_divz_le).
 move=> _ _ _ [buf2 off2] /= Hbuf2 _; rewrite Est; split; first by rewrite divz_pred_pos 1,2:/#.
 rewrite Hbuf2 Est; apply (asubwrite_squeeze_last _ _ _ _ _ _ _ _ C _ Hsw) => /#.
auto => |> &m Hr0 Hr1 Hsw C.
split; first by rewrite divz_pred_zero 1,2:/#.
by apply (asubwrite_squeeze_fin _ _ _ _ _ _ _ C Hsw) => /#.
qed.

phoare squeeze_ph _buf _st _r8:
 [ MM.__squeeze
 : buf=_buf /\ st=_st /\ _RATE8=_r8
 /\ 0 < _r8 <= 200
 ==> res.`1 = st_i _st ((_ASIZE-1) %/ _r8 + 1)
     /\ to_list res.`2 = (SQUEEZE1600 _r8 _ASIZE _st)
 ] = 1%r.
proof.
by conseq squeeze_ll (squeeze_h _buf _st _r8).
qed.

end KeccakArrayRef.
