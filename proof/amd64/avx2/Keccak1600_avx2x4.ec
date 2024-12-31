(******************************************************************************
   Keccak1600_avx2x4.ec:

   Correctness proof for the 4x_AVX2 implementation



******************************************************************************)

require import List Real Distr Int IntDiv CoreMap.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_SHA3 FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

from JazzEC require import WArray768.
from JazzEC require import Jazz_avx2.
from JazzEC require import Array24 Array5.




(** lemmata (move?) *)


import Ring.IntID.

lemma bits8_bits (w: W256.t) (k: int):
 w \bits8 k = W8.bits2w (bits w (8*k) 8).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

lemma bits64_bits (w: W256.t) (k: int):
 w \bits64 k = W64.bits2w (bits w (64*k) 64).
proof.
by rewrite -all_eqP /all_eq /bits /mkseq -iotaredE /= /#.
qed.

(* useful to eval constants... *)
lemma bits8_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits8 k
 = W8.of_int (to_uint w %/ (2^(8*k)) %% 2^8).
proof.
move=> Hk; rewrite bits8_bits.
apply W8.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W8.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma bits64_red (w: W256.t) (k: int):
 0 <= k =>
 w \bits64 k
 = W64.of_int (to_uint w %/ (2^(64*k)) %% 2^64).
proof.
move=> Hk; rewrite bits64_bits.
apply W64.word_modeqP.
rewrite of_uintK !modz_mod.
rewrite W64.to_uintE bits2wK 1:size_bits //.
by rewrite bits_divmod 1..2:/# modz_mod.
qed.

lemma get256_init256 (a: W256.t Array24.t) i:
 0 <= i < 24 =>
 get256 (init256 ("_.[_]" a)) i = a.[i].
proof.
move=> Hi; rewrite /get256_direct /init256 -(unpack8K a.[i]).
congr; apply W32u8.Pack.ext_eq => x Hx.
rewrite initiE //= unpack8E !initiE 1..2:/# /=; congr.
 congr; smt().
smt().
qed.



(** Packed 4x-state *)
type state4x = W256.t Array25.t.

op (\a25bits64) (a: state4x) (k: int): state =
 Array25.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op (\a24bits64) (a: W256.t Array24.t) (k: int): W64.t Array24.t =
 Array24.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op (\a5bits64) (a: W256.t Array5.t) (k: int): W64.t Array5.t =
 Array5.map (fun (x: W256.t) => W4u64.\bits64 x k) a.

op a25pack4 (l: state list): state4x =
 Array25.init (fun i => pack4 (map (fun (s: state) => s.[i]) l)).

op a25unpack4 (st4: state4x): state list =
 map (fun k=> st4 \a25bits64 k) (iota_ 0 4).

lemma a25bits64iE x k i:
 0 <= i < 25 =>
 (x \a25bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a24bits64iE x k i:
 0 <= i < 24 =>
 (x \a24bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a5bits64iE x k i:
 0 <= i < 5 =>
 (x \a5bits64 k).[i] = x.[i] \bits64 k.
proof. by move=> Hi; rewrite mapiE //. qed.

lemma a25unpack4K s4:
 a25pack4 (a25unpack4 s4) = s4.
proof.
rewrite /a25pack4 /a25unpack4.
apply Array25.ext_eq => i Hi; rewrite initiE //=.
rewrite -iotaredE /= !a25bits64iE //=.
rewrite -{5}(unpack64K s4.[i]); congr.
by rewrite unpack64E init_of_list -iotaredE /=. 
qed.

lemma a25pack4_bits64 k (stl: state list):
 0 <= k < 4 =>
 a25pack4 stl \a25bits64 k = nth st0 stl k.
proof.
move=> Hk; apply Array25.ext_eq => i Hi.
rewrite mapiE //= initiE //= pack4bE //=.
rewrite of_listE initiE //=.
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

op a5pack4 (l: (W64.t Array5.t) list): W256.t Array5.t =
 Array5.init (fun i => pack4 (map (fun (x: W64.t Array5.t) => x.[i]) l)).

op match_state4x (st0 st1 st2 st3: state) (st4x: state4x) =
 st4x = a25pack4 [st0; st1; st2; st3].

lemma a25pack4_eq stl st4x:
 a25pack4 stl = st4x
 <=>
 all (fun k=>st4x \a25bits64 k = nth st0 stl k) (iota_ 0 4).
proof.
split.
 move => <-; apply/List.allP => k. 
 rewrite mem_iota => Hk /=; apply a25pack4_bits64; smt().
move=> /List.allP H.
apply Array25.ext_eq => i Hi.
rewrite initiE //=.
rewrite -(unpack64K st4x.[i]); congr.
apply W4u64.Pack.ext_eq => k Hk.
rewrite of_listE unpack64E !initiE //=.
rewrite -a25bits64iE // H; first smt(mem_iota).
case: (k < size stl) => E.
 by rewrite (nth_map st0) 1:/#.
rewrite !nth_out; first 2 by smt(size_map).
by rewrite createiE.
qed.

lemma a5bits64_set (c: W256.t Array5.t) x y i:
 0 <= i < 4 =>
 0 <= x < 5 =>
 c.[x <- y] \a5bits64 i
 = (c \a5bits64 i).[x <- y \bits64 i].
proof.
move=> Hi Hx; apply Array5.ext_eq => j Hj.
rewrite a5bits64iE 1:// !get_setE 1..2:/#.
case: (j=x) => E //.
by rewrite a5bits64iE.
qed.

lemma xorw_bits64 (w1 w2: W256.t) k:
 0 <= k < 4 =>
 w1 `^` w2 \bits64 k = (w1 \bits64 k) `^` (w2 \bits64 k).
proof.
move=> Hk; rewrite -{1}(unpack64K w1) -{1}(unpack64K w2). 
by rewrite xorb4u64E pack4bE // map2iE // !unpack64E !initiE.
qed.




(******************)



