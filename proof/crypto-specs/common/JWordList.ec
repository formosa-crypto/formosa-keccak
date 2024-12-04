(* List of Jasmin Words *)
require import AllCore List Int IntDiv.
from Jasmin require import JMemory JWord JUtils.


require import EclibExtra.

(* TODO: cleanup!!! *)

require BitEncoding.
import BitEncoding.BitChunking BitEncoding.BS2Int.
require import StdOrder.
import IntOrder.


lemma bs2int_take k bs:
 0 <= k =>
 bs2int (take k bs) = bs2int bs %% 2^k.
proof.
move=> Hk.
case: (k < size bs) => Hbs.
 rewrite -{2}(cat_take_drop k bs) bs2int_cat.
 rewrite size_take 1:// Hbs /=. 
 rewrite mulzC modzMDr modz_small //.
 split; first by apply bs2int_ge0.
 move=> _; move: (bs2int_le2Xs (take k bs)).
 by rewrite size_take 1:// Hbs /= /#.
rewrite take_oversize 1:/# modz_small //.
split; first by apply bs2int_ge0.
move=> _; move: (bs2int_le2Xs bs).
by move: (ler_weexpn2l 2 _ (size bs) k _); smt(size_ge0).
qed.

lemma bs2int_drop k bs:
 0 <= k =>
 bs2int (drop k bs) = bs2int bs %/ 2^k.
proof.
move=> Hk.
case: (k < size bs) => Hbs.
 rewrite -{2}(cat_take_drop k bs) bs2int_cat.
 rewrite size_take 1:// Hbs /= mulzC divzMDr.
  smt(gt0_pow2).
 rewrite divz_small //.
 split; first by apply bs2int_ge0.
 move=> _; move: (bs2int_le2Xs (take k bs)).
 by rewrite size_take 1:// Hbs /= /#.
rewrite drop_oversize 1:/# bs2int_nil divz_small //.
split; first by apply bs2int_ge0.
move=> _; move: (bs2int_le2Xs bs).
by move: (ler_weexpn2l 2 _ (size bs) k _); smt(size_ge0).
qed.



lemma chunk0 ['a] n (l: 'a list):
 size l < n =>
 chunk n l = [].
proof.
move=> Hl; rewrite /chunk divz_small; smt(size_ge0 mkseq0).
qed.

(* chunk1 => chunk_size *)
lemma chunk_size ['a] r (l: 'a list):
 0 < r =>
 size l = r =>
 chunk r l = [l].
proof.
move=> Hr Hsz; rewrite /chunk Hsz divzz (:r<>0) 1:/# b2i1 /=.
by rewrite /mkseq -iotaredE /= drop0 -Hsz take_size.
qed.

lemma behead_chunk ['a] n (l:'a list):
 behead (chunk n l) = chunk n (drop n l).
proof.
case: (size l < n).
 move=> ?; rewrite drop_oversize 1:/#.
 rewrite /chunk behead_mkseq.
 rewrite divz_small /=; first smt(size_ge0).
 by rewrite mkseq0_le //= mkseq0.
case: (0 < n); last first.
rewrite -!lezNgt => ??.
 by rewrite drop_le0 // !chunk_le0.
rewrite -lezNgt => ??.
rewrite /chunk behead_mkseq /=.
rewrite size_drop // 1:/# lez_maxr 1:/#.
have ->: (size l - n) %/ n = size l %/ n - 1.
 have ->: size l = (size l - n) + 1*n by ring.
 by rewrite divzMDr /#.
by apply eq_in_mkseq => x Hx /=; rewrite drop_drop /#.
qed.

lemma drop_chunk n k (l: 'a list):
 0 < k =>
 drop n (chunk k l) = chunk k (drop (k*n) l).
proof.
move=> Hk; elim/natind: n l.
 by move=> n Hn l; rewrite !drop_le0 /#.
move=> n Hn IH l; rewrite dropS // IH behead_chunk drop_drop 1,2:/#.
by congr; congr; ring.
qed.

lemma nth_chunk ['a] k (l: 'a list) i:
 0 < k =>
 0 <= i =>
 k*i+k <= size l =>
 nth [] (chunk k l) i =
 take k (drop (k*i) l).
proof. by move=> *; rewrite nth_mkseq // /#. qed.

lemma chunk_take_eq ['a] n (l:'a list):
 0 < n =>
 chunk n l = chunk n (take (size l %/ n * n) l).
proof.
move=> Hn; rewrite /chunk.
have ->: (size (take (size l %/ n * n) l) %/ n) = (size l %/ n).
 rewrite size_take'; first smt(size_ge0).
 by rewrite lez_floor 1:/# /= mulzK 1:/#.
apply eq_in_mkseq => x Hx /=.
rewrite -{1}(cat_take_drop (size l %/ n * n) l).
rewrite drop_cat size_take'; first smt(size_ge0).
rewrite lez_floor 1:/# /= mulzC StdOrder.IntOrder.ltr_pmul2r 1:/#.
move: (Hx); move=> [? ->] /=.
have E: n <= size (drop (x * n) (take (size l %/ n * n) l)).
 rewrite size_drop 1:/# lez_maxr; last first.
  rewrite size_take' 1:/# lez_floor 1:/# /= -Ring.IntID.mulrBl.
  by rewrite -{1}mulz1 {1}mulzC StdOrder.IntOrder.ler_pmul2r // -ltzS /#.
 rewrite size_take' 1:/# lez_floor 1:/# /=.
 smt(size_ge0).
by rewrite take_cat' E.
qed.

lemma map_chunkK ['a] (f:'a list -> 'a list) n bs:
 0 < n =>
 n %| size bs =>
 (forall l, size l=n => f l = l) =>
 flatten (map f (chunk n bs)) = bs.
proof.
move => Hn Hsz Hf.
have [E _]:= (eq_in_map f idfun (chunk n bs)).
rewrite E.
 move=> x Hx; rewrite Hf //.
 by rewrite (in_chunk_size n bs) //.
by rewrite map_id chunkK //.
qed.

op chunkremains ['a] n (bs: 'a list) =
 drop (size bs %/ n * n) bs.

lemma size_chunkremains ['a] n (bs: 'a list):
 size (chunkremains n bs) = size bs %% n.
proof.
rewrite size_drop. smt(size_ge0).
rewrite lez_maxr; first smt(size_ge0).
by rewrite {1}(divz_eq (size bs) n) /#.
qed.

lemma chunkremains_small ['a] n (l: 'a list):
 size l < n =>
 chunkremains n l = l.
proof.
move=> H; rewrite /chunkremains divz_small.
 smt(size_ge0).
by rewrite drop0.
qed.


(** An "extended" version of [chunkK] *)
lemma chunkK' ['a] r (bs: 'a list):
 0 < r =>
 flatten (chunk r bs) ++ chunkremains r bs
 = bs.
proof.
move=> Hr; rewrite chunk_take_eq //.
rewrite chunkK //.
 rewrite size_take; first smt(size_ge0).
 rewrite {2}(divz_eq (size bs) r).
 case: (size bs %% r = 0)=> C; first smt().
 rewrite ifT 1:/#.
 by rewrite dvdz_mull /#.
by rewrite cat_take_drop.
qed.

lemma map_chunkK' ['a] f n (bs: 'a list):
 0 < n =>
 (forall (l : 'a list), size l = n => f l = l) =>
 flatten (map f (chunk n bs)) = take (size bs %/ n * n) bs.
proof.
move=> Hn H; rewrite chunk_take_eq // map_chunkK //.
by rewrite size_take'; smt(size_ge0).
qed.

lemma chunk_cat' ['a] (l1 l2: 'a list) r:
 0 < r =>
 chunk r (l1++l2)
 = chunk r l1 ++ chunk r (chunkremains r l1 ++ l2).
proof.
move=> Hr.
rewrite -{1}(cat_take_drop (size l1 %/ r * r) l1) -catA chunk_cat.
 rewrite size_take; first smt(size_ge0).
 rewrite {2}(divz_eq (size l1) r).
 case: (size l1 %% r = 0)=> C; first smt().
 rewrite ifT 1:/#.
 by rewrite dvdz_mull /#.
by rewrite -chunk_take_eq //.
qed.

(** [chunkpad] used to zero-fill the last chunk *)
op chunkpad ['a] (d:'a) r (l: 'a list) =
 nseq ((-size l)%%r) d.

lemma chunkpad_nil ['a] (d: 'a) r:
 chunkpad d r [] = [].
proof. by rewrite /chunkpad /= nseq0. qed.

lemma size_chunkpad ['a] (d: 'a) r l:
 0 < r =>
 size (chunkpad d r l) = b2i (! r %| size l) * (r - size l %% r).
proof.
move=> Hr.
case: (r %| size l) => [/dvdzE|] C.
 by rewrite /chunkpad /size_cat size_nseq ler_maxr 1:/# b2i0 -modzNm C.
rewrite size_nseq ler_maxr ?b2i1 /=; first smt(size_ge0).
by rewrite -modzNm -modzDl modz_small /#.
qed.

lemma chunkpadE ['a] (d: 'a) r l:
 0 < r => 
 chunkpad d r l = if r %| size l then [] else nseq (r - size l %% r) d.
proof.
move=> Hr. 
case: (r %| size l) => [/dvdzE|] C.
 by rewrite /chunkpad /= -modzNm C /= nseq0.
by rewrite /chunkpad /= -modzNm -modzDl modz_small /#.
qed.


(** [chunkfill] zero-fills the last chunk *)
op chunkfill ['a] (d: 'a) r l =
 l ++ chunkpad d r l.

lemma size_chunkfill ['a] (d: 'a) r l:
 0 < r =>
 size (chunkfill d r l) = size l %/ r * r + b2i (! r %| size l) * r.
proof.
move=> Hr; rewrite /chunkfill size_cat size_chunkpad //.
case: (r %| size l) => C /=.
 by rewrite b2i0 /= divzK.
by rewrite b2i1 {1}(divz_eq (size l) r) /#.
qed.

lemma chunkfill_nil ['a] (d: 'a) r:
 chunkfill d r [] = [].
proof. by rewrite /chunkfill /chunkpad /= nseq0. qed.

lemma chunkfillP ['a] (d: 'a) r l:
 0 < r =>
 r %| size (chunkfill d r l).
proof.
move=> Hr; rewrite size_chunkfill //.
case: (r %| size l) => C /=; first smt().
by rewrite b2i1 /= dvdzD /#.
qed.

lemma chunkfillE ['a] (d: 'a) r l:
 0 < r =>
 chunkfill d r l = if r %| size l then l else l ++ chunkpad d r l.
proof.
move=> Hr; rewrite /chunkfill chunkpadE //; smt(cats0).
qed.

(** [chunkify] is a version of [chunk] that allows the existence
 of an incomplete chunk at the end of the list *)
(*
op chunkify ['a] d r (bs: 'a list) =
 chunk r (chunkfill d r bs).
*)
op chunkify ['a] r (bs: 'a list) =
 mkseq (fun (i : int) => take r (drop (r * i) bs))
       (size bs %/ r + b2i (! r %| size bs)).

lemma chunkifyE ['a] r (bs: 'a list):
 0 < r =>
 chunkify r bs
 = chunk r bs ++ if r %| size bs then [] else [chunkremains r bs].
proof.
move=> Hr; rewrite /chunkify; case: (r %| size bs) => C.
 by rewrite b2i0 cats0.
rewrite b2i1 mkseqS; first smt(size_ge0).
rewrite cats1; congr => //=.
rewrite /chunkremains take_oversize.
 by rewrite size_drop; smt(size_ge0).
smt().
qed.

lemma chunkify_chunk ['a] n (bs: 'a list):
 0 < n =>
 n %| size bs =>
 chunkify n bs = chunk n bs.
proof.
move=> Hn Hsz.
by rewrite chunkifyE // Hsz /= cats0.
qed.

lemma chunkify_cat ['a] n (l1 l2: 'a list):
 0 < n =>
 n %| size l1 =>
 chunkify n (l1++l2) = chunkify n l1 ++ chunkify n l2.
proof.
move => Hn Hsz.
rewrite (chunkify_chunk _ l1) // chunkifyE // chunk_cat // -!catA; congr.
rewrite chunkifyE; case: (n %| size l2) => // C.
 rewrite size_cat ifT /= ?cats0 //; smt(dvdzD).
 rewrite size_cat.
 rewrite ifF.
 move: C; apply contra; smt(dvdzB).
rewrite /chunkremains size_cat; congr.
have ->: (size l1 + size l2)%/ n * n
         = size l1 + size l2 %/ n * n.
 by rewrite divzDl // /#.
by rewrite drop_cat ifF; smt(size_ge0).
qed.

lemma chunkify_nil ['a] n: chunkify <:'a> n [] = [].
by rewrite /chunkify mkseq0. qed.

lemma chunkify_cons ['a] n (l: 'a list):
 0 < n =>
 0 < size l =>
 chunkify n l = take n l :: chunkify n (drop n l).
proof.
move => n_gt0 Hsz0.
 rewrite -{1}(cat_take_drop n l).
case: (size l < n) => Hsz.
 by rewrite !drop_oversize 1:/# cats0 take_oversize 1:/# chunkify_nil chunkifyE // chunk0 /#.
rewrite chunkify_cat ?size_take' 1..3:/# chunkify_chunk // ?size_take' 1..2:/# chunk_size 1:/#. 
 by rewrite size_take' /#.
smt().
qed.

lemma size_chunkify ['a] n (bs: 'a list):
 0 < n =>
 size (chunkify n bs)
 = size bs %/ n + b2i (! n %| size bs).
proof.
by move=> Hn; rewrite /chunkify size_mkseq; smt(size_ge0). 
qed.

lemma nth_chunkify ['a] n (bs: 'a list) (i: int):
 0 < n =>
 0 <= i =>
 nth [] (chunkify n bs) i = take n (drop (n*i) bs).
proof.
move=> Hn Hi.
case: (i < size bs %/ n + b2i (! n %| size bs)) => C.
 by rewrite nth_mkseq //=.
rewrite nth_out ?size_chunkify // 1:/#. 
rewrite drop_oversize ?take_nil //.
rewrite (divz_eq (size bs) n); move: C; case: (n %| size bs).
 by rewrite b2i0 /= => /dvdzE -> C2 /#.
by rewrite b2i1 /= => C1 C2 /#.
qed.

lemma take_chunkify ['a] n (bs: 'a list) k:
 0 < n =>
 take k (chunkify n bs) = chunkify n (take (n*k) bs).
proof.
move=> n_gt0; rewrite -{1}(cat_take_drop (n*k) bs).
case: (0 <= n*k) => Hsz0; last first. 
 by rewrite !take_le0 1..2:/# /chunkify /= mkseq0_le //.
case: (n*k <= size bs) => E.
 rewrite chunkify_cat //.
  by rewrite size_take' 1:/# E /= dvdz_mulr dvdzz. 
 rewrite take_cat' !size_chunkify // size_take' // !E /= ifT. 
  by rewrite (:n %| n * k); smt(dvdz_mulr dvdzz). 
 rewrite take_oversize // size_chunkify // !size_take' // E /=.
 by rewrite dvdz_mulr ?dvdzz /= b2i0 /#.
rewrite drop_oversize 1:/# cats0 take_oversize //.
by rewrite size_chunkify // size_take' /#.
qed.

lemma drop_chunkify ['a] n (bs: 'a list) k:
 0 < n =>
 drop k (chunkify n bs) = chunkify n (drop (n*k) bs).
proof.
move => n_gt0; elim/natind: k bs => //=.
 by move=> k Hk l; rewrite !drop_le0 // /#.
move=> k Hk IH l.
rewrite -drop_drop //.
move: l => [|x xs] //.
 by rewrite /chunkify //= mkseq0_le.
rewrite {1}(chunkify_cons _ (x::xs) _) /= 1:/#; first smt(size_ge0).
rewrite drop0 (:! n * (k + 1) <= 0) 1:/# /= IH ifF 1:/# drop_drop 1..2:/#.
by congr; congr; ring.
qed.

lemma divz_minus1 m d:
 0 < d => 0 <= m => ! d %| m => (m-1) %/ d = m %/ d.
proof.
move=> Hd Hm Hdvd.
rewrite {1}(divz_eq m d) -addzA divzMDl 1:/#; ring.
rewrite divz_small //; apply JUtils.bound_abs; split.
 by move: Hdvd; rewrite dvdzE; smt(JUtils.modz_cmp).
by move=> ?; smt(JUtils.modz_cmp).
qed.

(** an alternative definition (normally not as usefull) for
 the size of chunkify *)
lemma sizechunkifyE n bslen:
 0 < n =>
 0 <= bslen =>
 bslen %/ n + b2i (! n %| bslen)
 = (bslen - 1) %/ n + 1.
proof.
move=> Hn Hsz.
case: (n %| bslen) => [/dvdzE C|C].
 by rewrite b2i0 /= /#.
by rewrite divz_minus1 //.
qed.

(*
(** [chunkfill] - zero-fill of a (partial) chunk *)
op chunkfill ['a] (d: 'a) n bs =
 take n (bs ++ nseq n d). 

lemma chunkfillE ['a] (d: 'a) n bs:
 chunkfill d n bs = if size bs < n then bs ++ nseq (n-size bs) d else take n bs.
proof.
rewrite /chunkfill; case: (size bs < n) => C.
 by rewrite take_cat' ifF 1:/# take_nseq ler_minl; smt(size_ge0).
by rewrite take_cat' ifT 1:/#.
qed.

lemma size_chunkfill ['a] (d: 'a) n bs:
 0 < n =>
 size (chunkfill d n bs) = n.
proof.
by move=> Hn; rewrite /chunkfill size_take' 1:/# !size_cat size_nseq ifT; smt(size_ge0).
qed.

(** [chunkify_fillsuffix] - zero-suffix that fills the last chunk *)
op chunkify_fillsuffix ['a] (d:'a) n sz =
 nseq (b2i (! n %| sz) * (n - sz %% n)) d.
*)


(*
lemma chunk_truncsize ['a] r (bs: 'a list):
 0 < r =>
 chunk r bs = chunk r (take (size bs %/ r * r) bs).
proof.
move=> Hr; rewrite /chunk size_take'; first smt(size_ge0).
rewrite ifT; first smt(size_ge0). 
rewrite mulzK 1:/#; apply eq_in_mkseq => i Hi /=.
rewrite drop_take 1:/# take_take; congr.
by rewrite lez_minl /#.
qed.
*)

lemma chunkpad_drop ['a] d r n (l: 'a list):
 0 < r =>
 0 <= n*r < size l =>
 chunkpad d r (drop (n*r) l) = chunkpad d r l.
proof.
move=> Hr Hn; rewrite !chunkpadE //.
 rewrite size_drop 1:/# lez_maxr 1:/#.
case: (r %| size l) => C.
 rewrite ifT //.
 by apply dvdzB => /#.
rewrite ifF //.
move: C; apply contra => H.
 by rewrite (:size l = size l - n*r + n*r) 1:/# dvdzD /#.
congr. 
by rewrite -modzBm modzMl /= modz_mod.
qed.

lemma map_chunkifyK ['a] d (f:'a list -> 'a list) n bs:
 0 < n =>
 (forall l, 0 < size l <= n => f l = chunkfill d n l) =>
 flatten (map f (chunkify n bs))
 = chunkfill d n bs.
proof.
move => Hn Hf; rewrite chunkifyE // chunkfillE // map_cat flatten_cat.
case: (n %| size bs) => C /=.
 rewrite flatten_nil cats0.
 apply map_chunkK => //.
 by move=> l Hl; rewrite Hf 1:/# chunkfillE // Hl dvdzz.
rewrite map_chunkK' //.
 by move=> l Hl; rewrite Hf 1:/# chunkfillE // ifT 1:/#.
rewrite flatten_seq1 Hf.
 by rewrite size_chunkremains /#.
rewrite /chunkfill catA /chunkremains cat_take_drop; congr.
rewrite chunkpad_drop //; smt(size_ge0).
qed.

(*
op chunkfillsize (n sz:int) = (-sz)%%n.

lemma chunkfillsize_cmp n sz:
 0 < n => 0 <= chunkfillsize n sz < n.
proof. move=> Hn; rewrite /chunkfillsize; smt(JUtils.modz_cmp). qed.

lemma chunkfillsizeP n sz k:
 0 < n => chunkfillsize n (n*k+sz) = chunkfillsize n sz.
proof.
move=> Hn; rewrite /chunkfillsize.
by rewrite -modzNm mulzC modzMDl modzNm.
qed.

lemma chunkfillsizeE' n sz:
 0 < n => 0 < sz => chunkfillsize n sz = n - 1 - (sz-1) %% n
by move=> ??; rewrite /chunkfillsize modNz.

lemma chunkfillsizeE n sz:
 0 < n => 0 <= sz => chunkfillsize n sz = if n %| sz then 0 else n - sz%%n.
proof.
move=> Hn Hsz'.
case: (n %| sz) .
 rewrite /chunkfillsize dvdzE -modzNm => ->; smt().
move=> ?.
have Hsz : 0 < sz by smt(dvdz0).
rewrite chunkfillsizeE' //. 
have ->: n - 1 - (sz - 1) %% n = n - (1 + (sz - 1) %% n) by ring.
congr; congr.
by rewrite !modzE divz_minus1 //; ring.
qed.

op chunkfill ['a] (d:'a) n l = l ++ nseq (chunkfillsize n (size l)) d.

lemma chunkfill_nil ['a] (d:'a) n:
 chunkfill d n [] = [].
proof. by rewrite /chunkfill /chunkfillsize nseq0. qed.

hint simplify chunkfill_nil.

lemma dvd_chunkfill ['a] (d:'a) n l:
 0 < n => n %| size l => chunkfill d n l = l.
proof.
by move=> Hn Hsz; rewrite /chunkfill chunkfillsizeE // ?size_ge0 !Hsz /= nseq0 cats0.
qed.

lemma size_chunkfill ['a] (d:'a) n l:
 0 < n =>
 size (chunkfill d n l) = (size l - 1) %/ n * n + n.
proof.
move=> Hn; rewrite /chunkfill size_cat size_nseq lez_maxr //.
 smt(chunkfillsize_cmp).
case: (size l = 0) => E.
 by rewrite !E /= /chunkfillsize /= divNz //=; ring.
rewrite chunkfillsizeE' //; first smt(size_ge0).
have ->: size l + (n - 1 - (size l - 1) %% n) = (size l-1) + n - (size l-1) %% n
 by ring.
by rewrite {1}(divz_eq (size l - 1) n); ring.
qed.

lemma chunkfillP ['a] (d:'a) n l:
 0 < n =>
 n %| size (chunkfill d n l).
proof.
move=> Hn; rewrite size_chunkfill //.
rewrite (: (size l - 1) %/ n * n + n = ((size l - 1) %/ n + 1) * n) 1:/#.
by rewrite dvdzE modzMl.
qed.

lemma chunkfillK ['a] (d:'a) n l:
 0 < n =>
 chunkfill d n (chunkfill d n l) = chunkfill d n l.
proof.
move=> Hn; rewrite {1}/chunkfill chunkfillsizeE // ?size_ge0.
by rewrite !chunkfillP //= nseq0 cats0.
qed.

lemma chunkfill_cat (d:'a) n l1 l2:
 0 < n => n %| size l1 => chunkfill d n (l1++l2) = l1 ++ chunkfill d n l2.
proof.
move=> H0 Hsz; rewrite /chunkfill -!catA; congr; congr; congr.
move: Hsz; rewrite size_cat dvdzP => [[k]].
rewrite mulzC => ->.
by rewrite chunkfillsizeP.
qed.

lemma chunkfillK' l (d:'a) n:
 0 < n => n %| size l => chunkfill d n l = l.
proof.
rewrite /chunkfill => Hn Hsz.
move: (Hsz); rewrite dvdzP => [[k E]].
by rewrite chunkfillsizeE // ifT 1:/# nseq0 cats0.
qed.

lemma chunkfillsize_ge0 k n: 0 < k => 0 <= chunkfillsize k n.
proof.  by rewrite /chunkfillsize /#. qed.

lemma drop_chunkfill n (d:'a) k l:
 0 < k => 0 <= n =>
 drop (k*n) (chunkfill d k l) = chunkfill d k (drop (k*n) (chunkfill d k l)).
proof.
move=> Hk Hn; have := chunkfillP d k l Hk.
rewrite /chunkfill size_cat size_nseq lez_maxr; first smt(chunkfillsize_ge0).
move=> Hdvd; pose S:= chunkfillsize _ (size (drop _ _)).
have ->: S = 0; last by rewrite nseq0 cats0.
rewrite /S -(chunkfillsizeP _ _ n) // size_drop 1:/# addzC /max size_cat size_nseq. 
rewrite lez_maxr; first by apply chunkfillsize_ge0.
case: (0 < size l + chunkfillsize k (size l) - k * n) => E.
 rewrite Ring.IntID.subrK chunkfillsizeE; first 2 smt(size_ge0 chunkfillsize_ge0).
 by rewrite !Hdvd.
by rewrite addzC chunkfillsizeP.
qed.

lemma nth_chunkfill k (d:'a) n l:
 0 < n => nth d (chunkfill d n l) k = nth d l k.
proof.
move=> Hn; rewrite /chunkfill nth_cat.
case: (k < size l) => E //.
case: (0 <= k - size l < chunkfillsize n (size l)) => ?.
 by rewrite nth_nseq // nth_out /#.
rewrite nth_out.
 by rewrite size_nseq lez_maxr // chunkfillsize_ge0. 
by rewrite nth_out /#.
qed.

lemma size_chunkfilled (d:'a) k l:
 0 < k =>
 size (BitEncoding.BitChunking.chunk k (chunkfill d k l))
 = (size l - 1) %/ k + 1.
proof.
move=> Hk; rewrite BitEncoding.BitChunking.size_chunk //.
by rewrite size_chunkfill // divzMDl 1:/# divzz (:k<>0) 1:/#.
qed.

lemma head_chunkfilled (d:'a) k l:
 head [] (BitEncoding.BitChunking.chunk k (chunkfill d k l))
 = take k (chunkfill d k l).
proof.
case: (0 < k) => Hk; last first.
 by rewrite take_le0 1:/# BitEncoding.BitChunking.chunk_le0 1:/#.
case: (0 < size l) => Hsz; last first.
 have ->: l=[] by smt(size_ge0).
 by rewrite chunkfill_nil /= /BitEncoding.BitChunking.chunk /= mkseq0.
rewrite -nth0 /BitEncoding.BitChunking.chunk nth_mkseq /=.
 by rewrite size_chunkfill // /#.
by rewrite drop0.
qed.

lemma nth_chunkfilled (d:'a) k l (i:int):
 0 < k =>
 0 <= i < (size l - 1) %/ k + 1 =>
 nth [] (BitEncoding.BitChunking.chunk k (chunkfill d k l)) i
 = take k (drop (k*i) (chunkfill d k l)).
proof.
move=> Hk Hi.
rewrite {1}(:i = i+0) // -nth_drop 1,2:/# drop_chunk // nth0.
by rewrite drop_chunkfill // 1:/# head_chunkfilled.
qed.

lemma nth_chunkfilled' dl (d:'a) k l (i:int):
 0 < k =>
 0 <= i < (size l - 1) %/ k + 1 =>
 nth dl (BitEncoding.BitChunking.chunk k (chunkfill d k l)) i
 = mkseq (fun j => nth d l (k*i+j)) k.
proof.
move=> Hk Hi.
rewrite -(nth_inside []); first by rewrite size_chunkfilled.
rewrite (nth_chunkfilled d k l i) //.
have Hsz: size (take k (drop (k * i) (chunkfill d k l))) = k.
 rewrite size_take' 1:/# size_drop 1:/# size_chunkfill //.
 rewrite lez_maxr; first smt(size_ge0).
 have: k <= (size l - 1) %/ k * k + k - k * i.
  by move: Hi => [?]; rewrite ltzE => [?] /#.
 smt().
apply (eq_from_nth d); first by rewrite Hsz size_mkseq /#.
rewrite Hsz => j Hj.
rewrite nth_take 1,2:/# nth_drop 1,2:/# nth_chunkfill 1:/#.
by rewrite nth_mkseq.
qed.
*)


(* END-MOVE THIS??? *)

abstract theory ListEmbedding.

(* instantiate this... *)
type SSS.
type TTT.
op n: int.
op dSSS: SSS.
op dTTT: TTT.
op SSS_to_TTTs: SSS -> TTT list.
op SSS_from_TTTs: TTT list -> SSS.

(* ...and provide these proofs *)
axiom n_gt0: 0 < n.
axiom size_SSS_to_TTTs x: size (SSS_to_TTTs x) = n.
axiom SSS_to_TTTs_inj: injective SSS_to_TTTs.
axiom SSS_to_TTTsK x: SSS_from_TTTs (SSS_to_TTTs x) = x.
axiom SSS_to_TTTs_nil: SSS_to_TTTs dSSS = nseq n dTTT.
axiom SSS_from_TTTsK l:
 size l <= n =>
 SSS_to_TTTs (SSS_from_TTTs l) = l ++ nseq (n-size l) dTTT.
axiom SSS_from_TTTs_nil: SSS_from_TTTs [] = dSSS.

(* list embeddings and some facts *)
op SSSs_to_TTTs (l: SSS list): TTT list =
 flatten (map SSS_to_TTTs l).
op SSSs_from_TTTs (l: TTT list): SSS list =
 map SSS_from_TTTs (chunkify n l).

lemma SSSs_to_TTTs_nil: SSSs_to_TTTs [] = [] by done.

lemma SSSs_to_TTTs_cons x xs:
 SSSs_to_TTTs (x::xs)
 = (SSS_to_TTTs x) ++ SSSs_to_TTTs xs by done.

lemma SSSs_to_TTTs_cat l1 l2:
 SSSs_to_TTTs (l1++l2)
 = SSSs_to_TTTs l1 ++ SSSs_to_TTTs l2.
proof. by elim: l1 => //= x xs IH; rewrite !SSSs_to_TTTs_cons IH catA. qed.

lemma size_SSSs_to_TTTs l:
 size (SSSs_to_TTTs l) = n*size l.
proof.
rewrite /SSSs_to_TTTs (size_flatten' n).
 by move=> x /mapP [Hx ->]; rewrite size_SSS_to_TTTs.
by rewrite size_map.
qed.

lemma SSSs_to_TTTs_flatten ll:
 SSSs_to_TTTs (flatten ll)
 = flatten (map SSSs_to_TTTs ll).
proof.
elim ll => //= x xs IH.
by rewrite !flatten_cons SSSs_to_TTTs_cat IH.
qed.

lemma SSSs_to_TTTs_inj: injective SSSs_to_TTTs.
proof.
rewrite /SSSs_to_TTTs; elim.
 move=> [|y ys] //=.
 rewrite flatten_nil flatten_cons.
 rewrite eq_sym -size_eq0 size_cat size_SSS_to_TTTs.
 smt(n_gt0 size_ge0).
move=> x xs IH; elim => //=.
 rewrite flatten_nil flatten_cons -size_eq0 size_cat size_SSS_to_TTTs.
 smt(n_gt0 size_ge0).
move=> y ys IH2.
rewrite !flatten_cons eqseq_cat ?size_SSS_to_TTTs //=; move => [/SSS_to_TTTs_inj -> /= ?].
by apply IH.
qed.

lemma SSS_from_TTTs_nseq0 k:
 0 <= k <= n =>
 SSS_from_TTTs (nseq k dTTT) = dSSS.
proof.
move=> Hk; apply SSS_to_TTTs_inj.
rewrite SSS_to_TTTs_nil SSS_from_TTTsK ?size_nseq 1:/# ler_maxr 1:/#.
by rewrite cat_nseq /#.
qed.

lemma SSSs_from_TTTs_nil: SSSs_from_TTTs [] = [].
proof. by rewrite /SSSs_from_TTTs chunkify_nil. qed.

lemma SSSs_from_TTTs_cat l1 l2:
 n %| size l1 =>
 SSSs_from_TTTs (l1++l2)
 = SSSs_from_TTTs l1 ++ SSSs_from_TTTs l2.
proof. by move=> Hsz; rewrite /SSSs_from_TTTs chunkify_cat ?n_gt0 // !map_cat. qed.

lemma SSSs_from_TTTs_nseq0 k:
 0 <= k =>
 SSSs_from_TTTs (nseq k dTTT) = nseq (k %/ n + b2i (! n %| k)) dSSS.
proof.
have n_gt0:= n_gt0.
move=> Hk.
have L: forall k',
 0 <= k' => n %| k' =>
 SSSs_from_TTTs (nseq k' dTTT) = nseq (k' %/ n) dSSS.
 move=> k' Hk0' Hk'; rewrite -{1}(divzK n k') //.
 have: (0 <= k' %/ n) by smt().
 move: (k' %/ n); elim/natind => //=.
  move=> n' ??; have ->/=: n'=0 by smt().  
  by rewrite !nseq0 SSSs_from_TTTs_nil.
 move=> Hn Hn' IH _.
 rewrite Ring.IntID.mulrSl -cat_nseq 1..2:/#.
 rewrite SSSs_from_TTTs_cat.
  by rewrite size_nseq /#.
 rewrite IH 1:/# -!cat_nseq 1..2:/# nseq1; congr.
 rewrite /SSSs_from_TTTs chunkifyE 1:/#.
 rewrite size_nseq ler_maxr 1:/# dvdzz /=.
 rewrite map_cat /= cats0 chunk_size 1:/#.
  by rewrite size_nseq /#.
 by rewrite /= SSS_from_TTTs_nseq0 /#.
rewrite {1}(divz_eq k n) -cat_nseq 1..2:/#.
rewrite SSSs_from_TTTs_cat.
 by rewrite size_nseq /#.
rewrite -cat_nseq 1..2:/# L 1..2:/#; congr.
 smt().
rewrite dvdzE.
case: (k %% n = 0) => C/=.
 by rewrite C b2i0 !nseq0 SSSs_from_TTTs_nil.
rewrite b2i1 nseq1.
rewrite /SSSs_from_TTTs chunkifyE 1:/#.
rewrite size_nseq ler_maxr 1:/# chunk0 /=.
 by rewrite size_nseq /#.
rewrite ifF 1:/# /= chunkremains_small.
 by rewrite size_nseq /#.
by rewrite SSS_from_TTTs_nseq0 /#.
qed.

lemma SSSs_to_TTTs_take k l:
 SSSs_to_TTTs (take k l)
 = take (n*k) (SSSs_to_TTTs l).
proof.
elim/natind: k l => //=.
 move=> k Hk l; rewrite !take_le0 //.
 by apply StdOrder.IntOrder.mulr_ge0_le0; smt(n_gt0).
move=> k Hk IH [|x xs] //=.
have ->/=: ! (k+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !SSSs_to_TTTs_cons take_cat.
have ->/=: ! (n * (k + 1) < size (SSS_to_TTTs x)).
 by rewrite size_SSS_to_TTTs; smt(n_gt0).
by rewrite mulzDr /= IH size_SSS_to_TTTs /#.
qed.

lemma SSSs_to_TTTs_drop k l:
 SSSs_to_TTTs (drop k l)
 = drop (n*k) (SSSs_to_TTTs l).
proof.
elim/natind: k l => //=.
 move=> k Hk l; rewrite !drop_le0 //.
 smt(n_gt0).
move=> k Hk IH [|x xs] //=.
have ->/=: ! (k+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !SSSs_to_TTTs_cons drop_cat.
have ->/=: ! (n * (k + 1) < size (SSS_to_TTTs x)).
 by rewrite size_SSS_to_TTTs; smt(n_gt0).
by rewrite mulzDr /= IH size_SSS_to_TTTs /#.
qed.

lemma chunk_SSSs_to_TTTs r l:
 chunk (n*r) (SSSs_to_TTTs l)
 = map SSSs_to_TTTs (chunk r l).
proof.
have n_gt0:= n_gt0.
rewrite /chunk map_mkseq /(\o) /=.
rewrite size_SSSs_to_TTTs divzMpl 1:/#.
apply eq_mkseq => x /=.
by rewrite SSSs_to_TTTs_take SSSs_to_TTTs_drop /#.
qed.

lemma SSSs_to_TTTs_map2 fS' fT' l1 l2:
 (forall x1 x2, SSS_to_TTTs (fS' x1 x2)
 = map2 fT' (SSS_to_TTTs x1) (SSS_to_TTTs x2)) =>
 SSSs_to_TTTs (JUtils.map2 fS' l1 l2)
 = map2 fT' (SSSs_to_TTTs l1) (SSSs_to_TTTs l2).
proof.
move => Hfg.
elim: l2 l1 => //=.
 by move=> [|x xs]; rewrite SSSs_to_TTTs_nil // SSSs_to_TTTs_cons /= map2_nilr /#.
move=> y ys IH1; elim => //=.
 by rewrite SSSs_to_TTTs_cons /SSSs_to_TTTs flatten_nil map2_nill.
move=> x xs IH2.
rewrite !SSSs_to_TTTs_cons map2_cat.
 by rewrite !size_SSS_to_TTTs.
rewrite IH1; congr.
by apply Hfg.
qed.


lemma SSSs_from_TTTs_cons l:
 0 < size l =>
 SSSs_from_TTTs l = SSS_from_TTTs (take n l) :: SSSs_from_TTTs (drop n l).
proof.
move: n_gt0 => n_gt0 Hsz0.
by rewrite /SSSs_from_TTTs chunkify_cons //.
qed.

lemma size_SSSs_from_TTTs l:
 size (SSSs_from_TTTs l)
 = size l %/ n + b2i (! n %| size l).
proof.
rewrite /gL size_map size_chunkify //.
by apply n_gt0.
qed.

lemma SSSs_from_TTTsK l:
 SSSs_to_TTTs (SSSs_from_TTTs l)
 = chunkfill dTTT n l.
proof.
rewrite /SSSs_to_TTTs /SSSs_from_TTTs -map_comp.
apply map_chunkifyK; first exact n_gt0.
move=> xs [Hxs0 Hxsn]; rewrite /(\o) SSS_from_TTTsK //.
rewrite /chunkfill; congr.
rewrite chunkpadE ?n_gt0 //.
case: (n %| size xs) => C.
 have ->: size xs = n by smt().
 by rewrite /= nseq0.
congr; rewrite modz_small //.
have: !n=size xs by smt(divzz).
smt(size_ge0).
qed.

lemma SSSs_from_TTTsK_dvd l:
 n %| size l => SSSs_to_TTTs (SSSs_from_TTTs l) = l.
proof.
move=> Hn; rewrite /SSSs_from_TTTs chunkify_chunk ?n_gt0 // /SSSs_to_TTTs -map_comp.
apply map_chunkK => //; first exact n_gt0.
by move=> xs Hxs; rewrite /(\o) SSS_from_TTTsK 1:/# Hxs /= nseq0 cats0.
qed.

lemma SSSs_to_TTTsK:
 cancel SSSs_to_TTTs SSSs_from_TTTs.
proof.
move=> k; apply SSSs_to_TTTs_inj.
rewrite SSSs_from_TTTsK_dvd // size_SSSs_to_TTTs dvdz_mulr.
smt(n_gt0).
qed.

lemma SSSs_to_TTTs_nseq0 k:
 SSSs_to_TTTs (nseq k dSSS) = nseq (n*k) dTTT.
proof.
elim/natind: k => /=.
 by move=> k Hk1; rewrite !nseq0_le //; smt(n_gt0).
move=> k Hk IH; rewrite nseqS // SSSs_to_TTTs_cons IH //.
rewrite addzC mulzDr mulz1 -cat_nseq //; first 2 smt(n_gt0).
by rewrite SSS_to_TTTs_nil.
qed.

lemma nth_SSSs_to_TTTs l i:
 0 <= i < n*size l =>
 nth dTTT (SSSs_to_TTTs l) i
 = nth dTTT (SSS_to_TTTs (nth dSSS l (i %/ n))) (i %% n).
proof.
move=> Hi; rewrite /SSSs_to_TTTs (nth_flatten _ n).
 rewrite allP; move=> x /mapP [y [Hy ->]] /=.
 by rewrite size_SSS_to_TTTs.
rewrite (nth_map dSSS) //.
apply divz_cmp => //; first by apply n_gt0.
by rewrite mulzC.
qed.

lemma drop_SSSs_from_TTTs k l:
 drop k (SSSs_from_TTTs l)
 = SSSs_from_TTTs (drop (n*k) l).
proof.
have n_gt0:= n_gt0.
rewrite /SSSs_from_TTTs -map_drop; congr.
by apply drop_chunkify.
qed.

lemma take_SSSs_from_TTTs k l:
 take k (SSSs_from_TTTs l)
 = SSSs_from_TTTs (take (n*k) l).
proof.
have n_gt0 := n_gt0.
rewrite /SSSs_from_TTTs -map_take; congr.
by apply take_chunkify.
qed.

lemma nth_SSSs_from_TTTs l k:
  0 <= k =>
  nth dSSS (SSSs_from_TTTs l) k
  = SSS_from_TTTs (take n (drop (n*k) l)).
proof.
have n_gt0 Hk0 := n_gt0.
rewrite /SSSs_from_TTTs (nth_map' []) /=.
 by rewrite SSS_from_TTTs_nil.
by congr; rewrite nth_chunkify //.
qed.

(*
lemma chunkfill_SSSs_from_TTTs k l:
 0 < k =>
 SSSs_to_TTTs (chunkfill dSSS k (SSSs_from_TTTs l))
 = chunkfill dTTT (n*k) l.
proof.
have n_gt0:= n_gt0; move=> Hk.
rewrite /chunkfill SSSs_to_TTTs_cat SSSs_from_TTTsK /chunkfill -catA; congr.
rewrite !chunkpadE 1..3:/#.
rewrite size_SSSs_from_TTTs.
case: (n * k %| size l) => C1.
 have C1': n %| (n*k) by smt(dvdz_mulr dvdzz).
 have E: (n %| size l) by smt(dvdz_trans).
 rewrite !E !b2i0 /=.
 rewrite ifT.
  move: C1 => /dvdzP [x ->].
  rewrite (mulzC n) -mulzA mulzK 1:/# dvdz_mull dvdzz.
 by rewrite SSSs_to_TTTs_nil.
case: (n %| size l) => C2.
 rewrite b2i0 /= ifF.
  admit.
 rewrite SSSs_to_TTTs_nseq0; congr.
 have ->: size l %% (n*k) = n*((size l%/ n) %% k).
  by rewrite mulz_modr /#.
 smt().
rewrite b2i1.
case: (k %| (size l %/ n + 1)) => C3.
 rewrite SSSs_to_TTTs_nil cats0; congr.
 admit.
rewrite SSSs_to_TTTs_nseq0 cat_nseq 1..2:/#; congr.
admit.
qed.

lemma chunkify_SSSs_from_TTTs k l:
 chunkify k (SSSs_from_TTTs l)
 = map SSSs_from_TTTs (chunkify (k*n) l).
proof.
rewrite /SSSs_from_TTTs /chunkify /=.
print map_comp.
rewrite -map_comp.
rewrite map_mkseq /(\o) /=.
congr.
 apply fun_ext => x.
 rewrite map_mkseq /(\o) /=.
rewrite -/(mkseq (fun (x0 : int) => SSS_from_TTTs (take n (drop (n * x0) l))) (size l %/ n + b2i (! n %| size l))).
rewrite drop_mkseq.
 admit.
rewrite take_mkseq /=.
 admit.
congr.
 apply fun_ext => y.
admit.
admit.

rewrite !size_map !size_iota !lez_maxr.
smt. 
case: (n %| size l) => C1 /=.
 rewrite !b2i0 /=.
 admit.
rewrite !b2i1.
admit.
qed.
*)

end ListEmbedding.

type bit = bool.
type bits = bool list.
type byte = W8.t.
type bytes = W8.t list.

clone export ListEmbedding as Bytes2Bits
 with
 type SSS <- W8.t,
 type TTT <- bool,
 op n <- 8,
 op dSSS <- W8.zero,
 op dTTT <- false,
 op SSS_to_TTTs <- W8.w2bits,
 op SSS_from_TTTs <- W8.bits2w
 rename [op, lemma]
  "SSSs_to_TTTs" as "bytes_to_bits"
  "SSSs_from_TTTs" as "bytes_from_bits"
  "SSS_to_TTTs" as "byte_to_bits"
  "SSS_from_TTTs" as "byte_from_bits"
  "SSSs" as "bytes"
  "SSS" as "byte"
  "TTT" as "bit"
  proof n_gt0 by done
  proof *.
realize size_byte_to_bits by done.
realize byte_to_bits_inj by apply W8.w2bits_inj.
realize byte_to_bitsK by apply W8.w2bitsK.
realize byte_to_bits_nil by rewrite /w2bits -mkseq_nseq /mkseq -iotaredE /=.
realize byte_from_bits_nil by apply W8_bits2w_nil.
realize byte_from_bitsK by apply W8_bits2wK'.

clone export ListEmbedding as W64s2Bits
 with
 type SSS <- W64.t,
 type TTT <- bool,
 op n <- 64,
 op dSSS <- W64.zero,
 op dTTT <- false,
 op SSS_to_TTTs <- W64.w2bits,
 op SSS_from_TTTs <- W64.bits2w
 rename [op, lemma]
  "SSSs_to_TTTs" as "w64L_to_bits"
  "SSSs_from_TTTs" as "w64L_from_bits"
  "SSS_to_TTTs" as "w64_to_bits"
  "SSS_from_TTTs" as "w64_from_bits"
  "SSSs" as "w64L"
  "SSS" as "w64"
  "TTT" as "bit"
  proof n_gt0 by done
  proof *.
realize size_w64_to_bits by done.
realize w64_to_bits_inj by apply W64.w2bits_inj.
realize w64_to_bitsK by apply W64.w2bitsK.
realize w64_to_bits_nil by rewrite /w2bits -mkseq_nseq /mkseq -iotaredE /=.
realize w64_from_bits_nil by apply W64_bits2w_nil.
realize w64_from_bitsK by apply W64_bits2wK'.





clone export ListEmbedding as W64s2Bytes
 with
 type SSS <- W64.t,
 type TTT <- W8.t,
 op n <- 8,
 op dSSS <- W64.zero,
 op dTTT <- W8.zero,
 op SSS_to_TTTs <- W8u8.to_list,
 op SSS_from_TTTs <- W8u8.pack8
 rename [op, lemma]
  "SSSs_to_TTTs" as "w64L_to_bytes"
  "SSSs_from_TTTs" as "w64L_from_bytes"
  "SSS_to_TTTs" as "w64_to_bytes"
  "SSS_from_TTTs" as "w64_from_bytes"
  "SSSs" as "w64L"
  "SSS" as "w64"
  "TTT" as "byte"
  proof n_gt0 by done
  proof *.
realize size_w64_to_bytes by done.
realize w64_to_bytes_inj by apply W8u8_to_list_inj.
realize w64_to_bytesK by apply W8u8_to_listK.
realize w64_to_bytes_nil by rewrite /= !W8u8.get_zero -mkseq_nseq /mkseq -iotaredE /=. 
realize w64_from_bytesK by apply W8u8_to_list_pack8.
realize w64_from_bytes_nil by apply W8u8_pack8_nil.


lemma w64_to_bytes_to_bits w:
 bytes_to_bits (W8u8.to_list w) = W64.w2bits w.
proof.
by rewrite /bytes_to_bits /w2bits /(\bits8) /flatten /mkseq -iotaredE /=.
qed.

lemma w64L_to_bytes_to_bits l:
 bytes_to_bits (w64L_to_bytes l) = w64L_to_bits l.
proof.
elim: l; first by rewrite /w64L_to_bytes /flatten.
move=> x xs IH.
by rewrite /w64L_to_bytes map_cons flatten_cons w64L_to_bits_cons -IH bytes_to_bits_cat  w64_to_bytes_to_bits //. 
qed.

lemma w64L_from_bytes_from_bits l:
 w64L_from_bytes (bytes_from_bits l) = w64L_from_bits l.
proof.
apply w64L_to_bits_inj.
rewrite -w64L_to_bytes_to_bits w64L_from_bytesK w64L_from_bitsK.
rewrite /chunkfill bytes_to_bits_cat bytes_from_bitsK -catA; congr.
rewrite !chunkpadE // size_bytes_from_bits.
case: (64 %| size l) => C1.
 have E: 8 %| size l by smt().
 rewrite !E !b2i0 /=.
 by rewrite ifT 1:/# bytes_to_bits_nil.
case: (8 %| size l) => C2.
 by rewrite b2i0 /= ifF 1:/# bytes_to_bits_nseq0 /#.
rewrite b2i1.
case: (8 %| (size l %/ 8 + 1)) => C3.
 by rewrite bytes_to_bits_nil cats0 /#.
by rewrite bytes_to_bits_nseq0 cat_nseq /#.
qed.

lemma w64_from_bits_from_bytes l:
 W64.bits2w (bytes_to_bits l) = pack8 l.
proof.
rewrite /bytes_to_bits; apply W64.wordP => i Hi.
rewrite get_bits2w // (nth_flatten _ 8).
 by rewrite allP => k /mapP [w [Hw ->]].
rewrite pack8E initiE //= get_of_list 1:/# -get_w2bits.
case: (i %/ 8 < size l) => C.
rewrite (nth_map W8.zero) 1..2:/#.
have ->: nth [] (map W8.w2bits l) (i %/ 8) = [].
 by rewrite nth_out ?size_map /#.
rewrite nth_out ?size_map 1:/#.
have ->: nth W8.zero l (i %/ 8) = W8.zero.
 by rewrite nth_out /#.
by rewrite byte_to_bits_nil nth_nseq 1:/#.
qed.

lemma w64L_from_bits_from_bytes l:
 w64L_from_bits (bytes_to_bits l) = w64L_from_bytes l.
proof.
apply (eq_from_nth W64.zero); rewrite size_w64L_from_bits size_bytes_to_bits.
 by rewrite size_w64L_from_bytes /#.
move=> i Hi.
rewrite nth_w64L_from_bits 1:/#.
rewrite (:64*i=8*(8*i)) 1:/# -bytes_to_bits_drop (:64=8*8) 1:/#.
rewrite -bytes_to_bits_take nth_w64L_from_bytes 1:/#.
by rewrite w64_from_bits_from_bytes.
qed.

(*
(*******************************************************************************)
(*                             W8 lists (aka "bytes")                          *)
(*******************************************************************************)

type bits = bool list.
type bytes = W8.t list.

op bytes2bits (l: bytes) : bits =
 flatten (map W8.w2bits l).

lemma bytes2bits_nil: bytes2bits [] = [] by done.

hint simplify bytes2bits_nil.

lemma bytes2bits_cons x xs:
 bytes2bits (x::xs) = W8.w2bits x ++ bytes2bits xs.
proof. by rewrite /bytes2bits map_cons flatten_cons. qed.

lemma bytes2bits_cat l1 l2:
 bytes2bits (l1++l2) = bytes2bits l1 ++ bytes2bits l2.
proof. by elim: l1 => //= x xs IH; rewrite !bytes2bits_cons IH catA. qed.

lemma size_bytes2bits x:
 size (bytes2bits x) = 8 * size x.
proof.
by rewrite /bytes2bits size_flatten -map_comp /(\o) /= StdBigop.Bigint.sumzE
StdBigop.Bigint.BIA.big_mapT /(\o) /= StdBigop.Bigint.big_constz count_predT_eq.
qed.

(*hint simplify size_bytes2bits.*)

lemma take_bytes2bits n l:
 take (8*n) (bytes2bits l) = bytes2bits (take n l).
proof.
elim/natind: n l => //=.
 move=> n Hn l; rewrite !take_le0 //.
 by apply StdOrder.IntOrder.mulr_ge0_le0.
move=> n Hn IH [|x xs] //=.
have ->/=: ! (n+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !bytes2bits_cons take_cat.
have ->/=: ! (8 * (n + 1) < size (w2bits x)) by rewrite W8.size_w2bits /#.
by rewrite mulzDr /= IH.
qed.

lemma drop_bytes2bits n l:
 drop (8*n) (bytes2bits l) = bytes2bits (drop n l).
proof.
elim/natind: n l => //=.
 move=> n Hn l; rewrite !drop_le0 //.
 by apply StdOrder.IntOrder.mulr_ge0_le0.
move=> n Hn IH [|x xs] //=.
have ->/=: ! (n+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !bytes2bits_cons drop_cat.
have ->/=: ! (8 * (n + 1) < size (w2bits x)) by rewrite W8.size_w2bits /#.
by rewrite mulzDr /= IH.
qed.

lemma bytes2bits_u64 w: bytes2bits (W8u8.to_list w) = W64.w2bits w.
proof.
by rewrite /bytes2bits /w2bits /(\bits8) /flatten /mkseq -iotaredE /=.
qed.

op bits2bytes (bs: bits) : bytes =
 map W8.bits2w (chunkify 8 bs).

lemma bits2bytes_nil: bits2bytes [] = [].
proof. by rewrite /bits2bytes /chunkify /chunk /= mkseq0. qed.

hint simplify bits2bytes_nil.

lemma size_bits2bytes bs:
 size (bits2bytes bs)
 = size bs %/ 8 + b2i (! 8 %| size bs).
proof. by rewrite /bits2bytes size_map size_chunkify //. qed.

lemma bits2bytesK bs:
 8 %| size bs => bytes2bits (bits2bytes bs) = bs.
proof.
move=> Hsz; rewrite /bytes2bits /bits2bytes chunkify_chunk //.
rewrite -map_comp map_chunkK //.
by move=> l Hl; rewrite /(\o) bits2wK //.
qed.

lemma bits2bytesK' bs:
 bytes2bits (bits2bytes bs)
 = bs ++ chunkfill bs 8 false.
proof.
rewrite /bytes2bits /bits2bytes -map_comp.
apply map_chunkifyK => //.
move=> l Hl @/(\o).
case: (size l = 8) => C.
 by rewrite bits2wK // take_size_cat //.
rewrite -(W8_bits2w_cat_nseq0 l (8-size l)). 
rewrite bits2wK ?size_cat ?size_nseq 1:/# take_cat ifF 1:/# take_nseq lez_minl //.
smt(size_ge0).
qed.

lemma bytes2bits_inj: injective bytes2bits.
proof.
rewrite /bytes2bits; elim.
 move=> [|y ys] //=.
 rewrite flatten_nil flatten_cons.
 rewrite eq_sym -size_eq0 size_cat size_w2bits.
 smt(size_ge0).
move=> x xs IH; elim => //=.
 rewrite flatten_nil flatten_cons -size_eq0 size_cat size_w2bits.
 smt(size_ge0).
move=> y ys IH2.
rewrite !flatten_cons eqseq_cat //=; move => [/W8.w2bits_inj -> /= ?].
by apply IH.
qed.

lemma bytes2bitsK: cancel bytes2bits bits2bytes.
proof.
move=> k. apply bytes2bits_inj.
by rewrite bits2bytesK // size_bytes2bits dvdz_mulr.
qed.

(*
lemma bytes2bits_xor' l1 l2:
 JUtils.map2 W8.(`^`) l1 l2
 = bits2w8L (map2 Bool.(^^) (bytes2bits l1) (bytes2bits l2)).
proof.
admit.
qed.
*)

from Jasmin require import JUtils.

lemma bytes2bits_xor l1 l2:
 bytes2bits (JUtils.map2 W8.(`^`) l1 l2)
 = map2 Bool.(^^) (bytes2bits l1) (bytes2bits l2).
proof.
elim: l1 l2 => //=.
 move=> [|y ys]; rewrite bytes2bits_nil // bytes2bits_cons.
 by rewrite map2C /= /#.
move=> x xs IH1; elim => //=.
 rewrite map2C; first by move=> b1 b2; ring.
 by rewrite bytes2bits_cons map2C /= /#.
move=> y ys IH2.
rewrite !bytes2bits_cons map2_cat.
 by rewrite !size_w2bits.
rewrite IH1; congr.
by rewrite W8.xorE map2_w2bits_w2bits.
(*
rewrite bytes2bits_xor' bits2w8LK //.
rewrite size_map2 !size_bytes2bits /#.
*)
qed.

lemma bytes2bits_nseq0 n:
 0 <= n =>
 bytes2bits (nseq n W8.zero) = nseq (8*n) false.
proof.
elim/natind: n => /=.
 by move=> n Hn1 Hn2; rewrite !nseq0_le 1,2:/#.
move=> n Hn IH H; rewrite nseqS // bytes2bits_cons IH //.
rewrite addzC mulzDr mulz1 nseq_add // 1:/#; congr.
by rewrite /w2bits -mkseq_nseq /mkseq -iotaredE /=.
qed.


(*******************************************************************************)
(*                                   W64 lists                                  *)
(*******************************************************************************)

type w64 = W64.t.
type w64s = w64 list.

op w64s2bits (l: w64s) : bits =
 flatten (map W64.w2bits l).

lemma size_w64s2bits l:
 size (w64s2bits l) = 64 * size l.
proof.
by rewrite /w64s2bits size_flatten -map_comp /(\o) /= StdBigop.Bigint.sumzE
StdBigop.Bigint.BIA.big_mapT /(\o) /= StdBigop.Bigint.big_constz count_predT_eq.
qed.

(*hint simplify size_w64L2bits.*)

op bits2w64s (bs: bits) : w64s =
 map W64.bits2w (chunkify 64 bs).

lemma bits2w64s_nil: bits2w64s [] = [].
proof.
by rewrite /bits2w64s /chunkify /chunk /= mkseq0.
qed.

lemma size_bits2w64s' bs:
 size (bits2w64s bs)
 = size bs %/ 64 + b2i (! 64 %| size bs).
proof. by rewrite /bits2w64s size_map size_chunkify //. qed.

hint simplify bits2w64s_nil.

lemma bits2w64sK bs:
 64 %| size bs => w64s2bits (bits2w64s bs) = bs.
proof.
move=> Hsz; rewrite /w64s2bits /bits2w64s chunkify_chunk //.
rewrite -map_comp map_chunkK //.
by move=> l Hl; rewrite /(\o) bits2wK //.
qed.

lemma bits2w64sK' bs:
 w64s2bits (bits2w64s bs)
 = bs ++ chunkfill bs 64 false.
proof.
rewrite /w64s2bits /bits2w64s -map_comp.
apply map_chunkifyK => //.
move=> l Hl @/(\o).
case: (size l = 64) => C.
 by rewrite bits2wK // take_size_cat //.
rewrite -(W64_bits2w_cat_nseq0 l (64-size l)). 
rewrite bits2wK ?size_cat ?size_nseq 1:/# take_cat ifF 1:/# take_nseq lez_minl //.
smt(size_ge0).
qed.

lemma w64s2bits_inj: injective w64s2bits.
proof.
rewrite /w64s2bits; elim.
 move=> [|y ys] //=.
 rewrite flatten_nil flatten_cons.
 rewrite eq_sym -size_eq0 size_cat size_w2bits.
 smt(size_ge0).
move=> x xs IH; elim => //=.
 rewrite flatten_nil flatten_cons -size_eq0 size_cat size_w2bits.
 smt(size_ge0).
move=> y ys IH2.
rewrite !flatten_cons.
rewrite eqseq_cat.
 by rewrite !size_w2bits.
move=> [/W64.w2bits_inj <- /= ?].
by apply IH.
qed.

lemma w64s2bitsK: cancel w64s2bits bits2w64s.
proof.
move=> k; apply w64s2bits_inj.
by rewrite bits2w64sK // size_w64s2bits dvdz_mulr.
qed.

lemma w64s2bits_nil: w64s2bits [] = [] by done.

lemma w64s2bits_cons x xs: w64s2bits (x::xs) = W64.w2bits x ++ w64s2bits xs.
proof. by rewrite /w64s2bits map_cons flatten_cons. qed.

lemma w64s2bits_cat l1 l2:
 w64s2bits (l1++l2) = w64s2bits l1 ++ w64s2bits l2.
proof.
elim: l1 => //=.
by move=> x xs IH; rewrite !w64s2bits_cons IH -!catA; congr.
qed.

lemma take_w64s2bits n l:
 take (64*n) (w64s2bits l) = w64s2bits (take n l).
proof.
elim/natind: n l => //=.
 move=> n Hn l; rewrite !take_le0 //.
 by apply StdOrder.IntOrder.mulr_ge0_le0.
move=> n Hn IH [|x xs] /=.
 by rewrite w64s2bits_nil.
have ->/=: ! (n+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !w64s2bits_cons take_cat.
have ->/=: ! (64 * (n + 1) < size (w2bits x)) by rewrite W64.size_w2bits /#.
by rewrite mulzDr /= IH.
qed.

lemma drop_w64s2bits n l:
 drop (64*n) (w64s2bits l) = w64s2bits (drop n l).
proof.
elim/natind: n l => //=.
 move=> n Hn l; rewrite !drop_le0 //.
 by apply StdOrder.IntOrder.mulr_ge0_le0.
move=> n Hn IH [|x xs] /=.
 by rewrite w64s2bits_nil.
have ->/=: ! (n+1 <= 0) by rewrite -ltzNge ltzS.
rewrite !w64s2bits_cons drop_cat.
have ->/=: ! (64 * (n + 1) < size (w2bits x)) by rewrite W64.size_w2bits /#.
by rewrite mulzDr /= IH.
qed.

lemma nth_w64s2bits l i:
 0 <= i < 64 * size l =>
 nth false (w64s2bits l) i
 = nth false (W64.w2bits (nth W64.zero l (i %/ 64))) (i%%64).
proof.
move=> Hi; rewrite /w64s2bits (nth_flatten _ 64).
 by rewrite allP; move=> x /mapP [y [Hy ->]].
rewrite (nth_map W64.zero) //.
apply divz_cmp => //.
by rewrite mulzC.
qed.

lemma w64s2bits_xor l1 l2:
 w64s2bits (JUtils.map2 W64.(`^`) l1 l2)
 = map2 Bool.(^^) (w64s2bits l1) (w64s2bits l2).
proof.
elim: l1 l2 => //=.
 move=> [|y ys]; rewrite w64s2bits_nil // w64s2bits_cons.
 rewrite map2C /=.
  exact W64.xorwC.
 smt().
move=> x xs IH1; elim => //=.
 rewrite w64s2bits_nil map2C; first by move=> b1 b2; ring.
 rewrite w64s2bits_cons map2C /#.
move=> y ys IH2.
rewrite !w64s2bits_cons map2_cat.
 by rewrite !size_w2bits.
rewrite IH1; congr.
by rewrite W64.xorE map2_w2bits_w2bits.
qed.

lemma w64L2bits_nseq0 n:
 0 <= n =>
 w64s2bits (nseq n W64.zero) = nseq (64*n) false.
proof.
elim/natind: n => /=.
 by move=> n Hn1 Hn2; rewrite !nseq0_le 1,2:/# w64s2bits_nil.
move=> n Hn IH H; rewrite nseqS // w64s2bits_cons IH //.
rewrite addzC mulzDr mulz1 nseq_add // 1:/#; congr.
by rewrite /w2bits -mkseq_nseq /mkseq -iotaredE /=.
qed.

(*******************************************************************************)
(*                      W8 lists  =>  W64 lists                                *)
(*******************************************************************************)

op bytes2w64s (l: bytes) : w64s =
 map W8u8.pack8 (chunkify 8 l).

lemma bytes2w64s_nil: bytes2w64s [] = [].
proof. by rewrite /bytes2w64s /chunkify /chunk mkseq0. qed.

hint simplify bytes2w64s_nil.

lemma size_bytes2w64s l:
 size (bytes2w64s l)
 = size l %/ 8 + b2i (! 8 %| size l).
proof. by rewrite /bytes2w64s size_map size_chunkify //. qed.

lemma bytes2w64s_cat l1 l2:
 8 %| size l1 => bytes2w64s (l1++l2) = bytes2w64s l1 ++ bytes2w64s l2.
proof. by move=> Hsz; rewrite /bytes2w64s chunkify_cat // !map_cat. qed.

(*
lemma bytes2w64s_singl xs:
 0 < size xs <= 8 => bytes2w64s xs = [pack8 xs].
proof.
move=> Hsz; rewrite /bytes2w64s /chunkify /chunk.
have ->: size (chunkfill W8.zero 8 xs) %/ 8 = 1.
 rewrite size_chunkfill // /#.
rewrite mkseq1 /= drop0 take_oversize.
 rewrite size_chunkfill //; smt(size_ge0).
rewrite !pack8E; apply W64.init_ext => x Hx /=.
by congr; rewrite !W8u8.Pack.get_of_list 1,2:/# nth_chunkfill.
qed.
*)

lemma chunk0 ['a] n (l: 'a list):
 size l < n =>
 chunk n l = [].
proof.
move=> Hl; rewrite /chunk divz_small; smt(size_ge0 mkseq0).
qed.

lemma bytes2w64s_cons l:
 0 < size l =>
 bytes2w64s l = W8u8.pack8 (take 8 l) :: bytes2w64s (drop 8 l).
proof.
move=> Hsz0.
 rewrite -{1}(cat_take_drop 8 l).
case: (size l < 8) => Hsz.
 by rewrite !drop_oversize 1:/# cats0 take_oversize 1:/# bytes2w64s_nil /bytes2w64s chunkifyE // chunk0 /#.
by rewrite bytes2w64s_cat ?size_take 1..2:/# {1}/bytes2w64s chunkify_chunk // ?size_take // 1:/# chunk1 /#.
qed.

lemma drop_bytes2w64s n l:
 drop n (bytes2w64s l) = bytes2w64s (drop (8*n) l).
proof.
elim/natind: n l => //=.
 by move=> n Hn l; rewrite !drop_le0 // /#.
move=> n Hn IH l.
rewrite -drop_drop //.
move: l => [|x xs] //.
rewrite {1}(bytes2w64s_cons (x::xs) _) /=; first smt(size_ge0).
rewrite drop0 (:! 8 * (n + 1) <= 0) 1:/# /= IH drop_drop 1:/# //.
by congr; congr; ring.
qed.

(*
lemma size_bytes2w64L' l:
 8 %| size l => size (bytes2w64L l) = size l %/ 8.
proof. by rewrite size_bytes2w64L dvdz_eq => E; smt(). qed.
*)

lemma take_bytes2w64s n l:
 take n (bytes2w64s l) = bytes2w64s (take (8*n) l).
proof.
rewrite -{1}(cat_take_drop (8*n) l).
case: (0 <= 8*n) => Hsz0; last by rewrite !take_le0 /#.
case: (8*n <= size l) => E.
 rewrite bytes2w64s_cat.
  by rewrite size_take' 1:/# E /= /#.
 rewrite take_cat' !size_bytes2w64s size_take' // !E /= ifT. 
  by rewrite (:8 %| 8 * n) /#.
 rewrite take_oversize // size_bytes2w64s !size_take //.
 case: (8*n < size l) => C; smt().
rewrite drop_oversize 1:/# cats0 take_oversize //.
by rewrite size_bytes2w64s size_take' /#.
qed.

lemma nth_map' ['a 'b] (da: 'a) (f: 'a -> 'b) (l: 'a list) db i:
 f da = db =>
 nth db (map f l) i = f (nth da l i).
proof.
move => Hf.
case: (0 <= i && i < size l) => C.
 by rewrite (nth_map da) //.
by rewrite !nth_out; smt(size_map).
qed.

lemma pack8_nil: W8u8.pack8 [] = W64.zero.
proof.
rewrite pack8E W8u8.Pack.of_listE.
rewrite -(W8u8.Pack.init_ext (fun j => W8.zero)) //=.
apply W64.ext_eq => k Hk; rewrite initiE //=.
by rewrite W8u8.Pack.initiE 1:/# /=.
qed.

lemma nth_bytes2w64s (l : bytes) (i : int):
  0 <= i =>
  nth W64.zero (bytes2w64s l) i
  = pack8 (take 8 (drop (8*i) l)).
(*
  = pack8_t (W8u8.Pack.init (fun j => l.[8*i + j])).*)
proof.
move=> Hi; rewrite /bytes2w64s (nth_map' []) /=.
 exact pack8_nil.
congr; apply W8u8.Pack.ext_eq => k Hk.
by rewrite !get_of_list //= nth_chunkify //.
qed.


(*******************************************************************************)
(*                      W64 lists  =>  W8 lists                                *)
(*******************************************************************************)


op w64s2bytes (l: w64s) : bytes =
 flatten (map W8u8.to_list l).

lemma w64s2bytes_nil:
 w64s2bytes [] = [].
proof. by rewrite /w64s2bytes. qed.

hint simplify w64s2bytes_nil.

lemma w64s2bytes_cons x xs:
 w64s2bytes (x::xs) = W8u8.to_list x ++ w64s2bytes xs.
proof. by rewrite /w64s2bytes map_cons flatten_cons. qed.

lemma size_w64s2bytes (l: W64.t list):
 size (w64s2bytes l) = 8 * size l.
proof.
elim: l => //= x xs IH.
by rewrite w64s2bytes_cons size_cat IH /#.
qed.

(*hint simplify size_w64s2bytes.*)

lemma w64s2bytes2bits l:
 bytes2bits (w64s2bytes l) = w64s2bits l.
proof.
elim: l; first by rewrite /w64s2bytes /flatten.
move=> x xs IH.
by rewrite /w64s2bytes map_cons flatten_cons w64s2bits_cons -IH bytes2bits_cat  bytes2bits_u64 //. 
qed.

lemma w64s2bytes_singl x: w64s2bytes [x] = W8u8.to_list x by rewrite /w64s2bytes.

lemma w64s2bytes_cat l1 l2:
 w64s2bytes (l1++l2) = w64s2bytes l1 ++ w64s2bytes l2.
proof.
by elim: l1 => //= x xs IH.
qed.

lemma take_w64s2bytes n l:
 take (8*n) (w64s2bytes l) = w64s2bytes (take n l).
proof.
elim: l n => //= x xs IH n.
case: (n <= 0) => E /=; first by rewrite take_le0 /#.
by rewrite !w64s2bytes_cons -IH take_cat /= ifF /#.
qed.

lemma nth_w64s2bytes (l : W64.t list) (i : int):
  nth W8.zero (w64s2bytes l) i
  = nth W64.zero l (i %/ 8) \bits8 (i %% 8).
proof.
rewrite /w64s2bytes.
have Hsz: all (fun (s : W8.t list) => size s = 8)
              (map (fun (w : W64.t) => (to_list w)%W8u8) l).
 by rewrite allP => x /mapP [y [Hy ->]].
rewrite (nth_flatten W8.zero 8) //.
move: Hsz; rewrite allP => Hsz.
case: (0 <= i %/ 8 < size l) => E; last first.
 rewrite nth_out; first rewrite nth_out ?size_map /#.
 by rewrite nth_out // W8u8.get_zero /#.
by rewrite (nth_map W64.zero) //= /#.
qed.

print pack8K.

lemma to_list_pack8 (bs: bytes):
 size bs <= 8 =>
 W8u8.to_list (pack8 bs) = bs.
move=> Hsz.
rewrite /= !pack8bE // !get_of_list //.
admit.
qed.

print "_.[_]".
search pack8_t (\bits8).

lemma bytes2w64sK (l: W8.t list):
 8 %| size l => w64s2bytes (bytes2w64s l) = l.
proof.
move=> Hsz; rewrite /bytes2w64s /w64s2bytes chunkify_chunk //.
rewrite -map_comp map_chunkK //.
move=> xs Hxs; rewrite /(\o).
print pack8K.
rewrite -(W8u8.pack8K).
print W8u8.pack8.
print W8u8.Pack.of_listK.
print W8u8.to_list.
print pack8K.
print pack8.
print W8u8.pack8K.
 /=. smt. bits2wK //.
qed.
move=> Hsz.
rewrite /w64s2bytes /bytes2w64s -map_comp dvd_chunkfill //.
have : forall (x : W8.t list),
        x \in chunk 8 l =>
         idfun x = W8u8.to_list (pack8 x).
 move=> x Hx; rewrite /idfun /= /=.
 have x_size:= (BitEncoding.BitChunking.in_chunk_size _ _ _ _ Hx) => //.
 by rewrite -{1}(map_nth_range W8.zero x) x_size /range -iotaredE.
rewrite List.eq_in_map => <-.
by rewrite map_id BitEncoding.BitChunking.chunkK // Hsz.
qed.

lemma bytesw64sK' l:
 w64s2bytes (bytes2w64s l) = chunkfill W8.zero 8 l.
proof.
rewrite /bytes2w64s -chunkfillK //.
by rewrite bytes2w64sK ?chunkfillP // chunkfillK.
qed.

lemma W8u8_to_listE (w: W64.t):
 W8u8.to_list w = W8u8.Pack.to_list (unpack8 w).
proof.
by rewrite W8u8.unpack8E W8u8.Pack.to_listE /mkseq -iotaredE /=.
qed.

lemma W8u8_unpack8_inj: injective W8u8.unpack8.
proof.
move=> w1 w2.
rewrite !unpack8E => E.
apply W64.ext_eq => k Hk.
rewrite !get_bits8 1..2://; congr.
have /= <-:= W8u8.Pack.initiE (fun (i : int) => w1 \bits8 i) (k%/8) _.
 smt().
by rewrite E W8u8.Pack.initiE /#.
qed.

lemma W8u8_to_list_inj:
 injective W8u8.to_list.
proof.
by move=> w1 w2; rewrite !W8u8_to_listE => /W8u8.Pack.to_list_inj /W8u8_unpack8_inj.
qed.

lemma w64s2bytes_inj: injective w64s2bytes.
proof.
rewrite /w64s2bytes; elim.
 by move=> [|y ys].
move=> x xs IH; elim => //.
move=> y ys IH2.
rewrite !map_cons !flatten_cons.
rewrite eqseq_cat //; beta.
by move => [/W8u8_to_list_inj -> ?]; congr; last by apply IH.
qed.

lemma w64s2bytesK: cancel w64s2bytes bytes2w64s.
proof.
move=> k; apply w64s2bytes_inj.
by rewrite bytes2w64sK // size_w64s2bytes dvdz_mulr.
qed.
*)



(*******************************************************************************)
(*                          MEMORY OPERATIONS                                  *)
(*******************************************************************************)

lemma stores_singl mem out x: stores mem out [x] = storeW8 mem out x.
proof. by rewrite storeW8E /stores. qed.

lemma stores_cat mem out l1 l2:
 stores mem out (l1++l2) = stores (stores mem out l1) (out + size l1) l2.
proof.
elim: l1 mem out => //=.
 by move=> mem out /=; rewrite store0.
move=> x xs IH mem out.
by rewrite !stores_cons IH addzA.
qed.

lemma stores_cons' mem out x xs:
 stores mem out (x::xs) = stores (storeW8 mem out x) (out+1) xs.
proof. by rewrite -cat1s stores_cat stores_singl. qed.

lemma stores_rcons mem out x xs:
 stores mem out (rcons xs x) = storeW8 (stores mem out xs) (out + size xs) x.
proof. by rewrite -cats1 stores_cat stores_singl. qed.

lemma stores_u64 mem out x:
 stores mem out (W8u8.to_list x) = storeW64 mem out x by rewrite storeW64E.


(* name alias to [stores] to avoid uncontrolled evaluation... *)
op stores8 mem out l = stores mem out l
axiomatized by stores8E.

lemma stores8_nil mem out: stores8 mem out [] = mem.
proof. by rewrite stores8E store0. qed.

lemma stores8_singl mem out x: stores8 mem out [x] = storeW8 mem out x.
proof. by rewrite stores8E storeW8E /stores. qed.

hint simplify stores8_nil, stores8_singl.

lemma stores8_cat mem out l1 l2:
 stores8 mem out (l1++l2) = stores8 (stores8 mem out l1) (out + size l1) l2.
proof. by rewrite !stores8E stores_cat. qed.

lemma stores8_cons' mem out x xs:
 stores8 mem out (x::xs) = stores8 (storeW8 mem out x) (out+1) xs.
proof. by rewrite !stores8E stores_cons'. qed.

lemma stores8_rcons mem out x xs:
 stores8 mem out (rcons xs x) = storeW8 (stores8 mem out xs) (out + size xs) x.
proof. by rewrite !stores8E stores_rcons. qed.

lemma stores8_u64 mem out x:
 stores8 mem out (W8u8.to_list x) = storeW64 mem out x.
proof. by rewrite stores8E storeW64E. qed.


(* as well for [store64]... *)
op stores64 (m: global_mem_t) (a:address) (w: W64.t list): global_mem_t =
 foldl (fun (m0 : global_mem_t) (i : int) => storeW64 m0 (a + 8*i) (nth W64.zero w i))
       m (iota_ 0 (size w))
axiomatized by stores64E.

lemma stores64_nil mem a: stores64 mem a [] = mem.
proof. by rewrite stores64E iota0 /=. qed.

lemma stores64_singl mem a x: stores64 mem a [x] = storeW64 mem a x.
proof. by rewrite stores64E /= iota1 /=. qed.

hint simplify stores64_nil, stores64_singl.

lemma stores64_cat mem out l1 l2:
 stores64 mem out (l1 ++ l2)
 = stores64 (stores64 mem out l1) (out + 8*size l1) l2.
proof.
rewrite !stores64E size_cat iota_add; first 2 smt(size_ge0).
rewrite (addzC 0) iota_addl foldl_cat foldl_map /=.
have ->: foldl (fun (m0 : global_mem_t) (i : int) =>
                 storeW64 m0 (out + 8 * i) (nth W64.zero (l1 ++ l2) i)) mem
               (iota_ 0 (size l1))
         = foldl (fun (m0 : global_mem_t) (i : int) =>
                   storeW64 m0 (out + 8 * i) (nth W64.zero l1 i)) mem
                 (iota_ 0 (size l1)).
 apply foldl_in_eq => mem' x; rewrite mem_iota => |> _ H0.
 by rewrite nth_cat H0.
apply foldl_in_eq => mem' x; rewrite mem_iota => |> *.
case: (x=0) => E.
 by rewrite E /= nth_cat ltzz.
rewrite nth_cat (:! size l1 + x < size l1) 1:/# /=; congr; first smt().
congr; smt().
qed.

lemma stores64_cons mem a x xs:
 stores64 mem a (x::xs) = stores64 (storeW64 mem a x) (a+8) xs.
proof. by rewrite -cat1s stores64_cat. qed.

lemma stores64_rcons mem out xs x:
 stores64 mem out (rcons xs x)
 = storeW64 (stores64 mem out xs) (out + 8*size xs) x.
proof. by rewrite -cats1 stores64_cat. qed.

lemma w64L_to_bytes_singl x:
 w64L_to_bytes [x]
 = W8u8.to_list x by done.

lemma stores64_stores8 mem out l:
 stores64 mem out l = stores8 mem out (w64L_to_bytes l).
proof.
rewrite stores8E; elim/last_ind: l mem out => //=.
 by move=> mem out; rewrite store0.
move=> xs x IH mem out.
rewrite stores64_rcons IH -cats1 w64L_to_bytes_cat stores_cat /=  w64L_to_bytes_singl.
by rewrite stores_u64 size_w64L_to_bytes.
qed.


(** [memread] reads a list of bytes from memory *)
op memread (m: global_mem_t) (a: address) (sz: int): W8.t list =
  mkseq (fun i => m.[a + i]) sz.

lemma size_memread mem a sz:
 0 <= sz => size (memread mem a sz) = sz
by rewrite size_mkseq /#.

lemma drop_memread n mem ptr k:
  0 <= n <= k =>
  drop n (memread mem ptr k) = memread mem (ptr+n) (k-n).
proof.
move=> Hn; rewrite drop_mkseq //=.
by apply eq_mkseq => x; smt().
qed.

lemma nth_memread mem in_ inlen i:
 0 <= i < inlen =>
 nth W8.zero (memread mem in_ inlen) i
 = loadW8 mem (in_ + i)%Int.
proof. by move=> Hi; rewrite nth_mkseq. qed.

lemma memread0 mem in_: memread mem in_ 0 = [].
proof. by rewrite /memread /= mkseq0. qed.

lemma memread1 mem in_: memread mem in_ 1 = [loadW8 mem in_].
proof. by rewrite /memread /= mkseq1 /= /#. qed.

hint simplify memread0, memread1.

lemma memread_add mem in_ x y:
 0 <= x => 0 <= y =>
 memread mem in_ (x+y)%Int = memread mem in_ x ++ memread mem (in_ + x) y.
proof.
move=> Hx Hy; rewrite /memread mkseq_add //; congr.
by apply eq_mkseq => z /=; rewrite addzA.
qed.

lemma memreadS mem in_ x:
 0 <= x =>
 memread mem in_ (x+1)%Int = rcons (memread mem in_ x) (loadW8 mem (in_+x)).
proof. by move=> Hx; rewrite memread_add //= cats1. qed.

lemma take_memread n mem ptr k:
 0 <= n => 
 take n (memread mem ptr k) = memread mem ptr (min n k).
proof. move=> Hn; rewrite /memread take_mkseq' //. qed.

lemma loadW8_memread mem in_ inlen i:
 0 <= i < inlen =>
 loadW8 mem (in_ + i)%Int
 = nth W8.zero (memread mem in_ inlen) i.
proof.
rewrite /loadW8 /memread => Hi.
by rewrite nth_mkseq.
qed.

lemma loadW8_memread' mem in_ off inlen i:
 (off <= i < off + inlen)%Int =>
 loadW8 mem (in_ + i)%Int
 = nth W8.zero (memread mem (in_ + off) inlen) (i-off).
proof.
rewrite /loadW8 /memread => Hi.
by rewrite nth_mkseq /#.
qed.


lemma nth_memread_u64 mem in_ inlen i:
 0 <= i => 8*i+8 <= inlen =>
 loadW64 mem (in_+8*i) = nth W64.zero (w64L_from_bytes (memread mem in_ inlen)) i.
proof.
move=> ??; rewrite nth_w64L_from_bytes 1:/#.
rewrite /loadW64 W8u8.pack8E pack8E; apply W64.init_ext => x Hx /=.
congr; rewrite W8u8.Pack.initiE 1:/# /= /memread /=.
rewrite of_listE W8u8.Pack.initiE 1:/# /=.
by rewrite drop_mkseq 1:/# take_mkseq 1:/# /= nth_mkseq /#.
qed.

lemma memread_split off mem a sz:
 0 <= off <= sz =>
 memread mem a sz = memread mem a off ++ memread mem (a+off) (sz-off).
proof.
move=> Hoff; have ->: sz = off + (sz-off) by ring.
rewrite /memread mkseq_add 1,2:/#; congr.
rewrite (:off + (sz - off) - off = sz-off) 1:/#.
by apply eq_mkseq => i /#.
qed.



(** [memread64] reads a list of [n] (full) 64-bit words from memory *)
op memread64 (m: global_mem_t) (a: address) (n: int): W64.t list =
 mkseq (fun i => loadW64 m (a+8*i)) n.

lemma memread64_0 mem in_: memread64 mem in_ 0 = [].
proof. by rewrite /memread64 mkseq0. qed.

lemma memread64_1 mem in_: memread64 mem in_ 1 = [loadW64 mem in_].
proof. by rewrite /memread64 mkseq1. qed.

hint simplify memread64_0, memread64_1.

lemma size_memread64 mem a sz:
 0 <= sz => size (memread64 mem a sz) = sz
by rewrite size_mkseq /#.

lemma nth_memread64 m a sz i:
 0 <= i < sz =>
 nth W64.zero (memread64 m a sz) i = loadW64 m (a+8*i).
proof. by move=> Hsz; rewrite nth_mkseq //. qed.

lemma memread64E m a sz:
 memread64 m a sz = w64L_from_bytes (memread m a (8*sz)).
proof.
apply (eq_from_nth W64.zero).
 by rewrite size_mkseq size_w64L_from_bytes size_mkseq /#. 
rewrite size_mkseq => i Hi.
rewrite nth_w64L_from_bytes 1:/# nth_memread64 1:/# /loadW64 of_listE; congr.
apply W8u8.Pack.init_ext => j Hj /=.
rewrite drop_memread 1:/# take_memread 1:/# nth_mkseq /#.
qed.

lemma memread_split64 mem a sz:
 0 <= sz =>
 memread mem a sz
 = w64L_to_bytes (memread64 mem a (sz %/ 8))
   ++ memread mem (a + sz %/8 * 8) (sz %% 8).
proof.
move=> Hsz; rewrite (memread_split (sz %/ 8*8)) 1:/#; congr.
 rewrite memread64E w64L_from_bytesK chunkfillE //. (* /chunkify_fillsuffix.*)
 by rewrite size_memread 1:/# /= dvdz_mulr 1:dvdzz /#.
by rewrite modzE.
qed.

lemma memread64_add mem in_ x y:
 0 <= x => 0 <= y =>
 memread64 mem in_ (x+y)%Int = memread64 mem in_ x ++ memread64 mem (in_ + 8*x) y.
proof.
move=> Hx Hy; rewrite /memread64 mkseq_add //; congr.
by apply eq_mkseq => z /=; congr; ring.
qed.

lemma memread64S mem in_ i:
 0 <= i =>
 memread64 mem in_ (i+1)
 = rcons (memread64 mem in_ i) (loadW64 mem (in_ + 8*i)).
proof. by move=> Hi; rewrite memread64_add // memread64_1 cats1. qed.

