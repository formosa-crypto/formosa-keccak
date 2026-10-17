(* ==================================================================== *)
(* Circuit bindings for Jasmin byte arrays (JByte_array.ByteArray, the  *)
(* [BArrayN.t] types of the [--array-model=barray] extraction).         *)
(*                                                                      *)
(* A byte array of [size] bytes is bound as a bitstring of [8 * size]   *)
(* bits (byte [i] occupies bits [8*i .. 8*i+7], little-endian within    *)
(* the byte, as in [W8.w2bits]). Accesses are bound with offsets in     *)
(* bytes, matching what the extraction emits:                           *)
(*   - [t.[i]] (get8)                   : "aextract"                    *)
(*   - [t.[i <- w]] (set8 / set8d)      : "uinsert", unit W8            *)
(*   - [getKd t i] / [setKd t i w]      : "uextract" / "uinsert", unit W8 *)
(*     (the scaled [getK t i] are abbreviations for [getKd t (r*i)])    *)
(*   - [get_sub] / [set_sub] of SubByteArray : "uextract" / "uinsert"   *)
(*                                                                      *)
(* The word accessors only make sense when the array holds at least one *)
(* word, so they live in nested abstract theories [GetSet16] ..         *)
(* [GetSet256], cloned for each array size where they are used (see    *)
(* keccak_barray_bindings.ec).                                          *)
(*                                                                      *)
(* Needs an EasyCrypt with the "uextract" / "uinsert" operator kinds.   *)
(* ==================================================================== *)
require import AllCore List IntDiv StdOrder BitEncoding QFABV.
from Jasmin require import JModel_x86 JByte_array.
require import Keccak_bindings.

import IntOrder BS2Int BitChunking.

(* -------------------------------------------------------------------- *)
abstract theory BArrayBS.
  clone import ByteArray as BA.

  axiom gt0_size : 0 < BA.size.

  (* ------------------------------------------------------------------ *)
  op tobits (a : BA.t) : bool list =
    flatten (map W8.w2bits (BA.to_list a)).

  op ofbits (bs : bool list) : BA.t =
    BA.of_list (map W8.bits2w (chunk 8 bs)).

  op touint (a : BA.t) : int = bs2int (tobits a).

  op tosint (a : BA.t) : int =
    let v = touint a in
    if nth false (tobits a) (8 * BA.size - 1) then v - 2 ^ (8 * BA.size) else v.

  op ofint (i : int) : BA.t = ofbits (int2bs (8 * BA.size) i).

  (* ------------------------------------------------------------------ *)
  lemma size_tobits (a : BA.t) : size (tobits a) = 8 * BA.size.
  proof.
  rewrite /tobits (size_flatten_ctt 8).
  - by move=> bs /mapP [w] [_ ->]; rewrite W8.size_w2bits.
  - by rewrite size_map BA.size_to_list.
  qed.

  lemma nth_tobits (a : BA.t) (k : int) :
    0 <= k < 8 * BA.size => nth false (tobits a) k = a.[k %/ 8].[k %% 8].
  proof.
  move=> hk; rewrite /tobits (nth_flatten false 8).
  - by rewrite allP => bs /mapP [w] [_ ->].
  rewrite (nth_map W8.zero) 1:BA.size_to_list 1:/#.
  by rewrite BA.get_to_list W8.get_w2bits.
  qed.

  (* A window of [n] bits at byte offset [base], characterised bitwise. *)
  lemma take_drop_tobits (a : BA.t) (base n : int) (bs : bool list) :
       0 <= base => 0 <= n => base * 8 + n <= 8 * BA.size
    => size bs = n
    => (forall j, 0 <= j < n => nth false bs j = a.[base + j %/ 8].[j %% 8])
    => take n (drop (base * 8) (tobits a)) = bs.
  proof.
  move=> h0 hn h1 hsz hbs; apply (eq_from_nth false).
  - by rewrite size_take // size_drop 1:/# size_tobits /#.
  move=> j; rewrite size_take // size_drop 1:/# size_tobits => hj.
  have {hj} hj : 0 <= j < n by smt().
  rewrite nth_take // 1:/# nth_drop 1,2:/# nth_tobits 1:/# hbs //.
  by rewrite divzMDl // modzMDl.
  qed.

  (* Bit [k] of a word made of [r] bytes. *)
  lemma divmod8 (k r : int) : 0 < r =>
       k %/ (8 * r) = k %/ 8 %/ r
    /\ k %% (8 * r) = (k %/ 8 %% r) * 8 + k %% 8.
  proof.
  move=> hr; split; 1: by rewrite divzMr // /#.
  rewrite {1}(divz_eq k 8) {1}(divz_eq (k %/ 8) r).
  have -> : (k %/ 8 %/ r * r + k %/ 8 %% r) * 8 + k %% 8
          = (k %/ 8 %/ r) * (8 * r) + ((k %/ 8 %% r) * 8 + k %% 8) by ring.
  by rewrite modzMDl modz_small; smt(modz_cmp).
  qed.

  (* Extensionality of the bit view. *)
  lemma tobits_ext (a : BA.t) (bs : bool list) :
       size bs = 8 * BA.size
    => (forall k, 0 <= k < 8 * BA.size => nth false bs k = a.[k %/ 8].[k %% 8])
    => bs = tobits a.
  proof.
  move=> hsz hbs; apply (eq_from_nth false); 1: by rewrite size_tobits.
  by move=> k; rewrite hsz => hk; rewrite nth_tobits // hbs.
  qed.

  (* ------------------------------------------------------------------ *)
  bind bitstring tobits ofbits touint tosint ofint BA.t (8 * BA.size).

  realize gt0_size by smt(gt0_size).
  realize size_tolist by exact: size_tobits.

  realize tolistP.
  proof.
  move=> a; rewrite /ofbits /tobits flattenK //.
  - by move=> bs /mapP [w] [_ ->]; rewrite W8.size_w2bits.
  rewrite -map_comp (eq_map _ idfun) => [w|]; 1: by rewrite /(\o) W8.w2bitsK.
  by rewrite map_id BA.to_listK.
  qed.

  realize oflistP.
  proof.
  move=> bs hsz; rewrite /tobits /ofbits BA.of_listK.
  - by rewrite size_map size_chunk // hsz; smt(gt0_size).
  rewrite -map_comp -(iffLR _ _ (eq_in_map idfun _ _)).
  - move=> w hw; have ? : size w = 8 by apply (in_chunk_size 8 bs w).
    by rewrite /idfun /(\o) W8.bits2wK.
  by rewrite map_id chunkK // hsz dvdz_mulr dvdzz.
  qed.

  realize touintP by done.

  realize tosintP.
  proof. by move=> a; right; rewrite /msb /tosint /touint /=; case: (nth _ _ _). qed.

  realize ofintP by done.

  (* ------------------------------------------------------------------ *)
  (* get8: aligned extraction of a byte.                                *)
  bind op [BA.t & W8.t] BA."_.[_]" "aextract".

  realize dvd_size by rewrite dvdz_mulr dvdzz.

  realize bvaextractP.
  proof.
  move=> a base hb; apply: take_drop_tobits; ~-1:smt(W8.size_w2bits).
  by move=> j hj; rewrite W8.get_w2bits (divz_small j 8) 1:/# (modz_small j 8) 1:/#.
  qed.

  (* ------------------------------------------------------------------ *)
  (* set8 / set8d: insertion of a byte at a byte offset.                *)
  bind op [BA.t & W8.t & W8.t] BA."_.[_<-_]" "uinsert".

  realize le_size by smt(gt0_size).

  realize bvuinsertP.
  proof.
  move=> a base w h0 h1 /=; apply: tobits_ext.
  - by rewrite size_mkseq; smt(gt0_size).
  move=> k hk; rewrite nth_mkseq //= BA.get_set_if.
  case: (k < base * 8 || base * 8 + 8 <= k) => hc.
  - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
    by rewrite ifF //; smt().
  rewrite (nth_change_dfl false) 1:W8.size_w2bits 1:/# W8.get_w2bits.
  by rewrite ifT 1:/#; congr; smt(divz_eq).
  qed.

  (* ------------------------------------------------------------------ *)
  (* 16-bit words at byte offsets: get16d / set16d (and get16 / set16).  *)
  abstract theory GetSet16.
    axiom le_size : 2 <= BA.size.

    (* The bit view of an array of [n] words is the concatenation of the *)
    (* bits of its words (used to bind views such as [ArrayN.init       *)
    (* (BArrayM.get16 a)] as "b2a").                                    *)
    lemma tobits_get16 (a : BA.t) (n : int) :
      2 * n = BA.size =>
      tobits a = flatten (map W16.w2bits (mkseq (fun i => BA.get16 a i) n)).
    proof.
    move=> hn; apply (eq_from_nth false).
    - rewrite size_tobits (size_flatten_ctt 16).
      + by move=> bs /mapP [w] [_ ->]; rewrite W16.size_w2bits.
      by rewrite size_map size_mkseq; smt(gt0_size).
    move=> k; rewrite size_tobits => hk.
    rewrite nth_tobits // (nth_flatten false 16).
    - by rewrite allP => bs /mapP [w] [_ ->].
    rewrite (nth_map W16.zero) 1:size_mkseq 1:/# nth_mkseq 1:/# /=.
    rewrite W2u8.get_bits8 1:/# BA.get16d_byte 1:/#.
    have hk8 : k %/ 8 = 2 * (k %/ 16) + (k %% 16) %/ 8.
    - rewrite {1}(divz_eq k 16) (_: k %/ 16 * 16 = (2 * (k %/ 16)) * 8) 1:/#.
      by rewrite divzMDl.
    have hm8 : k %% 8 = (k %% 16) %% 8.
    - by rewrite {1}(divz_eq k 16) (_: k %/ 16 * 16 = (2 * (k %/ 16)) * 8) 1:/# modzMDl.
    by rewrite hk8 hm8.
    qed.

    bind op [BA.t & W16.t & W8.t] BA.get16d "uextract".

    realize le_size by smt(le_size).

    realize bvuextractP.
    proof.
    move=> a base h0 h1; apply: take_drop_tobits; ~-1: smt(W16.size_w2bits).
    move=> j hj; rewrite W16.get_w2bits W2u8.get_bits8 1:/#.
    by rewrite BA.get16d_byte 1:/#.
    qed.

    bind op [BA.t & W16.t & W8.t] BA.set16d "uinsert".

    realize le_size by smt(le_size).

    realize bvuinsertP.
    proof.
    move=> a base w h0 h1 /=; apply: tobits_ext.
    - by rewrite size_mkseq; smt(gt0_size).
    move=> k hk; rewrite nth_mkseq //= BA.get8_set16dE.
    case: (k < base * 8 || base * 8 + 16 <= k) => hc.
    - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
      by rewrite ifF //; smt().
    rewrite (nth_change_dfl false) 1:W16.size_w2bits 1:/# W16.get_w2bits.
    rewrite ifT 1:/# W2u8.bits8iE 1:/#; congr; smt(divz_eq).
    qed.

    (* Constant tables: [of_list16 [w0; w1; ...]]. *)
    bind op [BA.t & W16.t] BA.of_list16 "oflist".

    realize bvoflistP.
    proof.
    move=> l; rewrite eq_sym; apply: tobits_ext.
    - by rewrite size_take ?size_cat ?size_nseq; smt(gt0_size size_ge0).
    move=> k hk; have [hq hm] := divmod8 k 2 _ => //.
    have hF : size (flatten (map W16.w2bits l)) = 16 * size l.
    - rewrite (size_flatten_ctt 16) 2:size_map //.
      by move=> bs /mapP [w] [_ ->]; rewrite W16.size_w2bits.
    rewrite nth_take 1,2:/# nth_cat hF BA.get8_of_list16.
    case: (k < 16 * size l) => hkl /=.
    - rewrite ifT; 1: smt(ltz_divLR).
      rewrite (nth_flatten false 16); 1: by rewrite allP => bs /mapP [w] [_ ->].
      rewrite (nth_map W16.zero) 1:#smt:(ltz_divLR size_ge0) W16.get_w2bits W2u8.bits8iE 1:/#.
      by rewrite (_ : 16 = 8 * 2) // hq hm.
    rewrite ifF; 1: smt(ltz_divLR).
    by rewrite nth_nseq_if W8.zerowE; smt().
    qed.
  end GetSet16.

  (* ------------------------------------------------------------------ *)
  (* 32-bit words at byte offsets: get32d / set32d (and get32 / set32).  *)
  abstract theory GetSet32.
    axiom le_size : 4 <= BA.size.

    (* The bit view of an array of [n] words is the concatenation of the *)
    (* bits of its words (used to bind views such as [ArrayN.init       *)
    (* (BArrayM.get32 a)] as "b2a").                                    *)
    lemma tobits_get32 (a : BA.t) (n : int) :
      4 * n = BA.size =>
      tobits a = flatten (map W32.w2bits (mkseq (fun i => BA.get32 a i) n)).
    proof.
    move=> hn; apply (eq_from_nth false).
    - rewrite size_tobits (size_flatten_ctt 32).
      + by move=> bs /mapP [w] [_ ->]; rewrite W32.size_w2bits.
      by rewrite size_map size_mkseq; smt(gt0_size).
    move=> k; rewrite size_tobits => hk.
    rewrite nth_tobits // (nth_flatten false 32).
    - by rewrite allP => bs /mapP [w] [_ ->].
    rewrite (nth_map W32.zero) 1:size_mkseq 1:/# nth_mkseq 1:/# /=.
    rewrite W4u8.get_bits8 1:/# BA.get32d_byte 1:/#.
    have hk8 : k %/ 8 = 4 * (k %/ 32) + (k %% 32) %/ 8.
    - rewrite {1}(divz_eq k 32) (_: k %/ 32 * 32 = (4 * (k %/ 32)) * 8) 1:/#.
      by rewrite divzMDl.
    have hm8 : k %% 8 = (k %% 32) %% 8.
    - by rewrite {1}(divz_eq k 32) (_: k %/ 32 * 32 = (4 * (k %/ 32)) * 8) 1:/# modzMDl.
    by rewrite hk8 hm8.
    qed.

    bind op [BA.t & W32.t & W8.t] BA.get32d "uextract".

    realize le_size by smt(le_size).

    realize bvuextractP.
    proof.
    move=> a base h0 h1; apply: take_drop_tobits; ~-1: smt(W32.size_w2bits).
    move=> j hj; rewrite W32.get_w2bits W4u8.get_bits8 1:/#.
    by rewrite BA.get32d_byte 1:/#.
    qed.

    bind op [BA.t & W32.t & W8.t] BA.set32d "uinsert".

    realize le_size by smt(le_size).

    realize bvuinsertP.
    proof.
    move=> a base w h0 h1 /=; apply: tobits_ext.
    - by rewrite size_mkseq; smt(gt0_size).
    move=> k hk; rewrite nth_mkseq //= BA.get8_set32dE.
    case: (k < base * 8 || base * 8 + 32 <= k) => hc.
    - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
      by rewrite ifF //; smt().
    rewrite (nth_change_dfl false) 1:W32.size_w2bits 1:/# W32.get_w2bits.
    rewrite ifT 1:/# W4u8.bits8iE 1:/#; congr; smt(divz_eq).
    qed.

    (* Constant tables: [of_list32 [w0; w1; ...]]. *)
    bind op [BA.t & W32.t] BA.of_list32 "oflist".

    realize bvoflistP.
    proof.
    move=> l; rewrite eq_sym; apply: tobits_ext.
    - by rewrite size_take ?size_cat ?size_nseq; smt(gt0_size size_ge0).
    move=> k hk; have [hq hm] := divmod8 k 4 _ => //.
    have hF : size (flatten (map W32.w2bits l)) = 32 * size l.
    - rewrite (size_flatten_ctt 32) 2:size_map //.
      by move=> bs /mapP [w] [_ ->]; rewrite W32.size_w2bits.
    rewrite nth_take 1,2:/# nth_cat hF BA.get8_of_list32.
    case: (k < 32 * size l) => hkl /=.
    - rewrite ifT; 1: smt(ltz_divLR).
      rewrite (nth_flatten false 32); 1: by rewrite allP => bs /mapP [w] [_ ->].
      rewrite (nth_map W32.zero) 1:#smt:(ltz_divLR size_ge0) W32.get_w2bits W4u8.bits8iE 1:/#.
      by rewrite (_ : 32 = 8 * 4) // hq hm.
    rewrite ifF; 1: smt(ltz_divLR).
    by rewrite nth_nseq_if W8.zerowE; smt().
    qed.
  end GetSet32.

  (* ------------------------------------------------------------------ *)
  (* 64-bit words at byte offsets: get64d / set64d (and get64 / set64).  *)
  abstract theory GetSet64.
    axiom le_size : 8 <= BA.size.

    (* The bit view of an array of [n] words is the concatenation of the *)
    (* bits of its words (used to bind views such as [ArrayN.init       *)
    (* (BArrayM.get64 a)] as "b2a").                                    *)
    lemma tobits_get64 (a : BA.t) (n : int) :
      8 * n = BA.size =>
      tobits a = flatten (map W64.w2bits (mkseq (fun i => BA.get64 a i) n)).
    proof.
    move=> hn; apply (eq_from_nth false).
    - rewrite size_tobits (size_flatten_ctt 64).
      + by move=> bs /mapP [w] [_ ->]; rewrite W64.size_w2bits.
      by rewrite size_map size_mkseq; smt(gt0_size).
    move=> k; rewrite size_tobits => hk.
    rewrite nth_tobits // (nth_flatten false 64).
    - by rewrite allP => bs /mapP [w] [_ ->].
    rewrite (nth_map W64.zero) 1:size_mkseq 1:/# nth_mkseq 1:/# /=.
    rewrite W8u8.get_bits8 1:/# BA.get64d_byte 1:/#.
    have hk8 : k %/ 8 = 8 * (k %/ 64) + (k %% 64) %/ 8.
    - rewrite {1}(divz_eq k 64) (_: k %/ 64 * 64 = (8 * (k %/ 64)) * 8) 1:/#.
      by rewrite divzMDl.
    have hm8 : k %% 8 = (k %% 64) %% 8.
    - by rewrite {1}(divz_eq k 64) (_: k %/ 64 * 64 = (8 * (k %/ 64)) * 8) 1:/# modzMDl.
    by rewrite hk8 hm8.
    qed.

    bind op [BA.t & W64.t & W8.t] BA.get64d "uextract".

    realize le_size by smt(le_size).

    realize bvuextractP.
    proof.
    move=> a base h0 h1; apply: take_drop_tobits; ~-1: smt(W64.size_w2bits).
    move=> j hj; rewrite W64.get_w2bits W8u8.get_bits8 1:/#.
    by rewrite BA.get64d_byte 1:/#.
    qed.

    bind op [BA.t & W64.t & W8.t] BA.set64d "uinsert".

    realize le_size by smt(le_size).

    realize bvuinsertP.
    proof.
    move=> a base w h0 h1 /=; apply: tobits_ext.
    - by rewrite size_mkseq; smt(gt0_size).
    move=> k hk; rewrite nth_mkseq //= BA.get8_set64dE.
    case: (k < base * 8 || base * 8 + 64 <= k) => hc.
    - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
      by rewrite ifF //; smt().
    rewrite (nth_change_dfl false) 1:W64.size_w2bits 1:/# W64.get_w2bits.
    rewrite ifT 1:/# W8u8.bits8iE 1:/#; congr; smt(divz_eq).
    qed.

    (* Constant tables: [of_list64 [w0; w1; ...]]. *)
    bind op [BA.t & W64.t] BA.of_list64 "oflist".

    realize bvoflistP.
    proof.
    move=> l; rewrite eq_sym; apply: tobits_ext.
    - by rewrite size_take ?size_cat ?size_nseq; smt(gt0_size size_ge0).
    move=> k hk; have [hq hm] := divmod8 k 8 _ => //.
    have hF : size (flatten (map W64.w2bits l)) = 64 * size l.
    - rewrite (size_flatten_ctt 64) 2:size_map //.
      by move=> bs /mapP [w] [_ ->]; rewrite W64.size_w2bits.
    rewrite nth_take 1,2:/# nth_cat hF BA.get8_of_list64.
    case: (k < 64 * size l) => hkl /=.
    - rewrite ifT; 1: smt(ltz_divLR).
      rewrite (nth_flatten false 64); 1: by rewrite allP => bs /mapP [w] [_ ->].
      rewrite (nth_map W64.zero) 1:#smt:(ltz_divLR size_ge0) W64.get_w2bits W8u8.bits8iE 1:/#.
      by rewrite (_ : 64 = 8 * 8) // hq hm.
    rewrite ifF; 1: smt(ltz_divLR).
    by rewrite nth_nseq_if W8.zerowE; smt().
    qed.
  end GetSet64.

  (* ------------------------------------------------------------------ *)
  (* 128-bit words at byte offsets: get128d / set128d (and get128 / set128).  *)
  abstract theory GetSet128.
    axiom le_size : 16 <= BA.size.

    (* The bit view of an array of [n] words is the concatenation of the *)
    (* bits of its words (used to bind views such as [ArrayN.init       *)
    (* (BArrayM.get128 a)] as "b2a").                                    *)
    lemma tobits_get128 (a : BA.t) (n : int) :
      16 * n = BA.size =>
      tobits a = flatten (map W128.w2bits (mkseq (fun i => BA.get128 a i) n)).
    proof.
    move=> hn; apply (eq_from_nth false).
    - rewrite size_tobits (size_flatten_ctt 128).
      + by move=> bs /mapP [w] [_ ->]; rewrite W128.size_w2bits.
      by rewrite size_map size_mkseq; smt(gt0_size).
    move=> k; rewrite size_tobits => hk.
    rewrite nth_tobits // (nth_flatten false 128).
    - by rewrite allP => bs /mapP [w] [_ ->].
    rewrite (nth_map W128.zero) 1:size_mkseq 1:/# nth_mkseq 1:/# /=.
    rewrite W16u8.get_bits8 1:/# BA.get128d_byte 1:/#.
    have hk8 : k %/ 8 = 16 * (k %/ 128) + (k %% 128) %/ 8.
    - rewrite {1}(divz_eq k 128) (_: k %/ 128 * 128 = (16 * (k %/ 128)) * 8) 1:/#.
      by rewrite divzMDl.
    have hm8 : k %% 8 = (k %% 128) %% 8.
    - by rewrite {1}(divz_eq k 128) (_: k %/ 128 * 128 = (16 * (k %/ 128)) * 8) 1:/# modzMDl.
    by rewrite hk8 hm8.
    qed.

    bind op [BA.t & W128.t & W8.t] BA.get128d "uextract".

    realize le_size by smt(le_size).

    realize bvuextractP.
    proof.
    move=> a base h0 h1; apply: take_drop_tobits; ~-1: smt(W128.size_w2bits).
    move=> j hj; rewrite W128.get_w2bits W16u8.get_bits8 1:/#.
    by rewrite BA.get128d_byte 1:/#.
    qed.

    bind op [BA.t & W128.t & W8.t] BA.set128d "uinsert".

    realize le_size by smt(le_size).

    realize bvuinsertP.
    proof.
    move=> a base w h0 h1 /=; apply: tobits_ext.
    - by rewrite size_mkseq; smt(gt0_size).
    move=> k hk; rewrite nth_mkseq //= BA.get8_set128dE.
    case: (k < base * 8 || base * 8 + 128 <= k) => hc.
    - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
      by rewrite ifF //; smt().
    rewrite (nth_change_dfl false) 1:W128.size_w2bits 1:/# W128.get_w2bits.
    rewrite ifT 1:/# W16u8.bits8iE 1:/#; congr; smt(divz_eq).
    qed.

    (* Constant tables: [of_list128 [w0; w1; ...]]. *)
    bind op [BA.t & W128.t] BA.of_list128 "oflist".

    realize bvoflistP.
    proof.
    move=> l; rewrite eq_sym; apply: tobits_ext.
    - by rewrite size_take ?size_cat ?size_nseq; smt(gt0_size size_ge0).
    move=> k hk; have [hq hm] := divmod8 k 16 _ => //.
    have hF : size (flatten (map W128.w2bits l)) = 128 * size l.
    - rewrite (size_flatten_ctt 128) 2:size_map //.
      by move=> bs /mapP [w] [_ ->]; rewrite W128.size_w2bits.
    rewrite nth_take 1,2:/# nth_cat hF BA.get8_of_list128.
    case: (k < 128 * size l) => hkl /=.
    - rewrite ifT; 1: smt(ltz_divLR).
      rewrite (nth_flatten false 128); 1: by rewrite allP => bs /mapP [w] [_ ->].
      rewrite (nth_map W128.zero) 1:#smt:(ltz_divLR size_ge0) W128.get_w2bits W16u8.bits8iE 1:/#.
      by rewrite (_ : 128 = 8 * 16) // hq hm.
    rewrite ifF; 1: smt(ltz_divLR).
    by rewrite nth_nseq_if W8.zerowE; smt().
    qed.
  end GetSet128.

  (* ------------------------------------------------------------------ *)
  (* 256-bit words at byte offsets: get256d / set256d (and get256 / set256).  *)
  abstract theory GetSet256.
    axiom le_size : 32 <= BA.size.

    (* The bit view of an array of [n] words is the concatenation of the *)
    (* bits of its words (used to bind views such as [ArrayN.init       *)
    (* (BArrayM.get256 a)] as "b2a").                                    *)
    lemma tobits_get256 (a : BA.t) (n : int) :
      32 * n = BA.size =>
      tobits a = flatten (map W256.w2bits (mkseq (fun i => BA.get256 a i) n)).
    proof.
    move=> hn; apply (eq_from_nth false).
    - rewrite size_tobits (size_flatten_ctt 256).
      + by move=> bs /mapP [w] [_ ->]; rewrite W256.size_w2bits.
      by rewrite size_map size_mkseq; smt(gt0_size).
    move=> k; rewrite size_tobits => hk.
    rewrite nth_tobits // (nth_flatten false 256).
    - by rewrite allP => bs /mapP [w] [_ ->].
    rewrite (nth_map W256.zero) 1:size_mkseq 1:/# nth_mkseq 1:/# /=.
    rewrite W32u8.get_bits8 1:/# BA.get256d_byte 1:/#.
    have hk8 : k %/ 8 = 32 * (k %/ 256) + (k %% 256) %/ 8.
    - rewrite {1}(divz_eq k 256) (_: k %/ 256 * 256 = (32 * (k %/ 256)) * 8) 1:/#.
      by rewrite divzMDl.
    have hm8 : k %% 8 = (k %% 256) %% 8.
    - by rewrite {1}(divz_eq k 256) (_: k %/ 256 * 256 = (32 * (k %/ 256)) * 8) 1:/# modzMDl.
    by rewrite hk8 hm8.
    qed.

    bind op [BA.t & W256.t & W8.t] BA.get256d "uextract".

    realize le_size by smt(le_size).

    realize bvuextractP.
    proof.
    move=> a base h0 h1; apply: take_drop_tobits; ~-1: smt(W256.size_w2bits).
    move=> j hj; rewrite W256.get_w2bits W32u8.get_bits8 1:/#.
    by rewrite BA.get256d_byte 1:/#.
    qed.

    bind op [BA.t & W256.t & W8.t] BA.set256d "uinsert".

    realize le_size by smt(le_size).

    realize bvuinsertP.
    proof.
    move=> a base w h0 h1 /=; apply: tobits_ext.
    - by rewrite size_mkseq; smt(gt0_size).
    move=> k hk; rewrite nth_mkseq //= BA.get8_set256dE.
    case: (k < base * 8 || base * 8 + 256 <= k) => hc.
    - rewrite (nth_change_dfl false) 1:size_tobits 1:// nth_tobits //.
      by rewrite ifF //; smt().
    rewrite (nth_change_dfl false) 1:W256.size_w2bits 1:/# W256.get_w2bits.
    rewrite ifT 1:/# W32u8.bits8iE 1:/#; congr; smt(divz_eq).
    qed.

    (* Constant tables: [of_list256 [w0; w1; ...]]. *)
    bind op [BA.t & W256.t] BA.of_list256 "oflist".

    realize bvoflistP.
    proof.
    move=> l; rewrite eq_sym; apply: tobits_ext.
    - by rewrite size_take ?size_cat ?size_nseq; smt(gt0_size size_ge0).
    move=> k hk; have [hq hm] := divmod8 k 32 _ => //.
    have hF : size (flatten (map W256.w2bits l)) = 256 * size l.
    - rewrite (size_flatten_ctt 256) 2:size_map //.
      by move=> bs /mapP [w] [_ ->]; rewrite W256.size_w2bits.
    rewrite nth_take 1,2:/# nth_cat hF BA.get8_of_list256.
    case: (k < 256 * size l) => hkl /=.
    - rewrite ifT; 1: smt(ltz_divLR).
      rewrite (nth_flatten false 256); 1: by rewrite allP => bs /mapP [w] [_ ->].
      rewrite (nth_map W256.zero) 1:#smt:(ltz_divLR size_ge0) W256.get_w2bits W32u8.bits8iE 1:/#.
      by rewrite (_ : 256 = 8 * 32) // hq hm.
    rewrite ifF; 1: smt(ltz_divLR).
    by rewrite nth_nseq_if W8.zerowE; smt().
    qed.
  end GetSet256.
end BArrayBS.

(* -------------------------------------------------------------------- *)
(* Sub-arrays: [get_sub a i] / [set_sub a i s], with [i] in bytes.      *)
(* Instantiate with the extraction's sub-array theory and the bindings  *)
(* of its two byte arrays:                                              *)
(*   clone SubBArrayBS as SBArrayB_SBS with                             *)
(*     theory SBA <- SBArrayB_S,                                        *)
(*     theory BigBS <- BArrayBBS, theory SmallBS <- BArraySBS           *)
(*   proof le_size by done.                                             *)
abstract theory SubBArrayBS.
  clone import SubByteArray as SBA.

  clone BArrayBS as BigBS   with theory BA <- SBA.Abig.
  clone BArrayBS as SmallBS with theory BA <- SBA.Asmall.

  axiom le_size : SBA.Asmall.size <= SBA.Abig.size.

  bind op [SBA.Abig.t & SBA.Asmall.t & W8.t] SBA.get_sub "uextract".

  realize le_size by smt(le_size).

  realize bvuextractP.
  proof.
  move=> a base h0 h1; apply: BigBS.take_drop_tobits; ~-1: smt(SmallBS.size_tobits SmallBS.gt0_size).
  move=> j hj; rewrite SmallBS.nth_tobits 1:/# get8_get_sub.
  by rewrite ifT 1:/#.
  qed.

  bind op [SBA.Abig.t & SBA.Asmall.t & W8.t] SBA.set_sub "uinsert".

  realize le_size by smt(le_size).

  realize bvuinsertP.
  proof.
  move=> a base s h0 h1 /=; apply: BigBS.tobits_ext.
  - by rewrite size_mkseq; smt(BigBS.gt0_size).
  move=> k hk; rewrite nth_mkseq //= get8_set_sub.
  case: (k < base * 8 || base * 8 + 8 * SBA.Asmall.size <= k) => hc.
  - rewrite (nth_change_dfl false) 1:BigBS.size_tobits 1:// BigBS.nth_tobits //.
    by rewrite ifF //; smt().
  rewrite (nth_change_dfl false) 1:SmallBS.size_tobits 1:/# SmallBS.nth_tobits 1:/#.
  rewrite ifT 1:/# (_ : k - base * 8 = k + (-base) * 8) 1:/#.
  by rewrite divzMDr // modzMDr; smt().
  qed.
end SubBArrayBS.
