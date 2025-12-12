require import AllCore List IntDiv.
from Jasmin require import JWord JUtils.

from CryptoSpecs require import Bindings.

(* circuit-friendly state mappings *)

abbrev u256_bits64 (w: W256.t) k : W64.t =
 W64.init (fun i => w.[i+64*k]).

lemma u256_bits64E w k:
 0 <= k < 4 =>
 u256_bits64 w k = w \bits64 k.
proof.
move=> Hk; rewrite /u256_bits64.
apply W64.ext_eq => i Hi.
by rewrite bits64E initiE 1://= initiE 1://= /#.
qed.

op u256_pack4 (w0 w1 w2 w3 : W64.t) : W256.t =
 W256.init (fun i => if i < 64 then w0.[i]
                     else if i < 128 then w1.[i-64]
                     else if i < 192 then w2.[i-128]
                     else w3.[i-192]). 

lemma u256_pack4E w0 w1 w2 w3:
 u256_pack4 w0 w1 w2 w3 = pack4 [w0; w1; w2; w3].
proof.
rewrite /u256_pack4; apply W256.ext_eq => k Hk.
rewrite pack4E initiE 1://= initiE 1:// /=.
rewrite get_of_list 1:/# /=.
case: (k < 64) => C1.
+ by rewrite ifT /#.
case: (k < 128) => C2.
+ by rewrite ifF 1:/# ifT /#.
case: (k < 192) => C3.
+ by rewrite ifF 1:/# ifF 1:/# ifT /#.
by rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifT /#.
qed.

lemma u256_pack4_zero:
 u256_pack4 W64.zero W64.zero W64.zero W64.zero = W256.zero.
proof.
by apply W256.all_eq_eq; rewrite /all_eq /u256_pack4 /=.
qed.

op u256_broadcastP w =
 u256_bits64 w 1 = u256_bits64 w 0
 /\ u256_bits64 w 2 = u256_bits64 w 0
 /\ u256_bits64 w 3 = u256_bits64 w 0.

lemma u256_broadcastP_VPBROADCAST w:
 u256_broadcastP (VPBROADCAST_4u64 w).
proof.
rewrite /VPBROADCAST_4u64 /u256_broadcastP.
by rewrite !u256_bits64E 1..4:// !pack4bE 1..4:// /= -iotaredE /=.
qed.

lemma u256_broadcastP_xor w1 w2:
 u256_broadcastP w1 =>
 u256_broadcastP w2 =>
 u256_broadcastP (w1 `^` w2).
proof.
by rewrite /u256_broadcastP !u256_bits64E 1..12:// !xorb64E /#.
qed.


