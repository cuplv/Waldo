module Waldo.SymmetricEncryption

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes


(** symmetric encryption *)
val enc (m: bytes) (k: bytes) : Wald (c: bytes {length c == length m})

(** symmetric decryption, may fail without the correct key *)
val dec (c: bytes) (k: bytes) :  (m: option bytes {Some? m ==> length (Some?.v m) == length c})

val dec_enc_correct (m: bytes) (k: bytes) (s: store) : Lemma
  (ensures (
    let r, _ = reify (enc m k) s in
    // If there's enough randomness to encrypt, then decrypting the ciphertext with the same key succeeds and returns the same message
    Some? r ==> dec (Some?.v r) k == Some m))

(** Generate a random key of length n *)
val gen_key (n: nat) : Wald (k: bytes {length k == n})

val bij_sym_enc: bijection
