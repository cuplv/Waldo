(** Authenticated Encryption with Associated Data (AEAD) *)
module Waldo.AEAD

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes


(** AEAD encryption *)
val enc (iv: bytes) (m: bytes) (ad: bytes) (k: bytes) : Wald (c: bytes {length c == length m})
val dec (iv: bytes) (c: bytes) (ad: bytes) (k: bytes) : (m: option bytes {Some? m ==> length (Some?.v m) == length c})

(** Decryption is the inverse of encryption for corresponding keypairs *)
val dec_enc_correct (iv: bytes) (m: bytes) (ad: bytes) (k: bytes) (s: store) : Lemma
  (ensures (
    let r, _ = reify (enc iv m ad k) s in
    // If there's enough randomness to encrypt, then decrypting the ciphertext returns the same message
    Some? r ==> dec iv (Some?.v r) ad k == Some m))

(** Generate a random key of length n *)
val gen_key (n: nat) : Wald (k: bytes {length k == n})

val bij_aead_enc: bijection
