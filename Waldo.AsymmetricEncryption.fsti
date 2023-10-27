module Waldo.AsymmetricEncryption

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes


(** asymmetric encryption *)
val enc (m: bytes) (pub_k: bytes) : Wald (c: bytes {length c == length m})

(** asymmetric decryption, may fail without the correct key *)
val dec (c: bytes) (priv_k: bytes) :  (m: option bytes {Some? m ==> length (Some?.v m) == length c})

(** Helper to determine if a public and private keys are a corresponding keypair *)
val is_keypair (pub_k priv_k: bytes) : bool

(** Decryption is the inverse of encryption for corresponding keypairs *)
val dec_enc_correct (m: bytes) (pub_k: bytes) (priv_k: bytes{is_keypair pub_k priv_k}) (s: store) : Lemma
  (ensures (
    let r, _ = reify (enc m pub_k) s in
    // If there's enough randomness to encrypt, then decrypting the ciphertext returns the same message
    Some? r ==> dec (Some?.v r) priv_k == Some m))

(** Generate a private key of length n and public key of length m *)
val gen_key (n m: nat) : Wald ((priv_k: bytes {length priv_k == n}) & (pub_k: bytes {length pub_k == m /\ is_keypair priv_k pub_k}))

val bij_asym_enc: bijection
