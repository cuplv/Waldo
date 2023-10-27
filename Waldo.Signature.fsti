(** Cryptographic signatures *)
module Waldo.Signature

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes

type algorithm = string

(** Signatures using the same algorithm have the same length *)
val sign_length (algo: algorithm) : nat

val sign (m: bytes) (priv_k: bytes) (algo: algorithm) : Wald (s: bytes {length s == sign_length algo})
val verify (m: bytes) (s: bytes) (pub_k: bytes) (algo: algorithm {length s == sign_length algo}) : bool

(** Helper to determine if a public and private keys are a corresponding keypair *)
val is_keypair (pub_k priv_k: bytes) : bool

val verify_sign_correct (m: bytes) (priv_k: bytes) (pub_k: bytes{is_keypair pub_k priv_k}) (algo: algorithm) (s: store) : Lemma
  (ensures (
    let r, _ = reify (sign m priv_k algo) s in
    // If there's enough randomness to sign a message, then verifying that message with the corresponding key will succeed
    Some? r ==> verify m (Some?.v r) pub_k algo))

val bij_sign (algo: algorithm) : bijection
