(** Message Authentication Codes (MACs) *)
module Waldo.MAC

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes


type algorithm = string

(** MACs using the same algorithm have the same length *)
val mac_length (algo: algorithm) : nat

val mac (m: bytes) (k: bytes) (algo: algorithm) : Wald (s: bytes {length s == mac_length algo})
val verify (m: bytes) (s: bytes) (k: bytes) (algo: algorithm {length s == mac_length algo}) : bool

val verify_mac_correct (m: bytes) (k: bytes) (algo: algorithm) (s: store) : Lemma
  (ensures (
    let r, _ = reify (mac m k algo) s in
    // If there's enough randomness to generate a mac, then verifying that message with the correct key will succeed
    Some? r ==> verify m (Some?.v r) k algo))

val bij_mac (algo: algorithm) : bijection
