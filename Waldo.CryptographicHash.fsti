(** Secure cryptographic hashing *)
module Waldo.CryptographicHash

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes


type algorithm = string

(** Hashes using the same algorithm have the same length *)
val hash_length (algo: algorithm) : nat

val hash (m: bytes) (algo: algorithm) : Wald (s: bytes {length s == hash_length algo})

(** Hash collisions are assumed to not happen *)
val no_collisions (m1 m2 : bytes) (algo: algorithm) (s: store) : Lemma
    (ensures (
        let r1, _ = reify (hash m1 algo) s in
        let r2, _ = reify (hash m2 algo) s in
        Some? r1 /\ Some? r2 /\ r1 == r2 ==> m1 == m2))

val bij_hash (algo: algorithm) : bijection
