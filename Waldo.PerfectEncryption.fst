module Waldo.PerfectEncryption

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


(** Models perfect encryption, generates a string of random bytes as long as the input plaintext *)
let enc (m: bytes) (k: bytes) : Wald (c: bytes {length c == length m}) =
    let c = rand_bytes (length m) in
    c

(** Generate a random key of length n *)
let gen_key (n: nat) : Wald (k: bytes) =
    let k = rand_bytes n in
    k

// We only need to use the identity bijection when assuming perfect encryption
let bij_perfect_enc: bijection = bij_id
