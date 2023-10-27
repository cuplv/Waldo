(** Secure cryptographic hashing *)
module Waldo.CryptographicHash

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


let hash_length algo = admit()

let hash m algo = admit()

let no_collisions m1 m2 algo = admit()

let bij_hash algo : bijection =
    bij_id
