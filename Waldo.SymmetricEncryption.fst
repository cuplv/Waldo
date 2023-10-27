module Waldo.SymmetricEncryption

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


(** model symmetric encryption by independent random sampling *)
let enc m k =
  let c = rand_bytes (length m) in
  c

(** model symmetric decryption *)
let dec c k = admit ()

let dec_enc_correct m k s
= admit ()

(** Generate a random key of length n *)
let gen_key (n: nat) : Wald (k: bytes {length k == n}) =
  let r = rand_bytes n in r

let bij_sym_enc: bijection =
  bij_id
