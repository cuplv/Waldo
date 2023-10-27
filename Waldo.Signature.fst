(** Cryptographic signatures *)
module Waldo.Signature

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


let sign_length algo = admit()

let sign m priv_k algo =
  let s = rand_bytes (sign_length algo) in
  s

let verify m s pub_k algo = admit()

let is_keypair pub_k priv_k = admit ()

let verify_sign_correct m priv_k pub_k algo s = admit()

let bij_sign algo : bijection =
  bij_id
