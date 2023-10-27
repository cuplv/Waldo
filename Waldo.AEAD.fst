module Waldo.AEAD

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


(** model aead encryption by independent random sampling *)
let enc iv m ad k =
  let c = rand_bytes (length m) in
  c

(** model aead decryption *)
let dec iv c ad k = admit ()

let dec_enc_correct iv m ad k s
= admit ()

(** Generate a random key of length n *)
let gen_key n=
  let r = rand_bytes n in r

let bij_aead_enc: bijection =
  bij_id
