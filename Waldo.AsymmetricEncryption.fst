module Waldo.AsymmetricEncryption

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


(** model asymmetric encryption by independent random sampling *)
let enc m pub_k =
  let c = rand_bytes (length m) in
  c

(** model asymmetric decryption *)
let dec c priv_k = admit ()

let is_keypair pub_k priv_k = admit ()

let dec_enc_correct m pub_k priv_k s
= admit ()

(** Generate a random key of length n *)
let gen_key n m =
  let priv_k = rand_bytes n in
  let pub_k = rand_bytes m in
  assume(is_keypair pub_k priv_k);
  (|priv_k, pub_k|)

let bij_asym_enc: bijection =
  bij_id
