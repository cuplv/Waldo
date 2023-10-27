module Waldo.MAC

open Waldo.Effects.Wald
open Waldo.Bijections
open Waldo.Bytes
open Waldo.RandBytes


let mac_length algo = admit()

let mac m k algo =
  let s = rand_bytes (mac_length algo) in
  s

let verify m s k algo = admit()

let is_keypair k = admit ()

let verify_mac_correct m k algo s = admit()

let bij_mac algo : bijection =
  bij_id
