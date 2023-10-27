module Waldo.OTP

open Waldo.Tape
open Waldo.Bytes
open Waldo.BytesHelpers
open Waldo.Effects.Wald
open Waldo.RandBytes
open Waldo.Xor


(** One-Time Pad encryption, XORs a message with a key at least as long as the message *)
let enc (m: bytes) (k: bytes {length k >= length m}) : (c: bytes {length c == length m}) =
  let k_sub = slice k 0 (length m) in
  xor m k_sub

(** One-Time Pad decryption, identical to encryption *)
let dec (c: bytes) (k: bytes {length k >= length c}) : (m: bytes {length c == length m}) = enc c k

let dec_enc_correct (m: bytes) (k: bytes {length k >= length m}) : Lemma
  (ensures dec (enc m k) k == m)
= ()

(** Generate a random key of length n *)
let gen_key (n: nat) : Wald (lbytes n) =
  let k = rand_bytes n in
  k

(** To prove indistinguishability for one-time-pad encryption, we simply need to provide a bijection where (assuming the first element of the tape, t[0], is sampled as the key) m1 ⊕ t[0] = m2 ⊕ t'[0] where t' is the tape obtained by applying the bijection to t. The bijection that sets t'[0] = m1 ⊕ m2 ⊕ t[0] works in this case. We can see that through substitution (and the commutativity and self-inverse properties of xor): m2 ⊕ t'[0] = m2 ⊕ (m1 ⊕ m2 ⊕ t[0]) = m2 ⊕ m2 ⊕ m1 ⊕ t[0] = m1 ⊕ t[0]. So, this bijection works to prove indistinguishability for xor. We can perform this bijection only up to the length of the tape *)
let bij_otp (#n: nat {n < size}) (m1 m2: lbytes n) =
  let f = fun (t: tape) ->
    let sub = Waldo.Tape.slice t (to_id 0) (length m1) in
    let x = (xor (xor (seq_to_bytes sub) m1) m2) in
    replace t (to_id 0) (bytes_to_seq x)
  in
  let finv = fun t ->
    let sub = Waldo.Tape.slice t (to_id 0) (length m1) in
    let x = (xor (xor (seq_to_bytes sub) m1) m2) in
    replace t (to_id 0) (bytes_to_seq x)
  in
  Bijection f finv
