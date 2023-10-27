(** Example indistinguishability specification and proof for a simple
    one-message One-Time Pad (OTP) protocol.

    The one-message OTP protocol is one in a participant generates a random key
    at least as long as the message to be encrypted, encrypts the message with
    the key, then sends the encrypted message to the other participant. The
    other participant is assumed to have knowledge of the shared secret key. OTP
    encryption is known to guarantee perfect secrecy (and by extension
    indistinguishability for messages of the same length) as long as the key is
    never re-used. As a result, this protocol preserves indistinguishability of
    observed network traces (of type traceT) which is the information available
    to a passive adversary.
*)
module OneMessageOTP

open Waldo.Bytes
open Waldo.BytesHelpers
open Waldo.Effects.Wald

module Ind = Waldo.Indistinguishability
module OTP = Waldo.OTP


(** Simple one-message OTP encryption protocol. Models sending a message `m` of
      length `n`, encrypted with OTP encryption, from participant `from` to
      participant `to`. *)
let one_msg_proto (n: nat) (from to: pid) (m: lbytes n) : Wald unit =
  // A fresh key is randomly generated and then used to encrypt the message `m`
  let k = OTP.gen_key n in
  let c = OTP.enc m k in
  // `trace` records that a message `c` was sent from `from` to `to`.
  // Indistinguishability is given with respect to these trace calls.
  trace from to c

(** Wrapper for the one-message protocol that coerces it into the type Waldo
    expects. In particular, this is a function from public arguments and private
    arguments to a value with the Wald effect. Indistinguishability is can then
    be shown with respect to differing private arguments but the same public
    arguments. *)
let one_msg_proto_wrapper : Ind.iprotocol =
  fun (pub_args: nat & pid & pid) (priv_args: lbytes (let n,_,_=pub_args in n)) ->
    let n, from, to = pub_args in
    let m = priv_args in
    one_msg_proto n from to m

(** Lemma and proof of indistinguishability for the one-messasge prototocol.

    n needs to be restricted here because the bijection is only defined on a
    finite tape.
*)
let otp_indistinguishable (n: nat {n < Waldo.Tape.size}) (from to: pid) (m1 m2: lbytes n) (tr: traceT) : Lemma
  (ensures Ind.indistinguishable_ensures one_msg_proto_wrapper (n, from, to) m1 m2 tr)
= // Note(klinvill): requires the bytes lemma_eq_elim to be applied. This is
  // done automatically via SMT patterns in the Waldo.ByteHelpers file.
  Ind.indistinguishable_lemma one_msg_proto_wrapper (OTP.bij_otp m1 m2) (n, from, to) m1 m2 tr
