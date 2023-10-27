(** Example indistinguishability specification and proof for simple two-message
    One-Time Pad (OTP) protocols. There are two different two-message OTP
    protocols given in this file, one that violates indistinguishability, and
    one that properly guarantees indistinguishability.

    The incorrect (violating) protocol uses the same key to encrypt both
    messages. Re-using the key breaks One-Time Pad encryption (as implied by the
    name). As a result, there is no such bijection that can be provided to
    verify the protocol provides indistinguishability. Such a failed proof
    attempt is given in `otp_proto_same_key_indistinguishable_two_step`.
    However, indistinguishability can be verified if only the first message is
    sent. In this case, the protocol reduces to the one-message OTP protocol.

    The correct protocol uses a new key when encrypting each message. The
    indistinguishability proof can be extended to an arbitrary number of
    messages as long as each message is encrypted with a fresh (new) key.
*)

module TwoMessageOTP

open Waldo.Tape
open Waldo.Effects.Wald
open Waldo.Bytes
open Waldo.BytesHelpers
open Waldo.Indistinguishability
open Waldo.OTP
open Waldo.Xor

module OTP = Waldo.OTP

(** Helper lemma that unfolds the definition of the bijection for OTP
  encryption. This lemma is specialized to 2 messages since that's all we need
  in this example *)
// TODO(klinvill): Some proofs need this lemma, they get an incomplete
// quantifiers error message without it. But this is surprising because the
// lemma discharges somewhat quickly without any additional facts, so it should
// be provable without this lemma.
#push-options "--z3rlimit_factor 5"
let lemma_unfold_concatenated_bij_otp (#n: nat {n + n < size}) (m1 m2: (lbytes n & lbytes n)) : Lemma
  (ensures (
    forall (t: tape).
      let n' = n + n in
      let m1_all = append (fst m1) (snd m1) in
      let m2_all = append (fst m2) (snd m2) in
      let t' = (bij_otp #n' m1_all m2_all).f t in
      equal
        (seq_to_bytes (Waldo.Tape.slice t' (to_id 0) n))
        (slice (xor (xor (seq_to_bytes (Waldo.Tape.slice t (to_id 0) n')) m1_all) m2_all) 0 n)
      /\ equal
        (seq_to_bytes (Waldo.Tape.slice t' (to_id n) (n' - n)))
        (slice (xor (xor (seq_to_bytes (Waldo.Tape.slice t (to_id 0) n')) m1_all) m2_all) n n')
      /\ equal (slice m1_all 0 n)  (fst m1)
      /\ equal (slice m1_all n n') (snd m1)
      /\ equal (slice m2_all 0 n)  (fst m2)
      /\ equal (slice m2_all n n') (snd m2)
  ))
= ()
#pop-options

(** Incorrect 2-message OTP protocol that reuses the same key. The protocol
    involves encrypting and sending message `m1` to participant `j`, and then
    encrypting and sending message `m2` in response to participant `i`. The
    protocol is parameterized on steps to allow for examining the incomplete
    protocol. *)
let otp_proto_same_key (steps: int) (n: nat) (i j: pid) (m1: lbytes n) (m2: lbytes n) : Wald unit =
  if steps > 0
  then
    let k = gen_key n in
    let c1 = OTP.enc m1 k in
    // `trace` records that a message `c1` was sent from `i` to `j`.
    // Indistinguishability is given with respect to these trace calls.
    trace i j c1;
  if steps > 1
  then
    let c2 = OTP.enc m2 k in
    trace j i c2

(** Correct 2-message OTP protocol that generates a new key for encrypting each
    message. The protocol involves encrypting and sending message `m1` to
    participant `j`, and then encrypting and sending message `m2` in response
    to participant `i`. The protocol is parameterized on steps to allow for
    examining the incomplete protocol. *)
let otp_proto_new_key (steps: int) (n: nat) (i j: pid) (m1: lbytes n) (m2: lbytes n) : Wald unit =
  if steps > 0
  then
    let k1 = gen_key n in
    let c1 = OTP.enc m1 k1 in
    trace i j c1;
  if steps > 1
  then
    let k2 = gen_key n in
    let c2 = OTP.enc m2 k2 in
    trace j i c2

(** Wrapper for the incorrect two-message protocol that coerces it into the type
    Waldo expects. In particular, this is a function from public arguments and
    private arguments to a value with the Wald effect. Indistinguishability is
    can then be shown with respect to differing private arguments but the same
    public arguments. This wrapper simply splits the packed secret arguments
    the generic indistinguishability spec and lemma expect into the unpacked
    arguments the protocols expect. *)
unfold let otp_proto_same_key_wrapper : iprotocol =
  fun (pub: int & nat & pid & pid) (priv: (let _,n,_,_=pub in lbytes n & lbytes n)) ->
    let steps, n, i, j = pub in
    let m1, m2 : (lbytes n * lbytes n) = priv in
    otp_proto_same_key steps n i j m1 m2

(** Wrapper for the correct two-message protocol that coerces it into the type
    Waldo expects. In particular, this is a function from public arguments and
    private arguments to a value with the Wald effect. Indistinguishability is
    can then be shown with respect to differing private arguments but the same
    public arguments. This wrapper simply splits the packed secret arguments
    the generic indistinguishability spec and lemma expect into the unpacked
    arguments the protocols expect. *)
unfold let otp_proto_new_key_wrapper : iprotocol =
  fun (pub: int & nat & pid & pid) (priv: (let _,n,_,_=pub in lbytes n & lbytes n)) ->
    let steps, n, i, j = pub in
    let m1, m2 : (lbytes n * lbytes n) = priv in
    otp_proto_new_key steps n i j m1 m2

#push-options "--query_stats --z3rlimit_factor 20"
(** Lemma and proof of indistinguishability for the correct two-messasge
    prototocol. It should succeed because OTP encryption with new keys for each
    encryption provides indistinguishability.

    n needs to be restricted here because the bijection is only defined on a
    finite tape. *)
let otp_proto_new_key_indistinguishable (steps: int) (n: nat {n + n < size}) (i j: pid) (m1 m2: lbytes n & lbytes n) (tr: traceT) : Lemma
  (ensures indistinguishable_ensures otp_proto_new_key_wrapper (steps, n, i, j) m1 m2 tr)
= // Since we sample for two messages, the tape needs to be permuted for both these messages
  let n' = n + n in
  let m1_all = append (fst m1) (snd m1) in
  let m2_all = append (fst m2) (snd m2) in
  let bij = (bij_otp #n' m1_all m2_all) in

  // Unfolds the definition of bij_otp
  lemma_unfold_concatenated_bij_otp m1 m2;
  indistinguishable_lemma otp_proto_new_key_wrapper bij (steps, n, i, j) m1 m2 tr;
  ()
#pop-options


#push-options "--query_stats --z3rlimit_factor 20"
(** Lemma and proof of indistinguishability for only up through first message of
    the incorrect two-message prototocol. It should succeed because OTP
    encryption with one key provides perfect secrecy as long as that key is
    never used more than once.

    This lemma serves to show that the failure to prove perfect secrecy for the
    full protocol is not due to a specification error with the protocol, but
    rather the fact that re-using a key breaks OTP encryption.

    n needs to be restricted here because the bijection is only defined on a
    finite tape. *)
let otp_proto_same_key_indistinguishable_one_step (steps: int) (n: nat {n + n < size}) (i j: pid) (m1 m2: lbytes n & lbytes n) (tr: traceT) : Lemma
  (requires steps == 0 \/ steps == 1)
  (ensures indistinguishable_ensures otp_proto_same_key_wrapper (steps, n, i, j) m1 m2 tr)
= // Since we sample for two messages, the tape needs to be permuted for both these messages
  let n' = n + n in
  let m1_all = append (fst m1) (snd m1) in
  let m2_all = append (fst m2) (snd m2) in
  let bij = (bij_otp #n' m1_all m2_all) in

  // Unfolds the definition of bij_otp
  lemma_unfold_concatenated_bij_otp m1 m2;
  indistinguishable_lemma otp_proto_same_key_wrapper bij (steps, n, i, j) m1 m2 tr;
  ()
#pop-options

(** Lemma and proof of indistinguishability for the incorrect two-message
        prototocol. It fails as expected (indicated by the [@@expect_failure]
        annotation) because re-using a key in one-time pad encryption leaks
        information, thereby violating indistinguishability. In particular, to
        prove indistinguishability we would need a bijection that could permute
        the first n elements of the tape (t[0:n]), which are the bytes that make
        up the key, to always equal both m1_1 ⊕ m2_1 ⊕ t[0:n] and also m1_2 ⊕
        m2_2 ⊕ t[0:n]. This is not possible for cases where m1_1 ⊕ m2_1 != m1_2
        ⊕ m2_2. *)
#push-options "--query_stats --z3rlimit_factor 20 --initial_ifuel 2"
#restart-solver
[@@expect_failure [19]]
let otp_proto_same_key_indistinguishable_two_step (steps: int) (n: nat {n + n < size}) (i j: pid) (m1 m2: lbytes n & lbytes n) (tr: traceT) : Lemma
  (requires steps == 2)
  (ensures indistinguishable_ensures otp_proto_same_key_wrapper (steps, n, i, j) m1 m2 tr)
= // Since we sample for two messages, the tape need to be permuted for both these messages
  let n' = n + n in
  let m1_all = append (fst m1) (snd m1) in
  let m2_all = append (fst m2) (snd m2) in
  let bij = (bij_otp #n' m1_all m2_all) in

  // Unfolds the definition of bij_otp
  lemma_unfold_concatenated_bij_otp m1 m2;
  indistinguishable_lemma otp_proto_same_key_wrapper bij (steps, n, i, j) m1 m2 tr;
  ()
#pop-options
