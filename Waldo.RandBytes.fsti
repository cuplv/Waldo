module Waldo.RandBytes

open Waldo.BytesHelpers
open Waldo.Bytes
open Waldo.Effects.Wald
open Waldo.Tape

(** Returns n random bytes *)
val rand_bytes (n: ℕ) : Wald (lbytes n)

// If only 1 byte is sampled, then rand_bytes is equivalent to sample.
// This postcondition is shared by multiple lemmas.
unfold let rand_bytes_1_equiv_to_sample_post (i: id) (t: tape) (tr: traceT) : Type0 =
  let (r1, s1) = reify (rand_bytes 1) (i, t, tr) in
  let (r2, s2) = reify (sample ()) (i, t, tr)  in
  s1 == s2
  /\ Some? r1 == Some? r2
  /\ (Some? r2 ==> Waldo.Bytes.get (Some?.v r1) 0 == Some?.v r2)

// Automatically applied by SMT solver
val rand_bytes_1_equiv_to_sample (i: id) (t: tape) (tr: traceT) : Lemma
  (ensures (rand_bytes_1_equiv_to_sample_post i t tr))
  [SMTPat (reify (rand_bytes 1) (i, t, tr))]

// Can be applied once regardless of number of ids you need to reason about
val rand_bytes_1_equiv_to_sample_fully_quantified (_: unit) : Lemma
  (ensures (forall (i: id) (t: tape) (tr: traceT).
    rand_bytes_1_equiv_to_sample_post i t tr
  ))

// If n bytes are sampled, then rand_bytes is equivalent to an n-length slice of the tape
val rand_bytes_n_equiv_to_slice (i: id) (t: tape) (n: nat) (tr: traceT) : Lemma
  (ensures (
    let (r, s) = reify (rand_bytes n) (i, t, tr) in
    if incrementable_by_n i n
    then Some? r
      /\ Waldo.Bytes.equal (Some?.v r) (seq_to_bytes (slice t i n))
      /\ s == (incr_n i n, tr)
    // Failed because tried to read past end of tape. The id should now be at the end of the tape.
    else None? r /\ s == (largest_id, tr)
  ))
  [SMTPat (reify (rand_bytes n) (i, t, tr))]
