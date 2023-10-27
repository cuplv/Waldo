module Waldo.BytesHelpers

open Waldo.Bytes


// TODO(klinvill): tapes are currently defined as sequences of elements, but I only use them as sequences of bytes. Should this be kept generic? If so, there needs to be a way to convert between a slice of the tape (which produces a seq) and its expected equivalent bytes, and vice versa.
assume val seq_to_bytes (l: Seq.seq byte) : (r: bytes {equal r (hide l)})
assume val bytes_to_seq (l: bytes) : (r: Seq.seq byte {Seq.equal r (reveal l)})

// TODO(klinvill): shouldn't need to admit this
let bytes_get_and_seq_index_equiv (s: Seq.seq byte) (i: nat {i < Seq.length s}) : Lemma
  (ensures (
    let b = seq_to_bytes s in
    get b i == Seq.index s i
  ))
  // TODO(klinvill): should we use this lemma automatically? How often do we really need it?
  [SMTPat (get (seq_to_bytes s) i)]
= admit ()


// TODO(klinvill): shouldn't need to admit this
let lemma_eq_elim (a b: bytes) : Lemma
  (requires equal a b)
  (ensures a == b)
  [SMTPat (equal a b)]
= admit ()
