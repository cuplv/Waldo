module Waldo.Bits

type bit = bool

(** Convenient literal notation for bits *)
let _0, _1 = false, true

type bits = Seq.seq bit
type lbits (n: nat) = (bs: bits {Seq.length bs = n})

let xor (a b: bit) = if a then not b else b
let (^) = xor

val xor_bits (#n: nat) (bs1 bs2: lbits n) : lbits n
let (^^) (#n: nat) = xor_bits #n

val xor_bits_index (#n: nat) (bs1 bs2: lbits n) (i: nat{i < n}): Lemma
  (ensures Seq.index (bs1 ^^ bs2) i = (Seq.index bs1 i) ^ (Seq.index bs2 i))
  [SMTPat (Seq.index (xor_bits bs1 bs2) i)]

val and_bits (#n: nat) (bs1 bs2: lbits n) : lbits n
let (&&&) (#n: nat) = and_bits #n

val and_bits_index (#n: nat) (bs1 bs2: lbits n) (i: nat{i < n}): Lemma
  (ensures Seq.index (bs1 &&& bs2) i = ((Seq.index bs1 i) && (Seq.index bs2 i)))
  [SMTPat (Seq.index (and_bits bs1 bs2) i)]

let reduce_xor (bs: bits) : bit =
  Seq.foldr xor bs _0

val xor_bit_commutative (a b: bit) : Lemma
  (ensures a ^ b == b ^ a)

val xor_bits_commutative (#n: nat) (a b: lbits n) : Lemma
  (ensures a ^^ b == b ^^ a)
  [SMTPat (xor_bits a b)]

val xor_bits_associative (#n: nat) (a b c: lbits n) : Lemma
  (ensures (a ^^ b) ^^ c == a ^^ (b ^^ c))
  [SMTPat (xor_bits (xor_bits a b) c)]

val xor_bits_inverse (#n: nat) (a b: lbits n) : Lemma
  (ensures (a ^^ b) ^^ b == a)
  [SMTPat (xor_bits (xor_bits a b) b)]


(*** Tests *)

(** Test smt patterns to make sure they're applied for both the notation and terms *)
let test_xor_patterns (n: nat) (a b c: lbits n) =
  assert (a ^^ b == b ^^ a);
  assert (xor_bits a b == xor_bits b a);
  assert ((a ^^ b) ^^ c == a ^^ (b ^^ c));
  assert (xor_bits (xor_bits a b) c == xor_bits a (xor_bits b c));
  assert ((a ^^ b) ^^ b == a);
  assert (xor_bits (xor_bits a b) b == a);
  assert (forall (i:nat{i < n}). Seq.index (a ^^ b) i == (Seq.index a i) ^ (Seq.index b i));
  assert (forall (i:nat{i < n}). Seq.index (xor_bits a b) i == xor (Seq.index a i) (Seq.index b i))

let test_and_patterns (n: nat) (a b: lbits n) =
  assert (forall (i:nat{i < n}). Seq.index (a &&& b) i == ((Seq.index a i) && (Seq.index b i)));
  assert (forall (i:nat{i < n}). Seq.index (and_bits a b) i == ((Seq.index a i) && (Seq.index b i)))
