module Waldo.Xor

open Waldo.Bytes


val xor (a: bytes) (b: bytes {length a == length b}) : Tot (c: bytes {length c == length a})

val xor_commutative (a: bytes) (b: bytes {length a == length b}) : Lemma
  (ensures xor a b == xor b a)
  [SMTPat (xor a b)]

val xor_associative (a: bytes) (b: bytes {length a == length b}) (c: bytes {length a == length c}) : Lemma
  (ensures xor (xor a b) c == xor a (xor b c))
  [SMTPat (xor (xor a b) c)]

val xor_inverse (a: bytes) (b: bytes {length a == length b}) : Lemma
  (ensures xor (xor a b) b == a)
  [SMTPat (xor (xor a b) b)]

val xor_slice_distributive
  (a: bytes)
  (b: bytes {length a == length b})
  (i: nat {i <= length a})
  (j: nat {j >= i /\ j <= length a})
  : Lemma
  (ensures (
    equal
      (slice (xor a b) i j)
      (xor (slice a i j) (slice b i j))
  ))
  [SMTPat (slice (xor a b) i j)]
