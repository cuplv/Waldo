module Waldo.Xor

open FStar.BV


let xor_byte (a b: byte) : byte =
  let a_bv = int2bv (UInt8.v a) in
  let b_bv = int2bv (UInt8.v b) in
  let c_bv = bvxor a_bv b_bv in
  UInt8.uint_to_t (bv2int c_bv)

let rec xor (a: bytes) (b: bytes {length a == length b}) : Tot (c: bytes {length c == length a}) (decreases length b) =
  match length a with
  | 0 -> empty_bytes
  | _ ->
    let a_h: byte = get a 0 in
    let a_tl = slice a 1 (length a) in
    let b_h: byte = get b 0 in
    let b_tl = slice b 1 (length b) in
    let c_h = xor_byte a_h b_h in
    append (create 1 c_h) (xor a_tl b_tl)

let xor_byte_commutative (a b: byte) : Lemma
  (ensures xor_byte a b == xor_byte b a)
  [SMTPat (xor_byte a b)]
= admit ()

let xor_byte_associative (a b c: byte) : Lemma
  (ensures xor_byte (xor_byte a b) c == xor_byte a (xor_byte b c))
  [SMTPat (xor_byte (xor_byte a b) c)]
= admit ()

let xor_byte_inverse (a b: byte) : Lemma
  (ensures xor_byte (xor_byte a b) b == a)
  [SMTPat (xor_byte (xor_byte a b) b)]
= admit ()

let xor_commutative (a: bytes) (b: bytes {length a == length b}) : Lemma
  (ensures xor a b == xor b a)
  [SMTPat (xor a b)]
= admit ()

let xor_associative (a: bytes) (b: bytes {length a == length b}) (c: bytes {length a == length c}) : Lemma
  (ensures xor (xor a b) c == xor a (xor b c))
  [SMTPat (xor (xor a b) c)]
= admit ()

let xor_inverse (a: bytes) (b: bytes {length a == length b}) : Lemma
  (ensures xor (xor a b) b == a)
  [SMTPat (xor (xor a b) b)]
= admit ()

let xor_slice_distributive
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
= admit ()

#push-options "--query_stats"
let test_xor_byte (a b c: byte) : Lemma
  (ensures (
    let fn (h: byte)  = xor_byte (xor_byte h a) b in
    // Effectively: xor_byte (xor_byte (xor_byte (xor_byte c a) b) a) b
    fn (fn c) == c))
= ()
#pop-options

#push-options "--query_stats"
let test_xor (a: bytes) (b: bytes {length a == length b}) (c: bytes {length a == length c}) : Lemma
  (ensures (
    let fn (h: bytes {length h == length a})  = xor (xor h a) b in
    // Effectively: xor (xor (xor (xor c a) b) a) b
    fn (fn c) == c))
= ()
#pop-options
