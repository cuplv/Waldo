module Waldo.Bits

open Waldo.SeqHelpers


let xor_bits #n bs1 bs2 =
  let xor_bitpair = fun (a,b) -> a ^ b in
  let bitpairs: Seq.seq (bit & bit) = (zip #bit #bit #n bs1 bs2) in
  Seq.map_seq xor_bitpair bitpairs

let xor_bits_index #n bs1 bs2 i =
  let xor_bitpair = fun (a,b) -> a ^ b in
  let bitpairs: Seq.seq (bit & bit) = (zip #bit #bit #n bs1 bs2) in
  zip_index #bit #bit #n bs1 bs2 i

let and_bits #n bs1 bs2 =
  let and_bitpair = fun (a,b) -> a && b in
  let bitpairs: Seq.seq (bit & bit) = (zip #bit #bit #n bs1 bs2) in
  Seq.map_seq and_bitpair bitpairs

let and_bits_index #n bs1 bs2 i =
  let and_bitpair = fun (a,b) -> a && b in
  let bitpairs: Seq.seq (bit & bit) = (zip #bit #bit #n bs1 bs2) in
  zip_index #bit #bit #n bs1 bs2 i

let xor_bit_commutative a b = ()

let xor_bits_commutative #n a b =
  assert (Seq.equal (a ^^ b) (b ^^ a))

let xor_bits_associative #n a b c =
  assert (Seq.equal ((a ^^ b) ^^ c) (a ^^ (b ^^ c)))

let xor_bits_inverse #n a b =
  assert (Seq.equal ((a ^^ b) ^^ b) a)

(*** Tests *)

let test_reduce_xor (a b c: bit) =
  assert(
    let bs = Seq.append (Seq.create 1 a) (Seq.append (Seq.create 1 b) (Seq.create 1 c)) in
    reduce_xor bs == a ^ b ^ c
  )
