(*
   Adapted from the FStar.DM4F.Heap.Random.fst file produced by Microsoft.
   That file carried the following copyright and license:

   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Waldo.Tape

(***** Random tape *****)

open FStar.Seq

let q = admit ()

type id = i:nat{i < size}

type tape #e = h:seq (elem #e){length h == size}

let to_id (n:nat{n < size}) : id = n

let to_nat i = i

let id_lteq i j = i <= j

let incrementable (i:id) = i + 1 < size

let incr (i:id{incrementable i}) : id = to_id (i + 1)

let incrementable_by_n (i:id) (n:nat) = i + n < size

let incr_n (i:id) (n:nat{incrementable_by_n i n}) : id = to_id (i + n)

let test_incrementable_by_1_eq_incrementable (i: id) : Lemma
  (ensures incrementable_by_n i 1 == incrementable i)
= ()

let test_incr_1_eq_incr (i: id {incrementable i}) : Lemma
  (ensures incr_n i 1 == incr i)
= ()

let test_always_incrementable_by_0 (i: id) : Lemma
  (ensures incrementable_by_n i 0)
= ()

let test_incr_0_eq_id (i: id) : Lemma
  (ensures incr_n i 0 == i)
= ()

let largest_id = size - 1

let incrementable_if_next_id_lt_size (x: nat) = ()
let incr_increases_by_one (x: nat) = ()
let incr_increases_by_one' (i: id) = ()
let incrementable_by_n_if_new_id_lt_size (x: nat) (n: nat) = ()
let incr_n_increases_by_n (x: nat) (n: nat) = ()
let incr_n_increases_by_n' (i: id) (n: nat) = ()

let remaining_samples (i: id) = size - i - 1
let incrementable_if_remaining_samples (i: id) = ()
let remaining_samples_incr_one_less (i: id) = ()

let incrementable_by_lt_n_if_incrementable_by_n (i: id) (n: nat) = ()
let incrementable_by_n_but_not_by_prev_n_means_i_plus_n_is_size (i: id) (n: nat {n > 0}) = ()

let to_id_injective n1 n2 = ()

let id_lteq_if_nat_lteq i j = ()

let id_lt i j = i < j
let id_lt_if_nat_lt i j = ()

let lemma_lt_implies_lteq i j = ()
let lemma_lt_implies_incrementable i j = ()
let lemma_lt_implies_incr_lteq i j = ()

let slice (t:tape) (i:id) (n:nat{to_id i + n <= size}) =
  let j = i+n in
  Seq.Base.slice t i j

(* Ensures that all elements on the tape can be sampled using slice *)
let test_slice_of_size_returns_whole_tape (t:tape) : Lemma
  (ensures slice t 0 size == t)
= ()

let index (h:tape) (i:id) : Tot elem = index h i

let upd (h:tape) (i:id) (x:elem) : Tot tape = upd h i x

let replace (dst: tape) (i:id) (src: seq elem {(to_nat i) + (Seq.length src) <= size}) : Tot tape =
  let end_index = i + Seq.length src in
  let p1 = Seq.slice dst 0 i in
  let p2 = src in
  let p3 = Seq.slice dst end_index size in
  Seq.append p1 (Seq.append p2 p3)

let create #e (x:elem) : Tot tape = create #elem size x

let equal #e (t1:tape #e) (t2:tape #e) = Seq.equal t1 t2

let lemma_eq_intro s1 s2 =
  assert (forall (i:id). index s1 i == Seq.index s1 i);
  assert (forall (i:id). index s2 i == Seq.index s2 i);
  Seq.lemma_eq_intro #elem s1 s2

let lemma_eq_elim s1 s2 = ()

let lemma_index_upd1 s n v = lemma_index_upd1 #elem s n v

let lemma_index_upd2 s n v i = lemma_index_upd2 #elem s n v i

let lemma_index_create v i = lemma_index_create #elem size v i

let lemma_len_slice (t:tape) (i:id) (n:nat{to_nat i + n <= size}) = ()

let lemma_index_slice (t:tape) (i:id) (n:nat{to_nat i + n <= size}) (k:nat{k < n}) = ()

let lemma_index_replace1 (t: tape) (i: id) (xs: seq elem) (j: id) = ()

let lemma_index_replace2 (t: tape) (i: id) (xs: seq elem) (j: id) = ()

let rec lemma_slice_replace1 #e (t: tape) (i: id) (n:nat{to_nat i + n <= size}) (xs: seq elem) : Lemma
  (requires Seq.length xs == n)
  (ensures Seq.equal (slice (replace t i xs) i n) xs)
  (decreases (Seq.length xs))
= match Seq.length xs with
  | 0 | 1 -> ()
  | _ -> lemma_slice_replace1 t (incr i) (n-1) (Seq.tail xs)

let lemma_slice_cons t i n = ()

let rec _lemma_slice_cons2 (t: tape) (i: id {incrementable i}) (n:nat{to_nat i + n <= size /\ n > 0}) : Lemma
  (ensures Seq.equal
    (slice t i n)
    (Seq.append (Seq.create 1 (Seq.index (slice t i n) 0)) (slice t (incr i) (n-1))))
  (decreases n)
= match n with
  | 0 | 1 -> ()
  | _ -> let i' = incr i in
    if incrementable i'
    then _lemma_slice_cons2 t i' (n-1)
    else ()

let lemma_slice_cons2 t i n =
  _lemma_slice_cons2 t i n
