(*
   Adapted from the FStar.DM4F.Heap.Random.fsti file produced by Microsoft.
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

let size = 320000

val q: pos

let elem (#e:eqtype) = e

val id : eqtype

val tape (#e:eqtype) : Type0

val to_id (n:nat{n < size}) : id

val to_nat (i:id) : (n:nat {n < size /\ to_id n == i})

val id_lteq (i j:id) : Tot (b:bool {∀ x y. to_id x == i ∧ to_id y == j ==> b == (x ≤ y)})

val incrementable: id -> bool

val incr (i:id{incrementable i}) : (i':id {id_lteq i i'})

val incrementable_by_n : (i:id) -> (n:nat) -> (r: bool{r = (to_nat i + n < size)})

val incr_n (i:id) (n:nat{incrementable_by_n i n}) : (i':id {id_lteq i i'})

val largest_id : (i: id {~(incrementable i) /\ to_nat i == size - 1})

// TODO(klinvill): I seem to need these lemmas to prove that sample () in Waldo.Effects.Wald.fst will return an element when the index is less than size and will properly increment the id value. Is there a more elegant way to do this?
val incrementable_if_next_id_lt_size (x: nat) : Lemma (requires x + 1 < size) (ensures incrementable (to_id x))
val incr_increases_by_one (x: nat) : Lemma (requires x + 1 < size /\ incrementable (to_id x)) (ensures incr (to_id x) == to_id (x + 1))
val incr_increases_by_one' (i: id) : Lemma (requires incrementable i) (ensures (to_nat i) + 1 < size /\ incr i == to_id ((to_nat i) + 1))
val incrementable_by_n_if_new_id_lt_size (x: nat) (n: nat) : Lemma (requires x + n < size) (ensures incrementable_by_n (to_id x) n)
val incr_n_increases_by_n (x: nat) (n: nat) : Lemma (requires x + n < size /\ incrementable_by_n (to_id x) n) (ensures incr_n (to_id x) n == to_id (x + n))
val incr_n_increases_by_n' (i: id) (n: nat) : Lemma (requires incrementable_by_n i n) (ensures (to_nat i) + n < size /\ incr_n i n == to_id ((to_nat i) + n)) [SMTPat (incr_n i n)]

val remaining_samples (i: id) : (r: nat {r < size /\ to_id (size - r - 1) = i})
val incrementable_if_remaining_samples (i: id) : Lemma (requires remaining_samples i > 0) (ensures incrementable i)
val remaining_samples_incr_one_less (i: id) : Lemma (requires remaining_samples i > 0) (ensures incrementable i /\ remaining_samples (incr i) == (remaining_samples i) - 1) [SMTPat (remaining_samples (incr i))]

val incrementable_by_lt_n_if_incrementable_by_n (i: id) (n: nat) : Lemma (requires incrementable_by_n i n) (ensures forall (m: nat {m < n}). incrementable_by_n i m)
val incrementable_by_n_but_not_by_prev_n_means_i_plus_n_is_size (i: id) (n: nat {n > 0}) : Lemma (requires incrementable_by_n i (n-1) /\ ~(incrementable_by_n i n)) (ensures to_nat i + n == size)

// Needed to prove: `remaining_samples (to_id 0) == size - 1`
val to_id_injective (n1 n2:nat) : Lemma
  (requires n1 < size /\ n2 < size /\ to_id n1 == to_id n2)
  (ensures n1 == n2)
  [SMTPat (to_id n1); SMTPat (to_id n2)]

val id_lteq_if_nat_lteq (i j:id) : Lemma
  (requires to_nat i <= to_nat j)
  (ensures id_lteq i j)
  [SMTPat (id_lteq i j)]

val id_lt (i j:id) : Tot (b:bool {∀ x y. to_id x == i ∧ to_id y == j ==> b == (x < y)})
val id_lt_if_nat_lt (i j:id) : Lemma
  (requires to_nat i < to_nat j)
  (ensures id_lt i j)
  [SMTPat (id_lt i j)]

val lemma_lt_implies_lteq (i j:id) : Lemma
  (requires id_lt i j)
  (ensures id_lteq i j)
  [SMTPat (id_lt i j)]

val lemma_lt_implies_incrementable (i j:id) : Lemma
  (requires id_lt i j)
  (ensures incrementable i)
  [SMTPat (id_lt i j)]

val lemma_lt_implies_incr_lteq (i j:id) : Lemma
  (requires id_lt i j)
  (ensures id_lteq (incr i) j)
  [SMTPat (id_lt i j)]

(** Slice of tape n elements long starting from index i (inclusive) *)
val slice (#e:eqtype) (t:tape #e) (i:id) (n:nat{to_nat i + n <= size}) : Tot (r: seq (elem #e) {Seq.length r == n})

val index (#e:eqtype) (t:tape #e) (i:id) : Tot (elem #e)
let sel = index

val upd (#e:eqtype) (t:tape #e) (i:id) (x:elem #e) : Tot (tape #e)

val replace (#e:eqtype) (dst: tape #e) (i:id) (src: seq (elem #e) {(to_nat i) + (Seq.length src) <= size}) : Tot (tape #e)

val create (#e:eqtype) (x:elem #e) : Tot (tape #e)

val equal: (#e:eqtype) -> tape #e -> tape #e -> GTot Type0

val lemma_eq_intro: (#e:eqtype) -> s1:tape #e -> s2:tape #e -> Lemma
  (requires ((forall (i:id).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)))
  (ensures (equal s1 s2))
  [SMTPat (equal s1 s2)]

val lemma_eq_elim: (#e:eqtype) -> s1:tape #e -> s2:tape #e -> Lemma
  (requires (equal s1 s2))
  (ensures (s1==s2))
  [SMTPat (equal s1 s2)]

val lemma_index_upd1: (#e:eqtype) -> s:tape #e -> n:id -> v:elem #e -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]

val lemma_index_upd2: (#e:eqtype) -> s:tape #e -> n:id -> v:elem #e -> i:id{i<>n} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]

val lemma_index_create: (#e:eqtype) -> v:elem #e -> i:id -> Lemma
  (requires True)
  (ensures (index (create v) i == v))
  [SMTPat (index (create v) i)]

val lemma_len_slice (#e:eqtype) (t:tape #e) (i:id) (n:nat{to_nat i + n <= size}) : Lemma
  (ensures (Seq.length (slice t i n) = n))
  [SMTPat (Seq.length (slice t i n))]

val lemma_index_slice (#e:eqtype) (t:tape #e) (i:id) (n:nat{to_nat i + n <= size}) (k:nat{k < n}) : Lemma
  (ensures (Seq.index (slice t i n) k == index t (to_id ((to_nat i) + k))))
  [SMTPat (Seq.index (slice t i n) k)]

val lemma_index_replace1: (#e:eqtype) -> t: tape #e -> i: id -> xs: seq (elem #e) -> j: id -> Lemma
  (requires
    (to_nat i) + (Seq.length xs) < size
    // j inside the range of the replaced indices
    /\ (to_nat j) < (to_nat i) + (Seq.length xs)
    /\ (to_nat j) >= (to_nat i))
  (ensures (index (replace t i xs) j == Seq.index xs (to_nat j - to_nat i)))
  [SMTPat (index (replace t i xs) j)]

val lemma_index_replace2: (#e:eqtype) -> t: tape #e -> i: id -> xs: seq (elem #e) -> j: id -> Lemma
  (requires
    (to_nat i) + (Seq.length xs) < size
    // j outside the range of the replaced indices
    /\ (
      ((to_nat j) >= (to_nat i) + (Seq.length xs) /\ to_nat j < size)
      \/ (to_nat j) < (to_nat i)))
  (ensures (index (replace t i xs) j == index t j))
  [SMTPat (index (replace t i xs) j)]

(** Specifies that taking the slice of the replaced section of the tape always returns what the replaced section was replaced with. *)
val lemma_slice_replace1 (#e:eqtype) (t: tape #e) (i: id) (n:nat{to_nat i + n <= size}) (xs: seq (elem #e)) : Lemma
  (requires Seq.length xs == n)
  (ensures Seq.equal (slice (replace t i xs) i n) xs)
  [SMTPat (slice (replace t i xs) i n)]

val lemma_slice_cons (#e:eqtype) (t: tape #e) (i: id {incrementable i}) (n:nat{to_nat i + n <= size /\ n > 0}) : Lemma
  (ensures forall x. mem x (slice t i n) <==> (x = index t i || (incr_increases_by_one' i; mem x (slice t (incr i) (n - 1)))))

val lemma_slice_cons2 (#e:eqtype) (t: tape #e) (i: id {incrementable i}) (n:nat{to_nat i + n <= size /\ n > 0}) : Lemma
  (ensures incr_increases_by_one' i; slice t i n == Seq.append (Seq.create 1 (index t i)) (slice t (incr i) (n - 1)))
