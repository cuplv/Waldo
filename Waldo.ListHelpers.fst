module Waldo.ListHelpers

open FStar.List.Tot


val cut_last (#a: Type) (l: list a{length l > 0}) : (r: list a{length r == length l - 1})
let cut_last #a l =
  let l', _ = unsnoc l in
  lemma_unsnoc_length l;
  l'

val cut_last_preserves_other_elems (#a: Type) (l: list a{length l > 0}) (j: nat{j < length l - 1}) : Lemma
  (ensures index (cut_last l) j == index l j)
  [SMTPat (index (cut_last #a l) j)]
let rec cut_last_preserves_other_elems #a l j =
  match l, j with
  | _, 0 -> ()
  | h :: tl, _ -> cut_last_preserves_other_elems tl (j - 1)

(** Zip two lists of elements into a list of tuples of those elements *)
val zip (#ta #tb: Type) (#n: nat) (a: list ta{length a = n}) (b: list tb{length b = n}) : (r: list (ta & tb) {length r = n})
let rec zip #ta #tb #n a b =
  if n = 0
  then []
  else
    let ha :: tla, hb :: tlb = a, b in
    let pair = (ha, hb) in
    pair :: (zip #ta #tb #(n-1) tla tlb)

val zip_index (#ta #tb: Type) (#n: nat) (a: list ta{length a = n}) (b: list tb{length b = n}) (i: nat{i < n}) : Lemma
  (ensures index (zip #ta #tb #n a b) i == (index a i, index b i))
  [SMTPat (index (zip #ta #tb #n a b) i)]
let rec zip_index #ta #tb #n a b i =
  if i = 0
  then ()
  else
    let _ :: a', _ :: b' = a, b in
    zip_index #ta #tb #(n-1) a' b' (i-1)
