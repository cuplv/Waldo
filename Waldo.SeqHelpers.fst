module Waldo.SeqHelpers

(** Zip two sequences of elements into a sequence of tuples of those elements *)
val zip (#ta #tb: Type) (#n: nat) (a: Seq.seq ta{Seq.length a = n}) (b: Seq.seq tb{Seq.length b = n}) : (r: Seq.seq (ta & tb) {Seq.length r = n})
let rec zip #ta #tb #n a b =
  if n = 0
  then Seq.empty
  else 
    let ha, tla = Seq.index a 0, Seq.slice a 1 n in
    let hb, tlb = Seq.index b 0, Seq.slice b 1 n in
    let pair = Seq.create 1 (ha, hb) in
    Seq.append pair (zip #ta #tb #(n-1) tla tlb)

val zip_index (#ta #tb: Type) (#n: nat) (a: Seq.seq ta{Seq.length a = n}) (b: Seq.seq tb{Seq.length b = n}) (i: nat{i < n}) : Lemma
  (ensures Seq.index (zip #ta #tb #n a b) i == (Seq.index a i, Seq.index b i))
let rec zip_index #ta #tb #n a b i =
  if i = 0
  then ()
  else 
    let a' = Seq.slice a 1 n in
    let b' = Seq.slice b 1 n in
    zip_index #ta #tb #(n-1) a' b' (i-1)

(*** Lemmas to have z3 automatically apply *)

let lemma_map_seq_len (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a)
  : Lemma (ensures Seq.length (Seq.map_seq f s) == Seq.length s)
  [SMTPat (Seq.length (Seq.map_seq f s))]
= Seq.map_seq_len f s

let lemma_map_seq_index (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures (Seq.map_seq_len f s; Seq.index (Seq.map_seq f s) i == f (Seq.index s i)))
  [SMTPat (Seq.index (Seq.map_seq f s) i)]
= Seq.map_seq_index f s i

let lemma_map_seq_append (#a #b:Type) (f:a -> Tot b) (s1 s2:Seq.seq a)
  : Lemma (ensures (Seq.map_seq f (Seq.append s1 s2) ==
                    Seq.append (Seq.map_seq f s1) (Seq.map_seq f s2)))
  [SMTPat (Seq.map_seq f (Seq.append s1 s2))]
= Seq.map_seq_append f s1 s2
