(** Custom bytes module modelled after FStar.Bytes, but with unbounded bytestrings *)
module Waldo.Bytes


unfold type byte = FStar.UInt8.t

val bytes : eqtype
val len : bytes -> nat

unfold let length b = len b

type lbytes (l:nat) = b:bytes{length b = l}

val empty_bytes : lbytes 0
val empty_unique:
    b:bytes
  -> Lemma (length b = 0 ==> b = empty_bytes)
    [SMTPat (len b)]

(**  representation for specs that need lemmas not defined here. *)
val reveal:
    bytes
  -> GTot (Seq.seq byte)

val length_reveal:
    x:bytes
  -> Lemma (ensures (Seq.length (reveal x) = length x))
          [SMTPatOr [[SMTPat (Seq.length (reveal x))];
                     [SMTPat (len x)]]]

val hide:
    s:Seq.seq byte
  -> GTot bytes

val hide_reveal:
    x:bytes
  -> Lemma (ensures (hide (reveal x) = x))
          [SMTPat (reveal x)]

val reveal_hide:
    x:Seq.seq byte
  -> Lemma (ensures (reveal (hide x) == x))
          [SMTPat (hide x)]

(** If you statically know the length, it is OK to read at arbitrary indexes *)
val get:
    b:bytes
  -> pos:nat{pos < length b}
  -> Pure byte
    (requires True)
    (ensures (fun y -> y == Seq.index (reveal b) pos))

unfold let op_String_Access = get

let equal b1 b2 =
  length b1 = length b2 /\
  (forall (i:nat{i < length b1}).{:pattern (b1.[i]); (b2.[i])} b1.[i] == b2.[i])

val create:
    len:nat
  -> v:byte
  -> b:lbytes len{forall (i:nat{i < len}).{:pattern b.[i]} b.[i] == v}

(** appending bytes **)
val append:
    b1:bytes
  -> b2:bytes
  -> Pure bytes
         (requires True)
         (ensures (fun b -> reveal b == Seq.append (reveal b1) (reveal b2)))
unfold let op_At_Bar = append

val slice:
    b:bytes
  -> s:nat
  -> e:nat{s <= e /\ e <= length b}
  -> r:bytes{reveal r == Seq.slice (reveal b) s e}

val zip (#n: nat) (a b: lbytes n) : (r: Seq.seq (byte * byte) {Seq.length r == n})

(*
let rec zip (#n: nat) (a b: lbytes n) : (r: Seq.seq (byte * byte) {Seq.length r == n}) =
  if length a = 0
  then Seq.empty
  else 
    let ha, tla = get a 0, slice a 1 n in
    let hb, tlb = get b 0, slice b 1 n in
    let pair = Seq.create 1 (ha, hb) in
    Seq.append pair (zip #(n-1) tla tlb)
*)

val zip_index (#n: nat) (a b: lbytes n) (i: nat{i < n}) : Lemma
  (ensures Seq.index (zip a b) i == (get a i, get b i))

val from_seq (s: Seq.seq byte) : (r: bytes {r == hide s})
val to_seq (bs: bytes) : (s: Seq.seq byte {s == reveal bs})
