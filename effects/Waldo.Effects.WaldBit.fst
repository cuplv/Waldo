(*
   Adapted from the FStar.DM4F.Random.fst file produced by Microsoft.
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
module Waldo.Effects.WaldBit

(** TODO(klinvill): The WALD effect should be polymorphic so we can have effects for tapes of different elements. There are some challenges with that since only indexed/layered effects can be polymorphic and indexed effects do not support reification, which we heavily rely upon. Remove this module whenever we have a polymorphic WALD effect *)

open Waldo.Bits
open Waldo.Tape

type pid = string
type traceT = list (pid & pid & bits)

(* for some reason this `unfold` makes everything 25% faster *)
unfold type store = id & tape #bit & traceT

(** Initial state starts from the beginning of the tape and contains an empty trace. *)
val init_store (t: tape) : (s: store{s == (to_id 0, t, [])})
let init_store t = to_id 0, t, []

unfold let writeable (s: store) : id & traceT =
  let next, _, tr = s in
  next, tr

(** Read-only tape with a pointer to the next unread position, along with a trace of network messages *)
type wald (a:Type) = store -> M (option a & (id & traceT))

let return (a:Type) (x:a) : wald a = fun (next,_,tr) -> Some x, (next, tr)

let bind (a b:Type) (c:wald a) (f:a -> wald b) : wald b =
  fun s ->
    let _, t, _ = s in
    let r, (next', tr') = c s in
    match r with
    | None   -> None, (next', tr')
    | Some x -> f x (next', t, tr')

(*
// Tm_refine is outside of the definition language: ...
let sample () : rand elem = fun store ->
  let next, t = store in
  if incrementable next then
    (Some (index t next), incr next)
  else
    (None, next)
*)

(** Get store *)
let get () : wald store = fun s -> Some s, writeable s

(** Update store *)
let put (s: id & traceT) : wald unit = fun _ -> Some (), s

(** Raise exception *)
let raise (a:Type) () : wald a = fun s -> None, writeable s

total reifiable reflectable new_effect {
  WALD_BIT: a:Type -> Effect
  with repr   = wald
     ; bind   = bind
     ; return = return
     ; get   = get
     ; put   = put
     ; raise = raise
}

effect WaldBit (a:Type) =
  WALD_BIT a (fun s post -> forall (x:option a & (id & traceT)). post x)

effect WaldBitHoare (a: Type) (req: store -> Type0) (ens: store -> option a -> (id & traceT) -> Type0) =
  WALD_BIT a (fun s post -> req s /\ (forall (r: option a) (s': id & traceT). ens s r s' ==> post (r, s')))


(** If not past the end of the tape, read a value and advance pointer *)
reifiable val sample: unit -> WALD_BIT elem (fun (next,t,tr) p ->
  if incrementable next then p (Some (index t next), (incr next, tr))
  else p (None, (next, tr)))
let sample () =
  let next, t, tr = WALD_BIT?.get () in
  if incrementable next then
    begin
    WALD_BIT?.put (incr next, tr);  // roughly RAND.next += 1
    index t next            // roughly tape[next]
    end
  else
    WALD_BIT?.raise elem ()

(** If reading the next n values would not advance past the end of the tape, read those values as a slice and advance the pointer n positions *)
reifiable val sample_n: n:nat -> WALD_BIT (r: Seq.seq elem {Seq.length r == n}) (fun (next,t,tr) p ->
  if incrementable_by_n next n then p (Some (slice t next n), (incr_n next n, tr))
  else p (None, (largest_id, tr)))
let sample_n n =
  let next, t, tr = WALD_BIT?.get () in
  if incrementable_by_n next n then
    begin
    let new_id = incr_n next n in
    WALD_BIT?.put (new_id, tr);
    slice t next n
    end
  else
    begin
    WALD_BIT?.put (largest_id, tr);
    WALD_BIT?.raise (Seq.seq elem) ()
    end

reifiable val trace (from to: pid) (msg: bits) : WALD_BIT unit (fun (next,_,tr) p ->
  // Using snoc ensures that the trace is ordered from oldest to newest.
  p (Some (), (next, List.Tot.snoc(tr, (from,to,msg)))))
let trace from to msg =
  let next, _ , tr = WALD_BIT?.get () in
  let tr' = List.Tot.snoc(tr, (from, to, msg)) in
  WALD_BIT?.put (next, tr')

let extract_trace (#a: Type) (r: option a & (id & traceT)) = let _, (_, tr) = r in tr

let trace_increases_length_by_one (from to: pid) (msg: bits) (tr: traceT) (t: tape) (i: id) : Lemma
  (ensures (List.Tot.length (extract_trace (reify (trace from to msg) (i, t, tr))) == List.Tot.length tr + 1))
= List.Tot.lemma_snoc_length (tr, (from, to, msg))

// TODO(klinvill): it seems this lemma is needed to prove that rand_bits returns a value. Is there a more elegant way to do this?
let sample_returns_some_until_size_read (next: nat) (t: tape) (tr: traceT) : Lemma
  (requires next + 1 < size)
  (ensures Some? (fst (reify (sample ()) ((to_id next), t, tr))))
  [SMTPat (reify (sample ()) ((to_id next), t, tr))]
= incrementable_if_next_id_lt_size next

// TODO(klinvill): it seems this lemma is needed to prove that rand_bits advances the tape pointer by a given amount. Is there a more elegant way to do this?
let sample_increments_id_until_size_read (i: nat) (t: tape) (tr: traceT) : Lemma
  (requires i + 1 < size)
  (ensures snd (reify (sample ()) ((to_id i), t, tr)) == (to_id (i + 1), tr))
  [SMTPat (reify (sample ()) ((to_id i), t, tr))]
= incrementable_if_next_id_lt_size i;
  incr_increases_by_one i

let sample_returns_some_until_none_remaining (i: id) (t: tape) (tr: traceT) : Lemma
  (requires remaining_samples i > 0)
  (ensures Some? (fst (reify (sample ()) (i, t, tr))))
  [SMTPat (reify (sample ()) (i, t, tr))]
= incrementable_if_remaining_samples i

let sample_increments_id_until_none_remaining (i: id) (t: tape) (tr: traceT) : Lemma
  (requires remaining_samples i > 0)
  (ensures snd (reify (sample ()) (i, t, tr)) == (incr i, tr))
  [SMTPat (reify (sample ()) (i, t, tr))]
= incrementable_if_remaining_samples i

let test_sample_some (v:elem) (t:tape{sel t (to_id 0) == v}) (tr: traceT) =
  let f = reify (sample ()) in
  assert (f (to_id 0,t,tr) == (Some v, (to_id 1, tr)))

let test_sample_none (v:elem) (t:tape) (tr: traceT) =
  let f = reify (sample ()) in
  assert (f (largest_id, t, tr) == (None, (largest_id, tr)))

#push-options "--query_stats --compat_pre_core 1"
let sample_n_equiv_to_n_samples (t: tape) (i: id) (n: nat) (tr: traceT) : Lemma
  (ensures (
    let r1, (i1, tr1) = reify (sample_n n) (i, t, tr) in
    forall (m: nat {m < n}).
      let j = if incrementable_by_n i m then incr_n i m else largest_id in
      let r2, (i2, tr2) = reify (sample ()) (j, t, tr) in
      // We expect the last element to be sampleable if the n elements are sampleable and vice-versa. Similarly we expect the last element to not be sampleable if the n elements are not sampleable and vice-versa.
      (m = n - 1 ==> Some? r1 == Some? r2)
      // If we can sample n elements, then we should be able to sample each of those elements individually from the tape
      /\ (Some? r1 ==> Some? r2)
      /\ (match r1 with
        // The m-th item in the slice should be equivalent to sampling the (i+m)-th item from the tape
        | Some(_) -> Seq.length (Some?.v r1) == n /\ Seq.index (Some?.v r1) m == Some?.v r2
        // No more elements to sample from tape, id should point to the end of the tape
        | None -> to_nat i1 == size - 1
      )
      // ids should agree after the final element is sampled
      /\ (m = n - 1 ==> i1 == i2)
      // Traces do not change
      /\ tr1 == tr2 /\ tr1 == tr
  ))
= if n > 0 then (
     // TODO(klinvill): should turn these assertions into lemmas
     // These assertions allow us to infer incrementability for other values of n. They are useful for the following proofs.
     assert(
       forall (m: nat {m < n}).
       incrementable_by_n i n ==> incrementable_by_n i m
     ) by (
       let open FStar.Tactics in
       let m = forall_intro_as "m" in
       let incrementable_n = implies_intro_as "incrementable_n" in
       let h1 = pose_lemma (`(incrementable_by_lt_n_if_incrementable_by_n (`@i) (`@n))) in
       smt ();
       smt ()
     );
     assert(
       forall (m: nat {m < n}).
       (~(incrementable_by_n i m)) ==> (~(incrementable_by_n i n))
     );

     assert(
       let n_prev: nat = n - 1 in
       incrementable_by_n i n ==> (
         let r1, s1 = reify (sample_n n) (i, t, tr) in
         let r2, s2 = reify (sample ()) (incr_n i n_prev, t, tr) in
         Some? r1 /\ Some? r2 /\ s1 == s2 /\ Some? r1 == Some? r2
       )
     );
     assert(
       let n_prev: nat = n - 1 in
       (~ (incrementable_by_n i n_prev)) ==> (
         let r1, s1 = reify (sample_n n) (i, t, tr) in
         let r2, s2 = reify (sample ()) (largest_id, t, tr) in
         None? r1 /\ None? r2 /\ s1 == s2 /\ Some? r1 == Some? r2
       )
     );

     assert(
       let n_prev: nat = n - 1 in
       incrementable_by_n i n_prev /\ ~(incrementable_by_n i n) ==> to_nat i + n == size
     ) by (
       let open FStar.Tactics in
       let inc_not_inc = implies_intro_as "inc_not_inc" in
       let h1 = pose_lemma (`(incrementable_by_n_but_not_by_prev_n_means_i_plus_n_is_size (`@i) (`@n))) in
       smt();
       smt()
     );
     assert(
       let n_prev: nat = n - 1 in
       incrementable_by_n i n_prev /\ ~(incrementable_by_n i n) ==> (
         let r1, s1 = reify (sample_n n) (i, t, tr) in
         let r2, s2 = reify (sample ()) (incr_n i n_prev, t, tr) in
         None? r1 /\ None? r2 /\ s1 == s2 /\ Some? r1 == Some? r2
       )
     )
  )
  else ();
  ()
#pop-options

(** Bijection over tapes, the inverse function acts as a witness *)
noeq type bijection =
  | Bijection:
      f:(tape #bit -> tape) ->
      finv:(tape -> tape){forall (h:tape). equal (f (finv h)) h /\ equal (finv (f h)) h} ->
      bijection

(** Inverse of a bijection *)
let inverse (bij:bijection) : bijection =
  Bijection bij.finv bij.f


(** Assume `sum` over `tape`. Definable as long as tape is finite *)
assume val sum: f:(tape #bit -> nat) -> nat

(** Reordering terms in a sum doesn't change the result *)
assume val sum_bijection: f:(tape -> nat) -> bij:bijection -> Lemma
  (sum f == sum (fun h -> f (bij.f h)))

(** The sum of non-negative function is monotonic *)
assume val sum_monotonic: f:(tape -> nat) -> g:(tape -> nat) -> Lemma
  (requires (forall h. f h <= g h))
  (ensures (sum f <= sum g))

(** Corollary *)
val sum_extensional: f:(tape -> nat) -> g:(tape -> nat) -> Lemma
  (requires (forall h. f h == g h))
  (ensures (sum f == sum g))
let sum_extensional f g =
  sum_monotonic f g;
  sum_monotonic g f

(** Unnormalized measure of a function `p` wrt the denotation of a probabilistic
    computation `f`.
    Assumes that the initial random tape is uniformly distributed
    When `p:a -> {0,1}` and `tape` is finite
    Pr[f : p] == 1/|tape| * sum_{h:tape} p (f h) == 1/|tape| * mass f p
*)
val mass: #a:Type -> f:(wald a) -> p:(traceT -> nat) -> (r:nat{r == sum (fun t -> p (extract_trace (f (init_store t))))})
let mass #a f p = sum (fun h -> let r = f (init_store h) in p (extract_trace r))

(* TODO(klinvill): The WaldBit effect doesn't have much information on traces. I
  believe this is leading to pr_leq to fail to prove unless mass is unfolded.
  The WaldBit effect should ideally have a more informative type such that
  unfolding mass is not required
*)
let unfold_mass (#a:Type) (f:wald a) (p:traceT -> nat) : Lemma
  (mass f p == sum (fun t -> p (extract_trace (f (init_store t)))))
= ()

val point: #a:eqtype -> x:a -> y:a -> nat
let point #a x = fun y -> if y = x then 1 else 0


(** If there exists a bijection over tapes such that `p1` evaluated
    on the result of `c1` is less than or equal to `p2` evaluated
    on the resulf of `c2`, then the measure of `p1` wrt `c1` is less than or
    equal to the measure of `p2` wrt `c2` *)
val pr_leq: #a:Type -> #b:Type ->
  c1:(wald a) ->
  c2:(wald b) ->
  tr: traceT ->
  bij:bijection -> Lemma
  (requires
    (forall t.
      let _,(_,tr1) = c1 (init_store t) in
      let _,(_,tr2) = c2 (init_store (bij.f t)) in
      (point tr tr1) <= (point tr tr2)))
  (ensures (mass c1 (point tr) <= mass c2 (point tr)))
let pr_leq #a #b c1 c2 tr bij =
  let bij' = inverse bij in
  let p = point tr in
  let f1 = (fun t -> let r1 = c1 (init_store t) in p (extract_trace r1)) in
  let f2 = (fun t -> let r2 = c2 (init_store t) in p (
  extract_trace r2)) in
  // f2 on the bijected tape
  let f2' = (fun t -> f2 (bij.f t)) in
  sum_monotonic f1 f2';
  sum_bijection f2' bij';
  sum_extensional (fun t -> f2 (bij.f (bij'.f t))) f2;
  unfold_mass c1 p;
  unfold_mass c2 p;
  ()

(** Corollary *)
val pr_eq: #a:Type -> #b:Type ->
  c1:(wald a) ->
  c2:(wald b) ->
  tr: traceT ->
  bij:bijection -> Lemma
  (requires
    (forall t.
      let _,(_,tr1) = c1 (init_store t) in
      let _,(_,tr2) = c2 (init_store (bij.f t)) in
      (point tr tr1) == (point tr tr2)))
  (ensures (mass c1 (point tr) == mass c2 (point tr)))
let pr_eq #a #b c1 c2 tr bij =
  pr_leq c1 c2 tr bij;
  pr_leq c2 c1 tr (inverse bij);
  ()
