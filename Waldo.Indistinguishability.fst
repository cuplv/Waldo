module Waldo.Indistinguishability

open Waldo.Tape
open Waldo.Effects.WaldBit
open Waldo.Effects.Wald

module RB = Waldo.Effects.WaldBit


(** Type of a protocol that generates traces and receives public and private arguments. The private arguments can be dependently typed on the public arguments. *)
type iprotocol (#a: Type) (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type) =
  pub: pub_args_type -> priv_args_type pub -> Wald a
type iprotocol_bit (#a: Type) (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type) =
  pub: pub_args_type -> priv_args_type pub -> WaldBit a

(** Type of indistinguishability propositions. These propositions are propositions on a single set of public arguments, a single possible output trace, and two sets of secret arguments *)
type iprop (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type) (#trace_type: pub_args_type -> eqtype) =
  pub: pub_args_type -> priv_args_type pub -> priv_args_type pub -> trace_type pub -> Type0

(** The proposition that guarantees indistinguishability. Namely that the probability of generating any particular trace from a protocol, with the same public inputs, is equivalent for all possible traces *)
unfold let indistinguishable_ensures
  (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type)
  (protocol: iprotocol)
  : iprop =
  (** Arguments generally meant to be instantiated from the top-level protocol lemma *)
  fun (pub_args: pub_args_type) (priv_args1 priv_args2: priv_args_type pub_args) (trace: traceT) ->
    let f1 h = reify (protocol pub_args priv_args1) h in
    let f2 h = reify (protocol pub_args priv_args2) h in
    (** Probability of the trace `trace` is equally likely to be generated regardless of the secret arguments *)
    mass f1 (point trace) == mass f2 (point trace)

unfold let indistinguishable_ensures_bit
  (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type)
  (protocol: iprotocol_bit)
  : iprop =
  (** Arguments generally meant to be instantiated from the top-level protocol lemma *)
  fun (pub_args: pub_args_type) (priv_args1 priv_args2: priv_args_type pub_args) (trace: RB.traceT) ->
    let f1 h = reify (protocol pub_args priv_args1) h in
    let f2 h = reify (protocol pub_args priv_args2) h in
    (** Probability of the trace `trace` is equally likely to be generated regardless of the secret arguments *)
    RB.mass f1 (RB.point trace) == RB.mass f2 (RB.point trace)

(** Generic lemma to prove indistinguishability using a bijection over tapes.

    The bijection must ensure that for all possible tapes, protocols, public inputs, pairs of secret inputs, and output traces, if the protocol generates a specific trace using the original tape and the first secret input then it also must generate the same trace using the bijected tape and the second secret input. Since this statement is universally quantified over all tapes and traces, and since we consider all tapes as equally likely, this precondition can be used to show that for any public input and secret inputs, the protocol is equally likely to generate a particular trace, regardless of the secret input. This reasoning follows from the R-Rand and PrLE rules of probabilistic Relational Hoare Logic (pRHL). *)
unfold let indistinguishable_lemma
  (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type)
  (protocol: iprotocol)
  (bij: bijection)
  (pub_args: pub_args_type)
  (priv_args1: priv_args_type pub_args)
  (priv_args2: priv_args_type pub_args)
  (tr: traceT)
  : Lemma
    (requires (
      let f1 h = reify (protocol pub_args priv_args1) h in
      let f2 h = reify (protocol pub_args priv_args2) h in
        forall t.
          let tr1 = extract_trace (f1 (init_store t)) in
          let tr2 = extract_trace (f2 (init_store (bij.f t))) in
          (point tr) tr1 == (point tr) tr2))
    (ensures (
      let f1 h = reify (protocol pub_args priv_args1) h in
      let f2 h = reify (protocol pub_args priv_args2) h in
      mass f1 (point tr) == mass f2 (point tr)))
= let f1 h = reify (protocol pub_args priv_args1) h in
  let f2 h = reify (protocol pub_args priv_args2) h in
  pr_eq f1 f2 tr bij

unfold let indistinguishable_lemma_bit
  (#pub_args_type: Type) (#priv_args_type: pub_args_type -> Type)
  (protocol: iprotocol_bit)
  (bij: RB.bijection)
  (pub_args: pub_args_type)
  (priv_args1: priv_args_type pub_args)
  (priv_args2: priv_args_type pub_args)
  (tr: RB.traceT)
  : Lemma
    (requires (
      let f1 h = reify (protocol pub_args priv_args1) h in
      let f2 h = reify (protocol pub_args priv_args2) h in
        forall t.
          let tr1 = RB.extract_trace (f1 (RB.init_store t)) in
          let tr2 = RB.extract_trace (f2 (RB.init_store (bij.f t))) in
          (RB.point tr) tr1 == (RB.point tr) tr2))
    (ensures (
      let f1 h = reify (protocol pub_args priv_args1) h in
      let f2 h = reify (protocol pub_args priv_args2) h in
      RB.mass f1 (RB.point tr) == RB.mass f2 (RB.point tr)))
= let f1 h = reify (protocol pub_args priv_args1) h in
  let f2 h = reify (protocol pub_args priv_args2) h in
  RB.pr_eq f1 f2 tr bij
