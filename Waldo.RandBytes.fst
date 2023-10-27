module Waldo.RandBytes


let rand_bytes n =
  let seq_samples = sample_n n in
  seq_to_bytes seq_samples

#push-options "--query_stats"
let rand_bytes_1_equiv_to_sample i t tr
= incrementable_by_n_if_new_id_lt_size (to_nat i) 0;
  sample_n_equiv_to_n_samples t i 1 tr;
  ()
#pop-options

#push-options "--query_stats --compat_pre_core 1"
let rand_bytes_1_equiv_to_sample_fully_quantified () : Lemma
  (ensures (forall (i: id) (t: tape) (tr: traceT).
    rand_bytes_1_equiv_to_sample_post i t tr
  ))
  by (
    let open FStar.Tactics in
    let post = forall_intro_as "post" in
    let h1 = implies_intro_as "h1" in
    let rt = forall_intro_as "rt" in
    let h1' = instantiate_as h1 rt "h1'" in
    mapply h1';
    let i = forall_intro_as "i" in
    let t = forall_intro_as "t" in
    let tr = forall_intro_as "tr" in
    // All the work done in this proof is to get the goal into this shape, where t is instantiated so we can apply the lemma
    let _ = apply_lemma (`rand_bytes_1_equiv_to_sample) in
    qed ()
  )
= ()
#pop-options

#push-options "--query_stats"
let rand_bytes_n_equiv_to_slice i t n tr = ()
#pop-options
