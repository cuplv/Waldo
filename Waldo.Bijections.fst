module Waldo.Bijections

open Waldo.Effects.Wald


let bij_id =
  let f    = λ h → h in
  let finv = λ h → h in
  Bijection f finv
