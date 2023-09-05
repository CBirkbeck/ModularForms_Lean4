/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.mdifferentiable
import Modformsported.ForMathlib.EisensteinSeries.bounded_at_infty


open Complex UpperHalfPlane
 
open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold

open ModularForm

open SlashInvariantForm

noncomputable section

namespace EisensteinSeries

def EisensteinSeriesModularForm (k : ℤ) (hk : 3 ≤ k) : ModularForm ⊤ k
    where
  toFun := (Eisenstein_SIF ⊤ k)
  slash_action_eq' := by convert (Eisenstein_SIF ⊤ k).2
  holo' := Eisenstein_series_is_mdiff k hk
  bdd_at_infty' A :=  Eisenstein_series_is_bounded k hk A