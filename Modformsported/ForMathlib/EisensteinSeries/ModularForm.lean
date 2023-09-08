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




/-

lemma tes (f : ℕ+ → ℂ)  (h : ∀ n, f n = 0) : ∑' n, f n = 0 := by 
  rw [←tsum_zero]
  apply tsum_congr
  exact h

lemma riemmaZeta_Odd_wt_eq_zero' (k : ℤ) ( hk : 3 ≤ k) (hkO : Odd k) : (∑' (n : ℤ), ((n : ℂ) ^ k)⁻¹) = 0 := by
  simp
  rw [int_tsum_pNat]
  simp
  norm_cast
  simp
  rw [add_assoc]
  rw [←tsum_add]
  have : ((0 : ℝ)^k)⁻¹ = 0 := by sorry
  simp at this
  rw [this]
  simp
  rw [←tsum_zero]
  apply tsum_congr
  intro b
  field_simp
  have hbo : (-(b: ℝ))^k = - b^k := by sorry
  simp at *
  rw [hbo]
  rw [inv_neg]
  linarith
  have := int_pnat_sum (fun n : ℤ => ((n : ℝ) ^ k)⁻¹)
  simp at this
  apply this
  have hk : 1 < k := by sorry
  stop




lemma eiseinsteinSeries_Odd_wt_eq_zero (k : ℤ) ( hk : 3 ≤ k) (hkO : Odd k) : 
  EisensteinSeriesModularForm k hk = 0 := by
  apply ModularForm.ext
  intro z
  simp only [ModularForm.zero_apply]
  rw [←ModularForm.toFun_eq_coe]
  rw [EisensteinSeriesModularForm]
  simp only
  rw [Eisenstein_SIF]
  simp only [SlashInvariantForm.coe_mk]
  rw [ Eisenstein_tsum]
  simp_rw [eise]
  
  /-
  rw [tsum_prod]
  rw [int_tsum_pNat]
  rw [int_tsum_pNat]
  simp
  norm_cast
  
  rw [add_assoc]
  rw [←tsum_add]
  have := riemmaZeta_Odd_wt_eq_zero' k hk hkO
  rw [int_tsum_pNat] at this
  simp at *
  norm_cast at *
  rw [this]
  simp
  apply tes
  intro n
  rw [←tsum_add]
  rw [int_tsum_pNat]
  simp
  norm_cast
  -/
  stop

 -/ 
  