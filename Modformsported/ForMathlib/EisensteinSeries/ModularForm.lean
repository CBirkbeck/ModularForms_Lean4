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

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "GL(" n ", " R ")" => Matrix.GeneralLinearGroup (Fin n) R

noncomputable section

namespace EisensteinSeries

def EisensteinSeriesModularForm (k : ℤ) (hk : 3 ≤ k) : ModularForm ⊤ k
    where
  toFun := (Eisenstein_SIF ⊤ k)
  slash_action_eq' := by convert (Eisenstein_SIF ⊤ k).2
  holo' := Eisenstein_series_is_mdiff k hk
  bdd_at_infty' A :=  Eisenstein_series_is_bounded k hk A

lemma coeGLl (A: SL(2,ℤ)) : (A : GL(2,ℤ)) i j = A.1 i j := by
  norm_cast

lemma neg_moeb_eq_id (z : ℍ) : (-1 : SL(2,ℤ)) • z = z := by
  rw [← UpperHalfPlane.ext_iff,UpperHalfPlane.specialLinearGroup_apply,UpperHalfPlane.coe_mk]
  simp
  simp_rw [coeGLl (-1 : SL(2,ℤ)) ] 
  simp
  field_simp
  


lemma ModularForms_Top_Odd_Wt_eq_zero (F : Type) (k : ℤ) ( hk : 3 ≤ k) (hkO : Odd k) 
  (f : ModularForm ⊤ k):
  f = 0 := by 
  apply  ModularForm.ext
  intro z
  have := slash_action_eqn' k ⊤ f 
  
  simp at *
  have HI := this (-1) z
  simp at HI
  norm_cast
  have h10 : (-1 : SL(2,ℤ)) 1 0 = 0 := by rfl
  norm_cast at HI
  simp_rw [coeGLl (-1 : SL(2,ℤ)) ] at HI
  simp at HI
  have HIn:= neg_moeb_eq_id z
  simp at HIn
  rw [HIn] at HI
  have hO : (-1 :ℂ)^k = -1 := by sorry
  simp at hO
  rw [hO] at HI
  simp at HI

  

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
  