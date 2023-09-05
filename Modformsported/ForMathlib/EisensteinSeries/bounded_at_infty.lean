/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.partial_sum_tendsto_uniformly 
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology 
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold  
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

open Complex UpperHalfPlane
 
open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold

open ModularForm

open SlashInvariantForm

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

noncomputable section

namespace EisensteinSeries

lemma slcoe (M : SL(2, ℤ)) : (M : GL (Fin 2) ℤ) i j = M i j  := by
  rfl

theorem mod_form_periodic (k : ℤ) (f : SlashInvariantForm (⊤ : Subgroup SL(2,ℤ)) k) :
    ∀ (z : ℍ) (n : ℤ), f ((ModularGroup.T^n)  • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k ⊤ f
  simp only [SlashInvariantForm.slash_action_eqn']
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h 
  have H:= h (ModularGroup.T^n) z
  rw [H]
  have h0 : ((ModularGroup.T^n) : GL (Fin 2) ℤ) 1 0 = 0  := by 
    rw [slcoe]
    rw [ModularGroup.coe_T_zpow n]
    rfl
  have h1: ((ModularGroup.T^n) : GL (Fin 2) ℤ) 1 1 = 1  := by 
    rw [slcoe]
    rw [ModularGroup.coe_T_zpow n]
    rfl    
  rw [h0,h1]
  ring_nf
  simp


theorem abs_floor_sub (r : ℝ) : |r - Int.floor r| < 1 :=
  by
  simp only [Int.self_sub_floor]
  rw [_root_.abs_of_nonneg (Int.fract_nonneg r)]
  apply Int.fract_lt_one r

theorem upp_half_translation (z : ℍ) :
    ∃ n : ℤ, ((ModularGroup.T^n)) • z ∈ upperHalfSpaceSlice 1 z.1.2 :=
  by
  let n := Int.floor z.1.1
  use-n
  have := modular_T_zpow_smul z (-n)
  simp_rw [this]
  simp  [ge_iff_le, slice_mem, UpperHalfPlane.coe_im, 
    UpperHalfPlane.coe_re]
  constructor
  have : (-(n : ℝ) +ᵥ z).1.re= -Int.floor z.1.1 + z.re := by rfl
  norm_cast at *
  rw [this]
  simp
  rw [add_comm]
  apply (abs_floor_sub z.1.1).le
  have : (-(n : ℝ) +ᵥ z).1.im = z.im := by 
    have := vadd_im (-(n : ℝ)) z
    rw [← this]
    congr
  rw [this]
  apply le_abs_self

theorem AbsEisenstein_bound (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    AbsEisenstein_tsum k z ≤ 8 / rfunct z ^ k * rZ (k - 1) :=
  by
  rw [AbsEisenstein_tsum, rZ, ← tsum_mul_left]
  let In := fun (n : ℕ) => square n
  have HI :=squares_cover_all
  let g := fun y : ℤ × ℤ => (AbsEise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by intro y; simp_rw [AbsEise]; simp
  have hgsumm : Summable g := by apply real_eise_is_summable k z h
  have index_lem := tsum_lemma g In HI hgsumm
  simp
  rw [index_lem]
  have ind_lem2 := sum_lemma g gpos In HI
  have smallclaim := SmallClaim k z h
  have hk : 1 < (k - 1 : ℤ) := by linarith
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero; simp; norm_cast; apply pow_ne_zero; apply EisensteinSeries.rfunct_ne_zero
  have riesum := int_RZ_is_summmable (k - 1) hk
  have riesum' : Summable fun n : ℕ => 8 / rfunct z ^ k * rie (↑k - 1) n :=
    by
    rw [← (summable_mul_left_iff nze).symm]
    simp at riesum 
    apply riesum
  apply tsum_le_tsum
  simp at *
  apply smallclaim
  rw [← ind_lem2]
  apply hgsumm
  norm_cast at *


theorem AbsEisenstein_bound_unifomly_on_stip (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
    (z : upperHalfSpaceSlice A B) :
    AbsEisenstein_tsum k z.1 ≤ 8 / rfunct (lbpoint A B hb) ^ k * rZ (k - 1) :=
  by
  have : 8 / rfunct (z : ℍ') ^ k * rZ (k - 1) ≤ 8 / rfunct (lbpoint A B hb) ^ k * rZ (k - 1) := by
    apply rfunctbound; exact h
  apply le_trans ( AbsEisenstein_bound k (z : ℍ') h) this

theorem eis_bound_by_real_eis (k : ℕ) (z : ℍ) (hk : 3 ≤ k) :
    Complex.abs (Eisenstein_tsum k z) ≤ AbsEisenstein_tsum k z :=
  by
  simp_rw [Eisenstein_tsum]
  simp_rw [AbsEisenstein_tsum]
  simp_rw [AbsEise]
  simp_rw [eise]
  apply abs_tsum'
  have := real_eise_is_summable k z hk
  simp_rw [AbsEise] at this 
  simp only [one_div, Complex.abs_pow, abs_inv, norm_eq_abs, zpow_ofNat] at *
  apply this

theorem Eisenstein_is_bounded' (k : ℕ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty ((Eisenstein_SIF ⊤ k)) := 
  by
  simp only [UpperHalfPlane.bounded_mem, Subtype.forall, UpperHalfPlane.coe_im]
  let M : ℝ := 8 / rfunct (lbpoint 1 2 <| by linarith) ^ k * rZ (k - 1)
  use M, 2
  intro z hz
  obtain ⟨n, hn⟩ := upp_half_translation z
  have := mod_form_periodic k (Eisenstein_SIF ⊤ k) z n
  rw [← this]
  let Z := (ModularGroup.T^n) • z
  apply le_trans (eis_bound_by_real_eis k Z hk)
  have hZ : Z ∈ upperHalfSpaceSlice 1 2 :=
    by
    simp only [map_zpow, slice_mem, abs_ofReal, ge_iff_le] at hn ⊢
    refine' ⟨hn.1, _⟩
    apply le_trans hz
    rw [modular_T_zpow_smul]
    have : ((n : ℝ) +ᵥ z).1.im = z.im := by 
      have := vadd_im ((n : ℝ)) z
      rw [← this]
      congr
    rw [this]
    apply le_abs_self
  convert  AbsEisenstein_bound_unifomly_on_stip k hk 1 2 (by linarith) ⟨Z, hZ⟩

theorem Eisenstein_is_bounded (k : ℤ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty ((Eisenstein_SIF ⊤ k)) :=
  by
  have : ∃ n : ℕ, (n : ℤ) = k :=
    haveI hk' : 0 ≤ k := by linarith
    CanLift.prf k hk'
  obtain ⟨n, hn⟩ := this
  have hn3 : 3 ≤ n := by linarith
  have := Eisenstein_is_bounded' n hn3
  convert this
  apply hn.symm
  apply hn.symm
  apply hn.symm

theorem Eisenstein_series_is_bounded (k : ℤ) (hk : 3 ≤ k) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty ( (Eisenstein_SIF ⊤ k)∣[k,A]) :=
  by
  simp_rw [(Eisenstein_SIF ⊤ k).2]
  have := Eisenstein_is_bounded k hk
  convert this
  have hr := (Eisenstein_SIF ⊤ k).2 ⟨A, by tauto⟩
  convert hr