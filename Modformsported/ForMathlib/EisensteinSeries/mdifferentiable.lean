/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.partial_sum_tendsto_uniformly

open Complex

open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold

open ModularForm

open SlashInvariantForm

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

noncomputable section

namespace EisensteinSeries

def holExtn (f : ℍ → ℂ) : ℍ' → ℂ := fun z : ℍ' => f (z : ℍ)

local notation "↑ₕ" => holExtn

instance : Coe (ℍ → ℂ) (ℍ' → ℂ) :=
  ⟨fun f => holExtn f⟩

theorem aux8 (a b k : ℤ) (x : ℂ) : (((a : ℂ) * x + b) ^ k)⁻¹ = ((a : ℂ) * x + b) ^ (-k) := by
  have := (zpow_neg ((a : ℂ) * x + b) k).symm
  norm_cast at *

def ein (a b k : ℤ) : ℂ → ℂ := fun x => (a * x + b) ^ k

theorem dd2 (a b k : ℤ) (x : ℂ) (h : (a : ℂ) * x + b ≠ 0) :
    HasDerivAt (ein a b k) (k * (a * x + b) ^ (k - 1) * a : ℂ) x := by
  unfold ein
  rw [← Function.comp_def (fun x : ℂ => x ^ k) (a * · + b)]
  apply HasDerivAt.comp
  · exact hasDerivAt_zpow k ((a : ℂ) * x + b ) (Or.inl h)
  · simpa using (hasDerivAt_id' x).const_mul (a : ℂ) |>.add_const _

variable (f : ℍ' → ℂ)

open scoped Topology Manifold

theorem ext_chart (z : ℍ') : (extendByZero f) z = (f ∘ ⇑(chartAt ℂ z).symm) z := by
  simp_rw [chartAt, extendByZero]
  simp only [TopologicalSpace.Opens.coe_mk, Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true,
    Function.comp_apply]
  have hh : z.1 ∈ UpperHalfPlane.upperHalfSpace := by apply z.2
  rw [if_pos hh]
  erw [PartialHomeomorph.left_inv _ (mem_chart_source _ _)]

theorem holo_to_mdiff (f : ℍ' → ℂ) (hf : IsHolomorphicOn f) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn] at hf
  simp_rw [MDifferentiable]
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  intro x
  constructor
  · have hc := hf.continuousOn
    simp only [TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.coe_mk] at hc
    rw [continuousOn_iff_continuous_restrict] at hc
    convert hc.continuousAt
    funext y
    simp only [Set.restrict_apply, extendByZero, UpperHalfPlane.mem_upperHalfSpace, Subtype.coe_eta,
      dite_eq_ite]

    have hh := y.2
    simp only [TopologicalSpace.Opens.mem_mk, UpperHalfPlane.mem_upperHalfSpace] at hh
    rw [if_pos hh]
  have hH : ℍ'.1 ∈ 𝓝 ((chartAt ℂ x) x) :=
    by
    simp_rw [Metric.mem_nhds_iff, chartAt]
    have := upper_half_plane_isOpen
    rw [Metric.isOpen_iff] at this
    exact this x.1 x.2
  apply DifferentiableOn.differentiableAt _ hH
  apply DifferentiableOn.congr hf
  intro z hz
  have HH := ext_chart f (⟨z, hz⟩ : ℍ')
  simp only [TopologicalSpace.Opens.coe_mk, Function.comp_apply] at HH
  simp only [Function.comp_apply]
  simp_rw [HH]
  norm_cast

theorem mdiff_to_holo (f : ℍ' → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : IsHolomorphicOn f :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  simp_rw [MDifferentiable] at hf
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps] at hf
  simp_rw [DifferentiableOn]
  intro x hx
  have hff := (hf ⟨x, hx⟩).2
  apply DifferentiableAt.differentiableWithinAt
  simp_rw [DifferentiableAt] at *
  obtain ⟨g, hg⟩ := hff
  refine' ⟨g, _⟩
  apply HasFDerivAt.congr_of_eventuallyEq hg
  simp_rw [Filter.eventuallyEq_iff_exists_mem]
  refine' ⟨ℍ', _⟩
  constructor
  simp_rw [Metric.mem_nhds_iff, chartAt]
  have := upper_half_plane_isOpen
  rw [Metric.isOpen_iff] at this
  have ht := this x hx
  simp at ht
  exact ht
  simp_rw [Set.EqOn]
  intro y hy
  apply ext_chart f (⟨y, hy⟩ : ℍ')

theorem mdiff_iff_holo (f : ℍ' → ℂ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ IsHolomorphicOn f :=
  ⟨mdiff_to_holo f, holo_to_mdiff f⟩

section mdifferentiable_lemmas

theorem Eise'_has_deriv_within_at (k : ℤ) (y : ℤ × ℤ) (hkn : k ≠ 0) :
    IsHolomorphicOn fun z : ℍ' => eise k z y := by
  rw [IsHolomorphicOn]
  intro z
  by_cases (y.1 : ℂ) * z.1 + y.2 = 0
  case neg hy =>
    simp_rw [eise, one_div]
    have := aux8 y.1 y.2 k z.1

    have nz : (y.1 : ℂ) * z.1 + y.2 ≠ 0 := by apply hy
    have hdd := dd2 y.1 y.2 (-k) z hy

    have H :
      HasDerivWithinAt (fun x : ℂ => (↑y.fst * x + ↑y.snd) ^ (-k))
        (↑(-k) * (↑y.fst * ↑z + ↑y.snd) ^ (-k - 1) * ↑y.fst) UpperHalfPlane.upperHalfSpace ↑z := by
        apply HasDerivAt.hasDerivWithinAt
        convert hdd
    simp only [zpow_neg, Int.cast_neg, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.coe_mk, neg_mul] at H
    let fx := (-k * ((y.1 : ℂ) * z.1 + y.2) ^ (-k - 1) * y.1 : ℂ)
    refine' ⟨fx, _⟩
    rw [hasDerivWithinAt_iff_tendsto] at *
    simp only [ne_eq, TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.coe_mk,
      zpow_neg, Int.cast_neg, neg_mul, norm_eq_abs, smul_eq_mul, mul_neg, sub_neg_eq_add] at *
    rw [Metric.tendsto_nhdsWithin_nhds] at *
    intro ε hε
    have HH := H ε hε
    obtain ⟨d1, hd1, hh⟩ := HH
    refine' ⟨d1, hd1, _⟩
    intro x hx hd
    simp_rw [extendByZero]
    simp only [UpperHalfPlane.mem_upperHalfSpace] at hx
    simp only [UpperHalfPlane.mem_upperHalfSpace, hx, dite_eq_ite, ite_true, Subtype.coe_prop,
      dist_zero_right, norm_mul, norm_inv, Real.norm_eq_abs, Complex.abs_abs]
    have H3 := hh hx hd
    simp only [dist_zero_right, norm_mul, norm_inv, Real.norm_eq_abs, Complex.abs_abs] at H3
    norm_cast at *
  case pos hy =>
    have hz : y.1 = 0 ∧ y.2 = 0 := (linear_eq_zero_iff y.1 y.2 z).1 hy
    simp_rw [eise, hz.1, hz.2, Int.cast_zero, zero_mul, add_zero, zero_zpow _ hkn, div_zero]
    simpa only [IsHolomorphicOn] using zero_hol ℍ' z

theorem Eise'_has_diff_within_at (k : ℤ) (y : ℤ × ℤ) (hkn : k ≠ 0) :
    DifferentiableOn ℂ (extendByZero fun z : ℍ' => eise k z y) ℍ' :=
  by
  have := isHolomorphicOn_iff_differentiableOn ℍ' fun z : ℍ' => eise k z y
  simp only [TopologicalSpace.Opens.coe_mk]
  rw [this]
  apply Eise'_has_deriv_within_at _ _ hkn

theorem eisenSquare_diff_on (k : ℤ) (hkn : k ≠ 0) (n : ℕ) :
    IsHolomorphicOn fun z : ℍ' => eisenSquare k n z :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  have h1 :
    (extendByZero fun z : ℍ' => eisenSquare k n z) = fun x : ℂ =>
      ∑ y in square n, (extendByZero fun z : ℍ' => eise k z y) x :=
    by
    simp_rw [eisenSquare]
    funext z
    simp only [extendByZero, Finset.sum_dite_irrel, Finset.sum_const_zero]
  simp only [Ne.def] at *
  rw [h1]
  apply DifferentiableOn.sum
  intro i _
  apply Eise'_has_diff_within_at k i hkn

theorem eisenSquare'_diff_on (k : ℤ) (hkn : k ≠ 0) (n : ℕ) : IsHolomorphicOn (eisenSquare' k n) :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  have h1 :
    extendByZero (eisenSquare' k n) = fun x : ℂ =>
      ∑ y in Finset.range n, (extendByZero fun z : ℍ' => eisenSquare k y z) x :=
    by
    ext1
    simp  [eisenSquare', extendByZero, Finset.sum_dite_irrel, Finset.sum_const_zero]

  rw [h1]
  apply DifferentiableOn.sum
  exact fun i _ => (isHolomorphicOn_iff_differentiableOn _ _).mpr (eisenSquare_diff_on k hkn i)

theorem Eisenstein_is_holomorphic' (k : ℤ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (Eisenstein_tsum k)) := by
  rw [← isHolomorphicOn_iff_differentiableOn]
  apply diff_on_diff
  intro x
  have H := Eisen_partial_tends_to_uniformly_on_ball' k hk x
  obtain ⟨A, B, ε, hε, hball, _, hεB, hunif⟩ := H
  have hball2 : Metric.closedBall (↑x) ε ⊆ ℍ'.1 := by
    apply ball_in_upper_half x A B ε hε hεB hball
  refine ⟨ε, hε, Metric.ball_subset_closedBall.trans hball2, ?_⟩
  have hkn : (k : ℤ) ≠ 0 := by norm_cast; rintro rfl; norm_num at hk
  let F : ℕ → ℂ → ℂ := fun n => extendByZero (eisenSquare' k n)
  have hdiff (n : ℕ) : DifferentiableOn ℂ (F n) (Metric.closedBall x ε) := by
    have := eisenSquare'_diff_on k hkn n
    rw [← isHolomorphicOn_iff_differentiableOn] at this
    apply this.mono
    apply hball2
  rw [←tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall _ _)] at hunif
  have := TendstoLocallyUniformlyOn.mono hunif Metric.ball_subset_closedBall
  apply this.differentiableOn ?_ Metric.isOpen_ball
  apply Filter.eventually_of_forall
  apply (fun n : ℕ => (hdiff n).mono Metric.ball_subset_closedBall)

/-
theorem Eisenstein_is_holomorphic (k : ℤ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (Eisenstein_tsum k)) :=
  by
  have : ∃ n : ℕ, (n : ℤ) = k :=
    haveI hk' : 0 ≤ k := by linarith
    CanLift.prf k hk'
  obtain ⟨n, hn⟩ := this
  have hn3 : 3 ≤ n := by linarith
  have := Eisenstein_is_holomorphic' n hn3
  convert this
  apply hn.symm
  -/

theorem Eisenstein_series_is_mdiff (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (↑ₕ (Eisenstein_SIF ⊤ ↑k)) := by
  simpa using (mdiff_iff_holo (↑ₕ (Eisenstein_SIF ⊤ k).toFun)).2 (Eisenstein_is_holomorphic' k hk)
