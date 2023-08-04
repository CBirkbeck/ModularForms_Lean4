/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

#align_import for_mathlib.unform_limits_of_holomorphic

/-!
# Circle integral transform
In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.
These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.
-/


open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal BigOperators Topology

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : ℝ) (z w : ℂ)

namespace Complex

#print Complex.circleTransform /-
/-- Given a function `f : ℂ → E`, `circle_transform R z w f` is the functions mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f (circle_map z R θ)`.
If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circleTransform (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)
-/

#print Complex.circleTransformDeriv /-
/-- The derivative of `circle_transform` w.r.t `w`.-/
def circleTransformDeriv (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)
-/

#print Complex.circleTransformDeriv_periodic /-
theorem circleTransformDeriv_periodic (f : ℂ → E) :
    Periodic (circleTransformDeriv R z w f) (2 * π) :=
  by
  have := periodic_circleMap
  simp_rw [periodic] at *
  intro x
  simp_rw [circle_transform_deriv, this]
  congr 2
  simp [this]
-/

#print Complex.circleTransformDeriv_eq /-
theorem circleTransformDeriv_eq (f : ℂ → E) :
    circleTransformDeriv R z w f = fun θ => (circleMap z R θ - w)⁻¹ • circleTransform R z w f θ :=
  by
  ext
  simp_rw [circle_transform_deriv, circle_transform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring
-/

#print Complex.integral_circleTransform /-
theorem integral_circleTransform [CompleteSpace E] (f : ℂ → E) :
    ∫ θ : ℝ in 0 ..2 * π, circleTransform R z w f θ =
      (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z :=
  by
  simp_rw [circle_transform, circleIntegral, deriv_circleMap, circleMap]
  simp
-/

#print Complex.continuous_circleTransform /-
theorem continuous_circleTransform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f <| sphere z R) (hw : w ∈ ball z R) :
    Continuous (circleTransform R z w f) :=
  by
  apply_rules [Continuous.smul, continuous_const]
  simp_rw [deriv_circleMap]
  apply_rules [Continuous.mul, continuous_circleMap 0 R, continuous_const]
  · apply continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _
-/

#print Complex.continuous_circleTransformDeriv /-
theorem continuous_circleTransformDeriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f (sphere z R)) (hw : w ∈ ball z R) :
    Continuous (circleTransformDeriv R z w f) :=
  by
  rw [circle_transform_deriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circle_transform hR hf hw)
-/

#print Complex.circleTransformBoundingFunction /-
/-- A useful bound for circle integrals (with complex codomain)-/
def circleTransformBoundingFunction (R : ℝ) (z : ℂ) (w : ℂ × ℝ) : ℂ :=
  circleTransformDeriv R z w.1 (fun x => 1) w.2
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Complex.continuousOn_prod_circle_transform_function /-
theorem continuousOn_prod_circle_transform_function {R r : ℝ} (hr : r < R) {z : ℂ} :
    ContinuousOn (fun w : ℂ × ℝ => (circleMap z R w.snd - w.fst)⁻¹ ^ 2)
      (closedBall z r ×ˢ (⊤ : Set ℝ)) :=
  by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  refine'
    ((continuous_circleMap z R).ContinuousOn.comp continuousOn_snd fun _ => And.right).sub
      (continuous_on_id.comp continuousOn_fst fun _ => And.left)
  simp only [mem_prod, Ne.def, and_imp, Prod.forall]
  intro a b ha hb
  have ha2 : a ∈ ball z R := by simp at *; linarith
  exact sub_ne_zero.2 (circleMap_ne_mem_ball ha2 b)
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Complex.continuousOn_abs_circleTransformBoundingFunction /-
theorem continuousOn_abs_circleTransformBoundingFunction {R r : ℝ} (hr : r < R) (z : ℂ) :
    ContinuousOn (abs ∘ fun t => circleTransformBoundingFunction R z t)
      (closedBall z r ×ˢ (⊤ : Set ℝ) : Set <| ℂ × ℝ) :=
  by
  have : ContinuousOn (circle_transform_bounding_function R z) (closed_ball z r ×ˢ (⊤ : Set ℝ)) :=
    by
    apply_rules [ContinuousOn.smul, continuousOn_const]
    simp only [deriv_circleMap]
    have c := (continuous_circleMap 0 R).ContinuousOn
    apply_rules [ContinuousOn.mul, c.comp continuousOn_snd fun _ => And.right, continuousOn_const]
    simp_rw [← inv_pow]
    apply continuous_on_prod_circle_transform_function hr
  refine' continuous_abs.continuous_on.comp this _
  show maps_to _ _ (⊤ : Set ℂ)
  simp [maps_to]
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Complex.abs_circleTransformBoundingFunction_le /-
theorem abs_circleTransformBoundingFunction_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
    ∃ x : (closedBall z r ×ˢ [0, 2 * π] : Set <| ℂ × ℝ),
      ∀ y : (closedBall z r ×ˢ [0, 2 * π] : Set <| ℂ × ℝ),
        abs (circleTransformBoundingFunction R z y) ≤ abs (circleTransformBoundingFunction R z x) :=
  by
  have cts := continuous_on_abs_circle_transform_bounding_function hr z
  have comp : IsCompact (closed_ball z r ×ˢ [0, 2 * π] : Set (ℂ × ℝ)) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none := (nonempty_closed_ball.2 hr').Prod nonempty_uIcc
  simpa using IsCompact.exists_forall_ge comp none (cts.mono (by intro z; simp; tauto))
-/

#print Complex.circleTransformDeriv_bound /-
/-- The derivative of a `circle_transform` is locally bounded. -/
theorem circleTransformDeriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ} (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) :
    ∃ B ε : ℝ,
      0 < ε ∧
        ball x ε ⊆ ball z R ∧
          ∀ (t : ℝ), ∀ y ∈ ball x ε, Complex.abs (circleTransformDeriv R z y f t) ≤ B :=
  by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    abs_circle_transform_bounding_function_le hr (pos_of_mem_ball hrx).le z
  let V : ℝ → ℂ → ℂ := fun θ w => circle_transform_deriv R z w (fun x => 1) θ
  have funccomp : ContinuousOn (fun r => abs (f r)) (sphere z R) :=
    by
    have cabs : ContinuousOn abs ⊤ := by apply continuous_abs.continuous_on
    apply cabs.comp hf; rw [maps_to]; tauto
  have sbou :=
    IsCompact.exists_forall_ge (isCompact_sphere z R) (NormedSpace.sphere_nonempty.2 hR.le) funccomp
  obtain ⟨X, HX, HX2⟩ := sbou
  refine' ⟨abs (V b a) * abs (f X), ε', hε', subset.trans H (ball_subset_ball hr.le), _⟩
  intro y v hv
  obtain ⟨y1, hy1, hfun⟩ :=
    periodic.exists_mem_Ico₀ (circle_transform_deriv_periodic R z v f) Real.two_pi_pos y
  have hy2 : y1 ∈ [0, 2 * π] := by
    convert Ico_subset_Icc_self hy1
    simp [real.two_pi_pos.le]
  have :=
    mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closed_ball (H hv), hy2⟩⟩)
      (HX2 (circleMap z R y1) (circleMap_mem_sphere z hR.le y1)) (complex.abs.nonneg _)
      (complex.abs.nonneg _)
  simp_rw [hfun]
  simp only [circle_transform_bounding_function, circle_transform_deriv, V, norm_eq_abs,
    Algebra.id.smul_eq_mul, deriv_circleMap, map_mul, abs_circleMap_zero, abs_I, mul_one, ←
    mul_assoc, mul_inv_rev, inv_I, abs_neg, abs_inv, abs_of_real, one_mul, abs_two, abs_pow,
    mem_ball, gt_iff_lt, Subtype.coe_mk, SetCoe.forall, mem_prod, mem_closed_ball, and_imp,
    Prod.forall, NormedSpace.sphere_nonempty, mem_sphere_iff_norm] at *
  exact this
-/

/-- Cauchy integral form of a function at `z` in a disk of radius `R`-/
def circleIntegralForm [CompleteSpace E] (R : ℝ) (z : ℂ) (f : ℂ → E) : ℂ → E := fun w =>
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z

theorem circle_intgral_form_eq_int [CompleteSpace E] (R : ℝ) (z : ℂ) (f : ℂ → E) :
    circleIntegralForm R z f = fun w => ∫ θ : ℝ in 0 ..2 * π, (circleTransform R z w f) θ := by
  simp_rw [circle_transform, circle_integral_form, circleIntegral, intervalIntegral.integral_smul]

theorem circleTransform_circle_int [CompleteSpace E] (R : ℝ) (z w : ℂ) (f : ℂ → E) :
    ∫ θ : ℝ in 0 ..2 * π, circleTransform R z w f θ =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z :=
  by
  simp_rw [circle_transform, circleIntegral, deriv_circleMap, circleMap]
  simp only [real_smul, nsmul_eq_mul, Nat.cast_bit0, Nat.cast_one, one_div,
    intervalIntegral.integral_smul, zero_add]

theorem circleTransform_hasDerivAt (R : ℝ) (z : ℂ) (f : ℂ → ℂ) :
    ∀ (t : ℝ),
      ∀ y ∈ ball z R,
        HasDerivAt (fun y => (circleTransform R z y f) t) ((circleTransformDeriv R z y f) t) y :=
  by
  intro y x hx
  simp only [circle_transform, circle_transform_deriv, Algebra.id.smul_eq_mul, ← mul_assoc,
    deriv_circleMap]
  apply_rules [HasDerivAt.mul_const, HasDerivAt.const_mul]
  have H : HasDerivAt (fun y_1 : ℂ => circleMap z R y - y_1) (-1) x := by
    apply HasDerivAt.const_sub; apply hasDerivAt_id
  have hfin := HasDerivAt.inv H (sub_ne_zero.2 (circleMap_ne_mem_ball hx y))
  simp only [one_div, neg_neg] at hfin 
  exact hfin

theorem circleTransform_aEMeasurable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) :
    ∀ᶠ y in 𝓝 x,
      AEMeasurable ((fun w => fun θ => circleTransform R z w f θ) y)
        (volume.restrict (Ι 0 (2 * π))) :=
  by
  rw [Filter.eventually_iff_exists_mem]
  obtain ⟨ε', He, HB⟩ := exists_ball_subset_ball hx
  refine' ⟨ball x ε', _⟩
  simp only [Metric.ball_mem_nhds x He, exists_true_left]
  intro y hy
  exact
    ContinuousOn.aemeasurable (continuous_circle_transform hR hf (HB hy)).ContinuousOn
      measurableSet_Ioc

theorem circle_intervalIntegrable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) :
    IntervalIntegrable ((fun w => fun θ => circleTransform R z w f θ) x) volume 0 (2 * π) :=
  ContinuousOn.intervalIntegrable (continuous_circleTransform hR hf hx).ContinuousOn

theorem circleTransformDeriv_aEMeasurable {R : ℝ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sphere z R)) :
    AEMeasurable ((fun w θ => circleTransformDeriv R z w f θ) x) (volume.restrict (Ι 0 (2 * π))) :=
  ContinuousOn.aemeasurable (continuous_circleTransformDeriv hR hf hx).ContinuousOn
    measurableSet_Ioc

/-- The `circle_integral_form` of a function, which is continuous on `sphere z R` is differentiable
on `ball z R`. -/
theorem circleIntegralForm_differentiableOn {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (hf : ContinuousOn f (sphere z R)) : DifferentiableOn ℂ (circleIntegralForm R z f) (ball z R) :=
  by
  simp_rw [circle_integral_form, ← circle_transform_circle_int R z _ f, DifferentiableOn,
    DifferentiableWithinAt]
  intro x hx
  have h4R : 0 < 4⁻¹ * R := by apply Left.mul_pos; rw [inv_pos]; linarith; apply hR
  set F : ℂ → ℝ → ℂ := fun w => fun θ => circle_transform R z w f θ
  set F' : ℂ → ℝ → ℂ := fun w => circle_transform_deriv R z w f
  have hF_meas : ∀ᶠ y in 𝓝 x, ae_strongly_measurable (F y) (volume.restrict (Ι 0 (2 * π))) :=
    by
    simp_rw [F, _root_.ae_strongly_measurable_iff_ae_measurable]
    exact circle_transform_ae_measurable hR z x hx hf
  have hF_int : IntervalIntegrable (F x) volume 0 (2 * π) :=
    by
    simp_rw [F]
    apply circle_interval_integrable hR z x hx hf
  have hF'_meas : ae_strongly_measurable (F' x) (volume.restrict (Ι 0 (2 * π))) :=
    by
    simp_rw [F', _root_.ae_strongly_measurable_iff_ae_measurable]
    exact circle_transform_deriv_ae_measurable hR z x hx f hf
  have BOU := circle_transform_deriv_bound hR hx hf
  obtain ⟨bound, ε, hε, h_ball, h_boun⟩ := BOU
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε, Complex.abs (F' y t) ≤ bound :=
    by
    apply eventually_of_forall
    exact fun _ => fun _ => by apply h_boun
  have bound_integrable : IntervalIntegrable (fun _ => bound) volume 0 (2 * π) :=
    _root_.interval_integrable_const
  have h_diff :
    ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε, HasDerivAt (fun y => F y t) (F' y t) y :=
    by
    simp_rw [F, F', circle_transform, circle_transform_deriv]
    have := circle_transform_has_deriv_at R z f
    apply eventually_of_forall
    simp_rw [circle_transform, circle_transform_deriv] at this 
    intro y hy x hx
    simp [real.two_pi_pos.le] at hy 
    have hy2 : y ∈ [0, 2 * π] := by
      convert Ioc_subset_Icc_self hy
      simp [real.two_pi_pos.le]
    exact this y x (h_ball hx)
  have :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hF_meas hF_int hF'_meas
      h_bound bound_integrable h_diff
  simp only [F, HasDerivAt, HasDerivAtFilter, HasFDerivWithinAt, mem_ball, zero_lt_mul_left,
    inv_pos, zero_lt_bit0, zero_lt_one, norm_eq_abs] at *
  exact
    ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (intervalIntegral (F' x) 0 (2 * π) volume),
      HasFDerivAtFilter.mono this.2 inf_le_left⟩

/-- The differece of the `circle_transform` of two functions `f,g` is the `circle_transform` of the
difference `f - g`. -/
theorem circleTransform_sub (R : ℝ) (f g : ℂ → ℂ) (z w : ℂ) (θ : ℝ) :
    (circleTransform R z w f) θ - (circleTransform R z w g) θ = circleTransform R z w (f - g) θ :=
  by
  simp only [circle_transform, mul_inv_rev, inv_I, neg_mul, deriv_circleMap, Algebra.id.smul_eq_mul,
    neg_sub_neg, Pi.sub_apply]
  ring

theorem circleTransform_of_bound_is_bound {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (z w : ℂ) (r : ℝ)
    (h : ∀ x : sphere z R, Complex.abs (f x) ≤ abs r) (θ : ℝ) :
    Complex.abs (circleTransform R z w f θ) ≤ Complex.abs (circleTransform R z w (fun x => r) θ) :=
  by
  simp only [circle_transform, abs_of_real, mul_one, Algebra.id.smul_eq_mul, abs_I, abs_two, ←
    mul_assoc, deriv_circleMap, abs_circleMap_zero, mul_inv_rev, inv_I, AbsoluteValue.map_neg,
    AbsoluteValue.map_mul, map_inv₀, one_mul]
  apply_rules [monotone_mul_left_of_nonneg, mul_nonneg, mul_nonneg]
  repeat' simp_rw [inv_nonneg]
  swap
  nlinarith
  repeat' apply _root_.abs_nonneg
  · simp only [map_nonneg]
  · simp only [abs_of_real, SetCoe.forall, Subtype.coe_mk] at h 
    exact h _ (circleMap_mem_sphere z hR.le θ)

/-- The `circle_transform` of a function is integrable. -/
theorem circleTransform_integrable {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (F_cts : ContinuousOn F (sphere z R)) (w : ball z R) :
    Integrable (circleTransform R z w F) (volume.restrict (Ioc 0 (2 * π))) :=
  by
  apply integrable_on.integrable
  rw [← intervalIntegrable_iff_integrable_Ioc_of_le real.two_pi_pos.le]
  apply
    ContinuousOn.intervalIntegrable (continuous_circle_transform hR F_cts w.property).ContinuousOn
  exact Real.locallyFinite_volume

/-- The (complex) absolute value of the `circle_transform` of a function is integrable. -/
theorem circleTransform_integrable_abs {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (F_cts : ContinuousOn F (sphere z R)) (w : ball z R) :
    Integrable (Complex.abs ∘ circleTransform R z w F) (volume.restrict (Ioc 0 (2 * π))) :=
  ⟨(circleTransform_integrable hR z F_cts w).AEStronglyMeasurable.norm,
    (circleTransform_integrable hR z F_cts w).HasFiniteIntegral.norm⟩

theorem abs_sub_add_cancel_bound (x : ℂ) (r : ℝ)
    (h : ∃ b : ℂ, Complex.abs (x - b) + Complex.abs b ≤ r) : Complex.abs x ≤ r :=
  by
  obtain ⟨b, hb⟩ := h
  rw [← sub_add_cancel x b]
  exact le_trans (abs.add_le (x - b) b) hb

/-- The `circle_transform` of a unifom limit of functions `F n` tends to the `circle_transform` of
  the limit function `f`. -/
theorem circleTransform_of_unifom_limit {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ) (z : ℂ)
    (hlim : TendstoUniformlyOn F f Filter.atTop (sphere z R)) (w : ball z R) (y : ℝ) :
    Tendsto (fun n => (circleTransform R z w (F n)) y) atTop (𝓝 ((circleTransform R z w f) y)) :=
  by
  rw [Metric.tendstoUniformlyOn_iff] at hlim 
  simp only [Metric.tendsto_nhds, dist_comm, circle_transform, one_div, Algebra.id.smul_eq_mul,
    gt_iff_lt, mem_closed_ball, Nat.cast_bit0, real_smul, ge_iff_le, nsmul_eq_mul, Nat.cast_one,
    eventually_at_top] at *
  intro ε hε
  set r : ℂ := (2 * π * I : ℂ)⁻¹ * circleMap 0 R y * I * (circleMap z R y - ↑w)⁻¹
  have hr : 0 < Complex.abs r :=
    by
    simp only [r, norm_eq_abs, abs_mul, abs_inv, abs_two, abs_of_real, abs_I, mul_one,
      abs_circleMap_zero]
    simp only [AbsoluteValue.map_neg, AbsoluteValue.map_mul, abs_I, map_inv₀, abs_of_real, abs_two,
      one_mul, abs_circleMap_zero, mul_one]
    apply
      Left.mul_pos
        (Left.mul_pos
          (inv_pos.2 (Left.mul_pos (@two_pos ℝ _ _ _ _ _) (_root_.abs_pos.2 Real.pi_ne_zero)))
          (_root_.abs_pos_of_pos hR))
        _
    simp only [inv_pos, AbsoluteValue.pos_iff]
    exact sub_ne_zero.2 (circleMap_ne_mem_ball w.2 y)
  let e := (Complex.abs r)⁻¹ * (ε / 2)
  have he : 0 < e := by simp_rw [e]; apply mul_pos (inv_pos.2 hr) (div_pos hε two_pos)
  obtain ⟨a, ha⟩ := hlim e he
  refine' ⟨a, fun b hb => _⟩
  simp_rw [deriv_circleMap, dist_eq_norm, ← mul_sub] at *
  have hg :
    Complex.abs
        ((2 * π * I : ℂ)⁻¹ *
          (circleMap 0 R y * I *
            ((circleMap z R y - ↑w)⁻¹ * (f (circleMap z R y) - F b (circleMap z R y))))) =
      Complex.abs ((2 * π * I : ℂ)⁻¹ * circleMap 0 R y * I * (circleMap z R y - ↑w)⁻¹) *
        Complex.abs (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))) :=
    by
    simp only [circleMap, abs_of_real, abs_exp_of_real_mul_I, mul_one, abs_I, abs_two, norm_eq_abs,
      mul_inv_rev, inv_I, zero_add, one_mul, AbsoluteValue.map_neg, AbsoluteValue.map_mul, map_inv₀]
    ring
  simp at *
  simp_rw [hg]
  have hab := (ha b hb) (z + ↑R * exp (↑y * I)) (circleMap_mem_sphere z hR.le y)
  apply lt_trans (mul_lt_mul_of_pos_left hab hr)
  simp_rw [e, r]
  simp only [mul_inv_rev, AbsoluteValue.map_mul, abs_I, map_inv₀, abs_of_real, abs_two,
    abs_circleMap_zero, mul_one, inv_inv]
  simp_rw [div_eq_inv_mul, ← mul_assoc]
  have := mul_inv_cancel (ne_of_gt hr)
  have hfin :
    |π|⁻¹ * 2⁻¹ * |R| * (Complex.abs (circleMap z R y - ↑w))⁻¹ *
                Complex.abs (circleMap z R y - ↑w) *
              |R|⁻¹ *
            2 *
          |π| *
        2⁻¹ =
      2⁻¹ *
        (|π|⁻¹ * 2⁻¹ * |R| * (Complex.abs (circleMap z R y - ↑w))⁻¹ *
          (|π|⁻¹ * 2⁻¹ * |R| * (Complex.abs (circleMap z R y - ↑w))⁻¹)⁻¹) :=
    by simp only [mul_inv_rev, inv_inv]; ring
  rw [hfin, this]
  simp only [inv_eq_one_div]
  nlinarith

/-- A uniform limit of functions on a `sphere` can be eventually bounded by an integrable
function.  -/
theorem circleTransform_of_uniform_exists_bounding_function {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R)
    (f : ℂ → ℂ) (z : ℂ) (w : ball z R) (F_cts : ∀ n, ContinuousOn (F n) (sphere z R))
    (hlim : TendstoUniformlyOn F f Filter.atTop (sphere z R)) :
    ∃ bound : ℝ → ℝ,
      (∀ n,
          ∀ᵐ r ∂volume.restrict (Ioc 0 (2 * π)),
            Complex.abs ((circleTransform R z w (F n)) r) ≤ bound r) ∧
        Integrable bound (volume.restrict (Ioc 0 (2 * π))) :=
  by
  have f_cont : ContinuousOn f (sphere z R) :=
    by
    apply TendstoUniformlyOn.continuousOn hlim
    simp only [F_cts, eventually_at_top, imp_true_iff, exists_const]
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, ge_iff_le, eventually_at_top] at hlim 
  obtain ⟨a, ha⟩ := hlim 1 zero_lt_one
  set bound : ℝ → ℝ := fun θ =>
    ∑ i in Finset.range (a + 1), Complex.abs ((circle_transform R z w (F i)) θ) +
        Complex.abs ((circle_transform R z w fun x => 1) θ) +
      Complex.abs ((circle_transform R z w f) θ)
  refine' ⟨bound, fun n => _, _⟩
  rw [ae_restrict_iff']
  apply eventually_of_forall
  intro y hyl
  by_cases n ≤ a
  simp_rw [bound]
  have hnn : n ∈ Finset.range (a + 1) := by simp only [Finset.mem_range]; linarith
  have :=
    Finset.add_sum_erase (Finset.range (a + 1))
      (fun i => Complex.abs ((circle_transform R z w (F i)) y)) hnn
  simp only [and_imp, mem_Ioc, Finset.mem_range, mem_sphere_iff_norm, norm_eq_abs] at *
  simp_rw [← this, add_assoc, le_add_iff_nonneg_right]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro a b
    apply AbsoluteValue.nonneg
  · apply add_nonneg
    apply AbsoluteValue.nonneg
    apply AbsoluteValue.nonneg
  · apply abs_sub_add_cancel_bound ((circle_transform R z w (F n)) y) (bound y)
    refine' ⟨circle_transform R z (↑w) f y, _⟩
    simp_rw [circle_transform_sub, bound]
    simp only [add_le_add_iff_right, Finset.univ_eq_attach]
    have := circle_transform_of_bound_is_bound hR (F n - f) z w 1
    have haan := ha n (not_le.1 h).le
    simp only [of_real_one, abs_one, Pi.sub_apply] at this 
    simp_rw [dist_eq_norm] at *
    simp only [norm_eq_abs] at haan 
    have haf : ∀ x : sphere z R, abs (F n x - f x) ≤ 1 := by intro x; rw [AbsoluteValue.map_sub];
      apply (haan x.1 x.property).le
    apply le_add_of_nonneg_of_le
    apply Finset.sum_nonneg
    intro d dd
    apply AbsoluteValue.nonneg
    simp only [AbsoluteValue.map_one] at this 
    apply (this haf) y
  · simp only [measurableSet_Ioc]
  · simp_rw [bound]
    apply_rules [integrable.add, integrable.add, integrable_finset_sum]
    refine' fun _ _ => circle_transform_integrable_abs hR z (F_cts _) w
    apply circle_transform_integrable_abs hR z continuous_const.continuous_on
    apply circle_transform_integrable_abs hR z f_cont

/-- The integral of a uniform limit of functions `F n` tends to the integral of the limit function
`f`. -/
theorem circle_int_uniform_lim_eq_lim_of_int {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ)
    (z : ℂ) (w : ball z R) (F_cts : ∀ n, ContinuousOn (F n) (sphere z R))
    (hlim : TendstoUniformlyOn F f Filter.atTop (sphere z R)) :
    Tendsto (fun n => ∫ θ : ℝ in 0 ..2 * π, (circleTransform R z w (F n)) θ) atTop
      (𝓝 <| ∫ θ : ℝ in 0 ..2 * π, (circleTransform R z w f) θ) :=
  by
  have F_measurable :
    ∀ n, ae_strongly_measurable (circle_transform R z w (F n)) (volume.restrict (Ioc 0 (2 * π))) :=
    by
    intro n; simp_rw [_root_.ae_strongly_measurable_iff_ae_measurable]
    apply (circle_transform_integrable hR z (F_cts n) w).AEMeasurable
  have h_lim'' :
    ∀ a : ℝ,
      tendsto (fun n => (circle_transform R z w (F n)) a) at_top
        (𝓝 ((circle_transform R z w f) a)) :=
    by apply circle_transform_of_unifom_limit hR f z hlim
  have h_lim' :
    ∀ᵐ a ∂volume.restrict (Ioc 0 (2 * π)),
      tendsto (fun n => (circle_transform R z w (F n)) a) at_top
        (𝓝 ((circle_transform R z w f) a)) :=
    by simp only [h_lim'', eventually_true]
  have hboundlem := circle_transform_of_uniform_exists_bounding_function hR f z w F_cts hlim
  obtain ⟨bound, h_bound, bound_integrable⟩ := hboundlem
  simp_rw [integral_of_le real.two_pi_pos.le]
  exact tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable h_bound h_lim'

theorem complex_abs_sub_le (a b : ℂ) : Complex.abs (-b) = Complex.abs b :=
  abs.map_neg b

theorem Ineq1 (a b c d e f r : ℂ) (ε : ℝ) (hε : 0 < ε) (h1 : abs (a - b) < 8⁻¹ * abs r * ε)
    (h2 : abs (c - d) < 8⁻¹ * abs r * ε) (h3 : (abs r)⁻¹ * abs (b - d - (e - f)) < 2 / 3 * ε) :
    (abs r)⁻¹ * abs (a - b - (c - d) + (b - d) - (e - f)) < ε :=
  by
  have h4 :
    abs (a - b - (c - d) + (b - d) - (e - f)) ≤ abs (a - b - (c - d)) + abs (b - d - (e - f)) := by
    convert complex.abs.add_le' (a - b - (c - d)) (b - d - (e - f)); ring_nf
  have h5 : abs (a - b - (c - d)) ≤ abs (a - b) + abs (c - d) :=
    by
    have := abs.sub_le (a - b) 0 (c - d)
    simp at this 
    rw [abs.map_sub c d]
    exact this
  have h6 :
    (abs r)⁻¹ * abs (a - b - (c - d) + (b - d) - (e - f)) ≤
      (abs r)⁻¹ * abs (a - b) + (abs r)⁻¹ * abs (c - d) + (abs r)⁻¹ * abs (b - d - (e - f)) :=
    by
    simp_rw [← mul_add]; nth_rw_lhs 1 [mul_comm]; nth_rw_rhs 1 [mul_comm]
    apply mul_le_mul_of_nonneg_right; swap; rw [inv_nonneg]; simp; simp_rw [← add_assoc]
    apply le_trans h4; simp_rw [← add_assoc]; simp only [h5, add_le_add_iff_right]
  have hr : 0 < abs r := by
    by_contra h
    simp at h 
    rw [h] at h1 
    simp [MulZeroClass.zero_mul, abs_zero, MulZeroClass.mul_zero] at h1 
    linarith [abs.nonneg (a - b), h1]
  have e1 : 8⁻¹ * abs r * ε = 8⁻¹ * ε * abs r := by ring_nf
  rw [e1] at *
  apply
    lt_trans
      (lt_of_le_of_lt h6
        (add_lt_add (add_lt_add ((inv_mul_lt_iff' hr).mpr h1) ((inv_mul_lt_iff' hr).mpr h2)) h3))
  ring
  linarith

theorem Ineq2 (a b c d r : ℂ) (ε : ℝ) (hε : 0 < ε)
    (h :
      ∃ x y : ℂ,
        abs (a - y) < 8⁻¹ * abs r * ε ∧
          abs (b - x) < 8⁻¹ * abs r * ε ∧ (abs r)⁻¹ * abs (y - x - (c - d)) < 8⁻¹ * ε) :
    (abs r)⁻¹ * abs (a - b - (c - d)) < 2 / 3 * ε :=
  by
  obtain ⟨x, y, h1, h2, h3⟩ := h
  have hr : 0 < abs r := by
    by_contra h
    simp at h 
    simp [h, MulZeroClass.zero_mul, abs_zero, MulZeroClass.mul_zero] at h1 
    linarith [abs.nonneg (a - y), h1]
  have h33 : (abs r)⁻¹ * abs (c - d - (y - x)) < 8⁻¹ * ε := by rw [abs.map_sub]; apply h3
  have h5 : abs (a - b - (c - d)) = abs (a - y - (b - x) - (c - d - (y - x))) := by ring_nf
  rw [h5]
  have h6 :
    (abs r)⁻¹ * abs (a - y - (b - x) - (c - d - (y - x))) ≤
      (abs r)⁻¹ * abs (a - y) + (abs r)⁻¹ * abs (b - x) + (abs r)⁻¹ * abs (c - d - (y - x)) :=
    by
    simp_rw [← mul_add]; nth_rw_lhs 1 [mul_comm]; nth_rw_rhs 1 [mul_comm]
    apply mul_le_mul_of_nonneg_right; swap; simp
    have h4 :
      abs (a - y - (b - x) + -(c - d - (y - x))) ≤ abs (a - y - (b - x)) + abs (c - d - (y - x)) :=
      by
      have := complex.abs.add_le (a - y - (b - x)) (-(c - d - (y - x)))
      have ho : abs (c - d - (y - x)) = abs (-(c - d - (y - x))) := by rw [abs.map_neg]
      rw [ho]
      convert this
    have h44 : abs (a - y - (b - x)) ≤ abs (a - y) + abs (b - x) :=
      by
      have := abs.sub_le (a - y) 0 (b - x)
      simp only [zero_sub, sub_zero, neg_sub] at this 
      have hcd : abs (b - x) = abs (x - b) := by apply abs.map_sub
      convert this
    apply le_trans h4
    simp only [← add_assoc, h44, add_le_add_iff_right]
  have e1 : 8⁻¹ * abs r * ε = 8⁻¹ * ε * abs r := by ring_nf
  rw [e1] at *
  apply
    lt_trans
      (lt_of_le_of_lt h6
        (add_lt_add (add_lt_add ((inv_mul_lt_iff' hr).mpr h1) ((inv_mul_lt_iff' hr).mpr h2)) h33))
  field_simp
  linarith

theorem Ineq3 (a b c d e f r : ℂ) (ε : ℝ) (hε : 0 < ε) (h1 : abs (a - b) < 8⁻¹ * abs r * ε)
    (h2 : abs (c - d) < 8⁻¹ * abs r * ε)
    (h :
      ∃ x y : ℂ,
        abs (b - y) < 8⁻¹ * abs r * ε ∧
          abs (d - x) < 8⁻¹ * abs r * ε ∧ (abs r)⁻¹ * abs (y - x - (e - f)) < 8⁻¹ * ε) :
    (abs r)⁻¹ * abs (a - b - (c - d) + (b - d) - (e - f)) < ε :=
  by
  apply Ineq1 _ _ _ _ _ _ _ _ hε h1 h2
  apply Ineq2 _ _ _ _ _ _ hε h

theorem circle_integral_unif_of_diff_has_fderiv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (z : ℂ) (R : ℝ)
    (hlim : TendstoUniformlyOn F f Filter.atTop (closedBall z R))
    (F_alt : ∀ (n : ℕ) (c : ball z R), F n c = (circleIntegralForm R z (F n)) c) (x : ℂ)
    (hx : x ∈ ball z R)
    (keyb :
      ∀ w : ↥(ball z R),
        Tendsto (fun n : ℕ => ∫ θ : ℝ in 0 ..2 * π, circleTransform R z (↑w) (F n) θ) atTop
          (𝓝 (∫ θ : ℝ in 0 ..2 * π, circleTransform R z (↑w) f θ)))
    (D : ℂ →L[ℂ] ℂ) (hD : HasFDerivWithinAt (circleIntegralForm R z f) D (ball z R) x) :
    ∃ f' : ℂ →L[ℂ] ℂ, HasFDerivWithinAt f f' (ball z R) x :=
  by
  refine' ⟨D, _⟩
  simp_rw [hasFDerivWithinAt_iff_tendsto, Metric.tendsto_nhds, tendsto_uniformly_on_iff,
    dist_eq_norm] at *
  intro ε hε
  have h8 : 0 < 8⁻¹ * ε := by rw [inv_eq_one_div]; linarith
  have hDε := hD (8⁻¹ * ε) h8
  clear hD
  simp only [mem_ball, gt_iff_lt, mem_closed_ball, norm_mul, ge_iff_le, instNonempty, sub_zero,
    zero_lt_bit0, zero_lt_mul_left, ContinuousLinearMap.map_sub, SetCoe.forall, Subtype.coe_mk,
    eventually_at_top, zero_lt_one, inv_pos, norm_eq_abs, norm_inv] at *
  rw [Filter.eventually_iff_exists_mem] at *
  obtain ⟨S1, hS1, HS1⟩ := hDε
  let U := S1 ⊓ ball z R
  refine' ⟨U, _⟩
  have hU : U ∈ 𝓝[ball z R] x :=
    by
    simp only [U, Metric.mem_nhdsWithin_iff, exists_prop, mem_ball, and_true_iff, gt_iff_lt,
      inf_eq_inter, inter_subset_right, subset_inter_iff] at *
    exact hS1
  simp only [hU, exists_true_left]
  clear hU hS1
  intro y hy
  simp_rw [U] at hy 
  by_cases ht : abs (y - x) ≠ 0
  simp [mem_ball, inf_eq_inter] at hy 
  simp_rw [Real.norm_eq_abs, abs_abs]
  have h8' : 0 < 8⁻¹ * abs (y - x) * ε :=
    by
    have : 0 < (8 : ℝ) := by linarith
    apply mul_pos (mul_pos (inv_pos.2 this) _) hε; apply abs.pos; simp at ht ;
    exact sub_ne_zero.mpr ht
  obtain ⟨a'', ha''⟩ := (keyb y (mem_ball.2 hy.2)) (8⁻¹ * abs (y - x) * ε) h8'
  obtain ⟨a, ha⟩ := hlim (8⁻¹ * abs (y - x) * ε) h8'
  obtain ⟨a', ha'⟩ := (keyb x hx) (8⁻¹ * abs (y - x) * ε) h8'
  set A' : ℕ := max a a'
  have test := mem_ball.1 (mem_ball.2 hy.2)
  simp only [mem_ball, abs_eq_zero, Ne.def, Subtype.coe_mk] at *
  set A : ℕ := max A' a''
  have haA : a ≤ A := by simp only [le_refl, true_or_iff, le_max_iff]
  have ha'A : a' ≤ A := by simp only [le_refl, true_or_iff, or_true_iff, le_max_iff]
  have ha''A : a'' ≤ A := by simp only [le_refl, or_true_iff, le_max_iff]
  have HH :
    ∀ y : ℂ,
      f y - f x - (D y - D x) = f y - F A y - (f x - F A x) + (F A y - F A x) - (D y - D x) :=
    by intro y; simp only [sub_left_inj]; ring_nf
  simp_rw [HH]
  apply
    Ineq3 _ _ _ _ _ _ _ _ hε (ha A haA y (mem_ball.1 (mem_ball.2 hy.2)).le)
      (ha A haA x (mem_ball.1 hx).le)
  clear keyb HH hε h8 h8'
  refine' ⟨circle_integral_form R z f x, circle_integral_form R z f y, _⟩
  simp_rw [circle_intgral_form_eq_int]
  refine'
    ⟨by
      have := F_alt A ⟨y, mem_ball.2 hy.2⟩
      simp only [Subtype.coe_mk] at this 
      rw [this, circle_intgral_form_eq_int]
      apply ha'' A ha''A, by
      have := F_alt A ⟨x, mem_ball.2 hx⟩
      simp only [Subtype.coe_mk] at this 
      rw [this, circle_intgral_form_eq_int]
      apply ha' A ha'A,
      by
      simp_rw [Real.norm_eq_abs, abs_abs, circle_intgral_form_eq_int] at HS1 
      apply HS1 _ hy.1⟩
  simp only [abs_eq_zero, Classical.not_not] at ht 
  simp only [ht, norm_zero, MulZeroClass.zero_mul, abs_zero, inv_zero, hε]

theorem uniform_of_diff_circle_int_is_diff {R : ℝ} (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (hR : 0 < R)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (closedBall z R))
    (hlim : TendstoUniformlyOn F f Filter.atTop (closedBall z R)) :
    DifferentiableOn ℂ f (ball z R) :=
  by
  have F_alt : ∀ (n : ℕ) (c : ball z R), F n c = (circle_integral_form R z (F n)) c :=
    by
    intro n c
    have hc : c.1 ∈ ball z R := by apply c.property
    have hcc : ∀ x : ℂ, x ∈ ball z R \ ∅ → DifferentiableAt ℂ (F n) x :=
      by
      simp only [diff_empty]; intro x hx
      apply_rules [(hdiff n).DifferentiableAt, closed_ball_mem_nhds_of_mem, hx]
    have ttt :=
      two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
        countable_empty hc (hdiff n).ContinuousOn hcc
    simp only [mem_ball, Algebra.id.smul_eq_mul, Subtype.val_eq_coe, diff_empty] at *
    rw [← ttt]
    simp only [circle_integral_form, circle_transform, one_div, Algebra.id.smul_eq_mul,
      Nat.cast_bit0, real_smul, integral_const_mul, nsmul_eq_mul, Nat.cast_one]
  have F_cts_ball : ∀ n, ContinuousOn (F n) (closed_ball z R) := by intro n;
    apply (hdiff n).ContinuousOn
  have F_cts_sphere : ∀ n, ContinuousOn (F n) (sphere z R) := by intro n;
    apply (F_cts_ball n).mono sphere_subset_closed_ball
  rw [DifferentiableOn]
  intro x hx
  have keyb := fun ww =>
    circle_int_uniform_lim_eq_lim_of_int hR f z ww F_cts_sphere
      (hlim.mono sphere_subset_closed_ball)
  rw [DifferentiableWithinAt]
  have hf : ContinuousOn f (closed_ball z R) :=
    by
    apply TendstoUniformlyOn.continuousOn hlim
    simp only [eventually_at_top, imp_true_iff, exists_const, F_cts_ball]
  have HF := circle_integral_form_differentiable_on hR z (hf.mono sphere_subset_closed_ball)
  clear hf F_cts_ball F_cts_sphere hdiff
  rw [DifferentiableOn] at HF 
  have HF2 := HF x hx
  clear HF
  simp only [hx, forall_true_left, DifferentiableWithinAt] at HF2 
  obtain ⟨D, hD⟩ := HF2
  apply circle_integral_unif_of_diff_has_fderiv z R hlim F_alt x hx keyb D hD

end Complex

