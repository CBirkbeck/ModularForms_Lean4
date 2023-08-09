/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleTransform

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

/-- Cauchy integral form of a function at `z` in a disk of radius `R`-/
def circleIntegralForm [CompleteSpace E] (R : ℝ) (z : ℂ) (f : ℂ → E) : ℂ → E := fun w =>
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z
#align complex.circle_integral_form Complex.circleIntegralForm

theorem circle_intgral_form_eq_int [CompleteSpace E] (R : ℝ) (z : ℂ) (f : ℂ → E) :
    circleIntegralForm R z f = fun w => ∫ θ : ℝ in (0)..2 * π, (circleTransform R z w f) θ := by
  simp_rw [circleTransform, circleIntegralForm, circleIntegral, intervalIntegral.integral_smul]
#align complex.circle_intgral_form_eq_int Complex.circle_intgral_form_eq_int

theorem circleTransform_circle_int [CompleteSpace E] (R : ℝ) (z w : ℂ) (f : ℂ → E) :
    ∫ θ : ℝ in (0)..2 * π, circleTransform R z w f θ =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z :=
  by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp only [real_smul, nsmul_eq_mul, Nat.cast_one, one_div,
    intervalIntegral.integral_smul, zero_add]
#align complex.circle_transform_circle_int Complex.circleTransform_circle_int

theorem circleTransform_hasDerivAt (R : ℝ) (z : ℂ) (f : ℂ → ℂ) :
    ∀ (t : ℝ),
      ∀ y ∈ ball z R,
        HasDerivAt (fun y => (circleTransform R z y f) t) ((circleTransformDeriv R z y f) t) y :=
  by
  intro y x hx
  simp only [circleTransform, circleTransformDeriv, Algebra.id.smul_eq_mul, ← mul_assoc,
    deriv_circleMap]
  apply_rules [HasDerivAt.mul_const, HasDerivAt.const_mul]
  have H : HasDerivAt (fun y_1 : ℂ => circleMap z R y - y_1) (-1) x := by
    apply HasDerivAt.const_sub; apply hasDerivAt_id
  have hfin := HasDerivAt.inv H (sub_ne_zero.2 (circleMap_ne_mem_ball hx y))
  simp only [one_div, neg_neg] at hfin
  exact hfin
#align complex.circle_transform_has_deriv_at Complex.circleTransform_hasDerivAt

theorem circleTransform_aemeasurable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) :
    ∀ᶠ y in 𝓝 x,
      AEMeasurable ((fun w => fun θ => circleTransform R z w f θ) y)
        (volume.restrict (Ι 0 (2 * π))) :=
  by
  rw [Filter.eventually_iff_exists_mem]
  obtain ⟨ε', He, HB⟩ := exists_ball_subset_ball hx
  refine' ⟨ball x ε', _⟩
  simp only [Metric.ball_mem_nhds x He, true_and]
  intro y hy
  exact
    ContinuousOn.aemeasurable (continuous_circleTransform hR hf (HB hy)).continuousOn
      measurableSet_Ioc
#align complex.circle_transform_ae_measurable Complex.circleTransform_aemeasurable

theorem circle_intervalIntegrable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) :
    IntervalIntegrable ((fun w => fun θ => circleTransform R z w f θ) x) volume 0 (2 * π) :=
  ContinuousOn.intervalIntegrable (continuous_circleTransform hR hf hx).continuousOn
#align complex.circle_interval_integrable Complex.circle_intervalIntegrable

theorem circleTransformDeriv_aemeasurable {R : ℝ} (hR : 0 < R) (z x : ℂ) (hx : x ∈ ball z R)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sphere z R)) :
    AEMeasurable ((fun w θ => circleTransformDeriv R z w f θ) x) (volume.restrict (Ι 0 (2 * π))) :=
  ContinuousOn.aemeasurable (continuous_circleTransformDeriv hR hf hx).continuousOn
    measurableSet_Ioc
#align complex.circle_transform_deriv_ae_measurable Complex.circleTransformDeriv_aemeasurable

/-- The `circleIntegralForm` of a function, which is continuous on `sphere z R` is differentiable
on `ball z R`. -/
theorem circleIntegralForm_differentiableOn {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (hf : ContinuousOn f (sphere z R)) : DifferentiableOn ℂ (circleIntegralForm R z f) (ball z R) :=
  by
  simp_rw [circleIntegralForm, ← circleTransform_circle_int R z _ f, DifferentiableOn,
    DifferentiableWithinAt]
  intro x hx
  set F : ℂ → ℝ → ℂ := fun w => fun θ => circleTransform R z w f θ
  set F' : ℂ → ℝ → ℂ := fun w => circleTransformDeriv R z w f
  have hF_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (Ι 0 (2 * π))) :=
    by
    simp_rw [_root_.aestronglyMeasurable_iff_aemeasurable]
    exact circleTransform_aemeasurable hR z x hx hf
  have hF_int : IntervalIntegrable (F x) volume 0 (2 * π) :=
    by
    simp_rw []
    apply circle_intervalIntegrable hR z x hx hf
  have hF'_meas : AEStronglyMeasurable (F' x) (volume.restrict (Ι 0 (2 * π))) :=
    by
    simp_rw [_root_.aestronglyMeasurable_iff_aemeasurable]
    exact circleTransformDeriv_aemeasurable hR z x hx f hf
  have BOU := circleTransformDeriv_bound hR hx hf
  obtain ⟨bound, ε, hε, h_ball, h_boun⟩ := BOU
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε, Complex.abs (F' y t) ≤ bound :=
    by
    apply eventually_of_forall
    exact fun _ => fun _ => by apply h_boun
  have bound_integrable : IntervalIntegrable (fun _ => bound) volume 0 (2 * π) :=
    _root_.intervalIntegrable_const
  have h_diff :
    ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε, HasDerivAt (fun y => F y t) (F' y t) y :=
    by
    simp_rw [circleTransform, circleTransformDeriv]
    have := circleTransform_hasDerivAt R z f
    apply eventually_of_forall
    simp_rw [circleTransform, circleTransformDeriv] at this
    intro y hy x hx
    simp [Real.two_pi_pos.le] at hy
    exact this y x (h_ball hx) 
  have :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hF_meas hF_int hF'_meas
      h_bound bound_integrable h_diff
  simp only [HasDerivAt, HasDerivAtFilter, HasFDerivWithinAt, mem_ball, zero_lt_mul_left,
    inv_pos, zero_lt_bit0, zero_lt_one, norm_eq_abs, intervalIntegrable_const] at *
  exact
    ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (intervalIntegral (F' x) 0 (2 * π) volume),
      HasFDerivAtFilter.mono this.2 inf_le_left⟩
#align complex.circle_integral_form_differentiable_on Complex.circleIntegralForm_differentiableOn

/-- The differece of the `circle_transform` of two functions `f,g` is the `circle_transform` of the
difference `f - g`. -/
theorem circleTransform_sub (R : ℝ) (f g : ℂ → ℂ) (z w : ℂ) (θ : ℝ) :
    (circleTransform R z w f) θ - (circleTransform R z w g) θ = circleTransform R z w (f - g) θ :=
  by
  simp only [circleTransform, mul_inv_rev, inv_I, neg_mul, deriv_circleMap, Algebra.id.smul_eq_mul,
    neg_sub_neg, Pi.sub_apply]
  ring
#align complex.circle_transform_sub Complex.circleTransform_sub

theorem circleTransform_of_bound_is_bound {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (z w : ℂ) (r : ℝ)
    (h : ∀ x : sphere z R, Complex.abs (f x) ≤ abs r) (θ : ℝ) :
    Complex.abs (circleTransform R z w f θ) ≤ Complex.abs (circleTransform R z w (fun _ => r) θ) :=
  by
  simp only [circleTransform, abs_ofReal, mul_one, Algebra.id.smul_eq_mul, abs_I, abs_two, ←
    mul_assoc, deriv_circleMap, abs_circleMap_zero, mul_inv_rev, inv_I, AbsoluteValue.map_neg,
    AbsoluteValue.map_mul, map_inv₀, one_mul]
  apply monotone_mul_left_of_nonneg
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  rw [inv_nonneg]
  apply _root_.abs_nonneg
  rw [inv_nonneg]
  linarith
  apply _root_.abs_nonneg
  rw [inv_nonneg]
  apply Complex.abs.nonneg
  have hz := (circleMap_mem_sphere z hR.le θ)
  simpa using  (h ⟨circleMap z R θ, hz⟩)

#align complex.circle_transform_of_bound_is_bound Complex.circleTransform_of_bound_is_bound

/-- The `circle_transform` of a function is integrable. -/
theorem circleTransform_integrable {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (F_cts : ContinuousOn F (sphere z R)) (w : ball z R) :
    Integrable (circleTransform R z w F) (volume.restrict (Ioc 0 (2 * π))) :=
  by
  apply IntegrableOn.integrable
  rw [← intervalIntegrable_iff_integrable_Ioc_of_le Real.two_pi_pos.le]
  apply
    ContinuousOn.intervalIntegrable (continuous_circleTransform hR F_cts w.property).continuousOn
  -- exact Real.locallyFinite_volume
#align complex.circle_transform_integrable Complex.circleTransform_integrable

/-- The (complex) absolute value of the `circle_transform` of a function is integrable. -/
theorem circleTransform_integrable_abs {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
    (F_cts : ContinuousOn F (sphere z R)) (w : ball z R) :
    Integrable (Complex.abs ∘ circleTransform R z w F) (volume.restrict (Ioc 0 (2 * π))) :=
  ⟨(circleTransform_integrable hR z F_cts w).aestronglyMeasurable.norm,
    (circleTransform_integrable hR z F_cts w).hasFiniteIntegral.norm⟩
#align complex.circle_transform_integrable_abs Complex.circleTransform_integrable_abs

theorem abs_sub_add_cancel_bound (x : ℂ) (r : ℝ)
    (h : ∃ b : ℂ, Complex.abs (x - b) + Complex.abs b ≤ r) : Complex.abs x ≤ r :=
  by
  obtain ⟨b, hb⟩ := h
  rw [← sub_add_cancel x b]
  exact le_trans (abs.add_le (x - b) b) hb
#align complex.abs_sub_add_cancel_bound Complex.abs_sub_add_cancel_bound

/-- The `circle_transform` of a unifom limit of functions `F n` tends to the `circle_transform` of
  the limit function `f`. -/
theorem circleTransform_of_unifom_limit {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ) (z : ℂ)
    (hlim : TendstoUniformlyOn F f Filter.atTop (sphere z R)) (w : ball z R) (y : ℝ) :
    Tendsto (fun n => (circleTransform R z w (F n)) y) atTop (𝓝 ((circleTransform R z w f) y)) :=
  by
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  simp only [Metric.tendsto_nhds, dist_comm, circleTransform, one_div, Algebra.id.smul_eq_mul,
    gt_iff_lt, mem_closedBall, real_smul, ge_iff_le, nsmul_eq_mul, Nat.cast_one,
    eventually_atTop] at *
  intro ε hε
  set r : ℂ := (2 * π * I : ℂ)⁻¹ * circleMap 0 R y * I * (circleMap z R y - ↑w)⁻¹
  have hr : 0 < Complex.abs r :=
    by
    simp only [norm_eq_abs, abs_mul, abs_inv, abs_two, abs_ofReal, abs_I, mul_one,
      abs_circleMap_zero]
    simp only [AbsoluteValue.map_neg, AbsoluteValue.map_mul, abs_I, map_inv₀, abs_ofReal, abs_two,
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
  have he : 0 < e := by  apply mul_pos (inv_pos.2 hr) (div_pos hε two_pos)

  obtain ⟨a, ha⟩ := hlim e he
  refine' ⟨a, fun b hb => _⟩
  simp_rw [deriv_circleMap, dist_eq_norm, ← mul_sub] at *
  have hg :
    Complex.abs
        ((2 * π * I : ℂ)⁻¹ *
          (circleMap 0 R y * I *
            ((circleMap z R y - ↑w)⁻¹ * (F b (circleMap z R y) - f (circleMap z R y))))) =
      Complex.abs ((2 * π * I : ℂ)⁻¹ * circleMap 0 R y * I * (circleMap z R y - ↑w)⁻¹) *
        Complex.abs (F b (z + ↑R * exp (↑y * I)) - f (z + ↑R * exp (↑y * I))) :=
    by
    simp only [circleMap, mul_inv_rev, inv_I, neg_mul, zero_add, map_neg_eq_map, map_mul, abs_I, 
      map_inv₀, abs_ofReal,abs_two, one_mul, abs_exp_ofReal_mul_I, mul_one]
  
    ring
  simp only [mul_inv_rev, inv_I, neg_mul, norm_neg, norm_mul, norm_eq_abs, abs_I, norm_inv, abs_ofReal,
    IsROrC.norm_ofNat, one_mul, abs_circleMap_zero, mul_one, gt_iff_lt] 
  simp only [mul_inv_rev, inv_I, neg_mul, map_neg_eq_map, map_mul, abs_I, map_inv₀, abs_ofReal, abs_two, one_mul,
    abs_circleMap_zero, mul_one] at hg
  simp_rw [hg]     
  have hab0 := (circleMap_mem_sphere z hR.le y)
  rw [circleMap] at hab0
  have hab2 := (ha b hb) (z + ↑R * exp (↑y * I)) 
  have hab := hab2 hab0
  have habb := mul_lt_mul_of_pos_left hab hr
  simp at habb
  apply lt_trans habb
  simp only [mul_inv_rev, AbsoluteValue.map_mul, abs_I, map_inv₀, abs_ofReal, abs_two,
    abs_circleMap_zero, mul_one, inv_inv]
  simp_rw [div_eq_inv_mul, ← mul_assoc]
  have := mul_inv_cancel (ne_of_gt hr)
  simp at this
  have hfinn : |π|⁻¹ * 2⁻¹ * |R| * (Complex.abs (circleMap z R y - ↑w))⁻¹ * Complex.abs (circleMap z R y - ↑w) 
    * |R|⁻¹ * 2 * |π| * 2⁻¹ * ε = 
    (|π|⁻¹ * 2⁻¹ * |R| * (Complex.abs (circleMap z R y - ↑w))⁻¹ * 
      (Complex.abs (circleMap z R y - ↑w) * (|R|⁻¹ * (2 * |π|))))*2⁻¹ *ε := 
      by ring
  rw [hfinn, this]
  simp only [inv_eq_one_div]
  nlinarith
#align complex.circle_transform_of_unifom_limit Complex.circleTransform_of_unifom_limit

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
    simp only [F_cts, eventually_atTop, imp_true_iff, exists_const]
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, ge_iff_le, eventually_atTop] at hlim
  obtain ⟨a, ha⟩ := hlim 1 zero_lt_one
  set bound : ℝ → ℝ := fun θ =>
    ∑ i in Finset.range (a + 1), Complex.abs ((circleTransform R z w (F i)) θ) +
        Complex.abs ((circleTransform R z w fun x => 1) θ) +
      Complex.abs ((circleTransform R z w f) θ)
  refine' ⟨bound, fun n => _, _⟩
  rw [ae_restrict_iff']
  apply eventually_of_forall
  intro y hyl
  by_cases h : n ≤ a
  simp_rw []
  have hnn : n ∈ Finset.range (a + 1) := by simp only [Finset.mem_range]; linarith
  have :=
    Finset.add_sum_erase (Finset.range (a + 1))
      (fun i => Complex.abs ((circleTransform R z w (F i)) y)) hnn
  simp only [and_imp, mem_Ioc, Finset.mem_range, mem_sphere_iff_norm, norm_eq_abs] at *
  simp_rw [← this, add_assoc, le_add_iff_nonneg_right]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro a _
    apply AbsoluteValue.nonneg
  · apply add_nonneg
    apply AbsoluteValue.nonneg
    apply AbsoluteValue.nonneg
  · apply abs_sub_add_cancel_bound ((circleTransform R z w (F n)) y) (bound y)
    refine' ⟨circleTransform R z (↑w) f y, _⟩
    simp_rw [circleTransform_sub]
    simp only [add_le_add_iff_right, Finset.univ_eq_attach]
    have := circleTransform_of_bound_is_bound hR (F n - f) z w 1
    have haan := ha n (not_le.1 h).le
    simp only [ofReal_one, abs_one, Pi.sub_apply] at this
    simp_rw [dist_eq_norm] at *
    simp only [norm_eq_abs] at haan
    have haf : ∀ x : sphere z R, abs (F n x - f x) ≤ 1 := by
      intro x; rw [AbsoluteValue.map_sub];
      apply (haan x.1 x.property).le
    apply le_add_of_nonneg_of_le
    apply Finset.sum_nonneg
    intro d _
    apply AbsoluteValue.nonneg
    simp only [AbsoluteValue.map_one] at this
    apply (this haf) y
  · simp only [measurableSet_Ioc]
  · simp_rw []
    apply_rules [Integrable.add, Integrable.add, integrable_finset_sum]
    refine' fun _ _ => circleTransform_integrable_abs hR z (F_cts _) w
    apply circleTransform_integrable_abs hR z continuous_const.continuousOn
    apply circleTransform_integrable_abs hR z f_cont 
#align complex.circle_transform_of_uniform_exists_bounding_function Complex.circleTransform_of_uniform_exists_bounding_function

/-- The integral of a uniform limit of functions `F n` tends to the integral of the limit function
`f`. -/
theorem circle_int_uniform_lim_eq_lim_of_int {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ)
    (z : ℂ) (w : ball z R) (F_cts : ∀ n, ContinuousOn (F n) (sphere z R))
    (hlim : TendstoUniformlyOn F f Filter.atTop (sphere z R)) :
    Tendsto (fun n => ∫ θ : ℝ in (0)..2 * π, (circleTransform R z w (F n)) θ) atTop
      (𝓝 <| ∫ θ : ℝ in (0)..2 * π, (circleTransform R z w f) θ) :=
  by
  have F_measurable :
    ∀ n, AEStronglyMeasurable (circleTransform R z w (F n)) (volume.restrict (Ioc 0 (2 * π))) :=
    by
    intro n; simp_rw [_root_.aestronglyMeasurable_iff_aemeasurable]
    apply (circleTransform_integrable hR z (F_cts n) w).aemeasurable
  have h_lim'' :
    ∀ a : ℝ,
      Tendsto (fun n => (circleTransform R z w (F n)) a) atTop
        (𝓝 ((circleTransform R z w f) a)) :=
    by apply circleTransform_of_unifom_limit hR f z hlim
  have h_lim' :
    ∀ᵐ a ∂volume.restrict (Ioc 0 (2 * π)),
      Tendsto (fun n => (circleTransform R z w (F n)) a) atTop
        (𝓝 ((circleTransform R z w f) a)) :=
    by simp only [h_lim'', eventually_true]
  have hboundlem := circleTransform_of_uniform_exists_bounding_function hR f z w F_cts hlim
  obtain ⟨bound, h_bound, bound_integrable⟩ := hboundlem
  simp_rw [integral_of_le Real.two_pi_pos.le]
  exact tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable h_bound h_lim'
#align complex.circle_int_uniform_lim_eq_lim_of_int Complex.circle_int_uniform_lim_eq_lim_of_int

theorem Ineq1 (a b c d e f r : ℂ) (ε : ℝ) (hε : 0 < ε) (h1 : abs (a - b) < 8⁻¹ * abs r * ε)
    (h2 : abs (c - d) < 8⁻¹ * abs r * ε) (h3 : (abs r)⁻¹ * abs (b - d - (e - f)) < 2 / 3 * ε) :
    (abs r)⁻¹ * abs (a - b - (c - d) + (b - d) - (e - f)) < ε :=
  by
  have h4 :
    Complex.abs (a - b - (c - d) + (b - d) - (e - f)) ≤ Complex.abs (a - b - (c - d)) + 
      Complex.abs (b - d - (e - f)) := by
    have:= Complex.abs.add_le' (a - b - (c - d)) (b - d - (e - f))
    simp at this
    have hh : a - b - (c - d) + (b - d) - (e - f) = a - b - (c - d) + (b - d - (e - f)) := by ring
    rw [hh]
    exact this
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
    simp_rw [← mul_add]; 
    apply mul_le_mul_of_nonneg_left; 
    swap; rw [inv_nonneg]; simp; simp_rw [← add_assoc]
    apply le_trans h4; simp_rw [← add_assoc]; simp only [h5, add_le_add_iff_right]
  have hr : 0 < abs r := by
    by_contra h
    simp at h
    rw [h] at h1
    simp [MulZeroClass.zero_mul, abs_zero, MulZeroClass.mul_zero] at h1
    linarith [abs.nonneg (a - b), h1]
  have e1 : 8⁻¹ * abs r * ε = 8⁻¹ * ε * abs r := by ring_nf
  rw [e1] at h1
  rw [e1] at h2
  apply
    lt_trans
      (lt_of_le_of_lt h6
        (add_lt_add (add_lt_add ((inv_mul_lt_iff' hr).mpr h1) ((inv_mul_lt_iff' hr).mpr h2)) h3))
  ring_nf
  simp
  linarith
#align complex.Ineq1 Complex.Ineq1

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
    simp_rw [← mul_add]; 
    apply mul_le_mul_of_nonneg_left; swap; simp
    have h4 :
      abs (a - y - (b - x) + -(c - d - (y - x))) ≤ abs (a - y - (b - x)) + abs (c - d - (y - x)) :=
      by
      have := Complex.abs.add_le (a - y - (b - x)) (-(c - d - (y - x)))
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
  rw [e1] at h1
  rw [e1] at h2
  apply
    lt_trans
      (lt_of_le_of_lt h6
        (add_lt_add (add_lt_add ((inv_mul_lt_iff' hr).mpr h1) ((inv_mul_lt_iff' hr).mpr h2)) h33))
  field_simp
  linarith
#align complex.Ineq2 Complex.Ineq2

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
#align complex.Ineq3 Complex.Ineq3

theorem circle_integral_unif_of_diff_has_fderiv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (z : ℂ) (R : ℝ)
    (hlim : TendstoUniformlyOn F f Filter.atTop (closedBall z R))
    (F_alt : ∀ (n : ℕ) (c : ball z R), F n c = (circleIntegralForm R z (F n)) c) (x : ℂ)
    (hx : x ∈ ball z R)
    (keyb :
      ∀ w : ↥(ball z R),
        Tendsto (fun n : ℕ => ∫ θ : ℝ in (0)..2 * π, circleTransform R z (↑w) (F n) θ) atTop
          (𝓝 (∫ θ : ℝ in (0)..2 * π, circleTransform R z (↑w) f θ)))
    (D : ℂ →L[ℂ] ℂ) (hD : HasFDerivWithinAt (circleIntegralForm R z f) D (ball z R) x) :
    ∃ f' : ℂ →L[ℂ] ℂ, HasFDerivWithinAt f f' (ball z R) x :=
  by
  refine' ⟨D, _⟩
  simp_rw [hasFDerivWithinAt_iff_tendsto, Metric.tendsto_nhds, tendstoUniformlyOn_iff,
    dist_eq_norm] at *
  intro ε hε
  have h8 : 0 < 8⁻¹ * ε := by rw [inv_eq_one_div]; linarith
  have hDε := hD (8⁻¹ * ε) h8
  clear hD
  simp only [mem_ball, gt_iff_lt, mem_closedBall, norm_mul, ge_iff_le, instNonempty, sub_zero,
    zero_lt_bit0, zero_lt_mul_left, ContinuousLinearMap.map_sub, SetCoe.forall, Subtype.coe_mk,
    eventually_atTop, zero_lt_one, inv_pos, norm_eq_abs, norm_inv] at *
  rw [Filter.eventually_iff_exists_mem] at *
  obtain ⟨S1, hS1, HS1⟩ := hDε
  let U := S1 ⊓ ball z R
  refine' ⟨U, _⟩
  have hU : U ∈ 𝓝[ball z R] x :=
    by
    simp only [Metric.mem_nhdsWithin_iff, exists_prop, mem_ball, and_true_iff, gt_iff_lt,
      inf_eq_inter, inter_subset_right, subset_inter_iff] at *
    exact hS1
  simp only [hU, true_and_iff]
  clear hU hS1
  intro y hy
  simp_rw [] at hy
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
  refine' ⟨circleIntegralForm R z f x, circleIntegralForm R z f y, _⟩
  simp_rw [circle_intgral_form_eq_int]
  refine'
    ⟨by
      have := F_alt A y (mem_ball.2 hy.2)
      simp only [Subtype.coe_mk] at this
      rw [this, circle_intgral_form_eq_int]
      apply ha'' A ha''A, by
      have := F_alt A x (mem_ball.2 hx)
      simp only [Subtype.coe_mk] at this
      rw [this, circle_intgral_form_eq_int]
      apply ha' A ha'A,
      by
      simp_rw [Real.norm_eq_abs, abs_abs, circle_intgral_form_eq_int] at HS1
      apply HS1 _ hy.1⟩
  simp only [abs_eq_zero, Classical.not_not] at ht
  simp only [ht, norm_zero, MulZeroClass.zero_mul, abs_zero, inv_zero, hε]
#align complex.circle_integral_unif_of_diff_has_fderiv Complex.circle_integral_unif_of_diff_has_fderiv

theorem uniform_of_diff_circle_int_is_diff {R : ℝ} (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (hR : 0 < R)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (closedBall z R))
    (hlim : TendstoUniformlyOn F f Filter.atTop (closedBall z R)) :
    DifferentiableOn ℂ f (ball z R) :=
  by
  have F_alt : ∀ (n : ℕ) (c : ball z R), F n c = (circleIntegralForm R z (F n)) c :=
    by
    intro n c
    have hc : c.1 ∈ ball z R := by apply c.property
    have hcc : ∀ x : ℂ, x ∈ ball z R \ ∅ → DifferentiableAt ℂ (F n) x :=
      by
      simp only [diff_empty]; intro x hx
      apply_rules [(hdiff n).differentiableAt, closedBall_mem_nhds_of_mem, hx]
    have ttt :=
      two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        countable_empty hc (hdiff n).continuousOn hcc
    simp only [mem_ball, Algebra.id.smul_eq_mul, diff_empty] at *
    rw [← ttt]
    simp only [circleIntegralForm, circleTransform, one_div, Algebra.id.smul_eq_mul,
       real_smul, integral_const_mul, nsmul_eq_mul, Nat.cast_one]
  have F_cts_ball : ∀ n, ContinuousOn (F n) (closedBall z R) := by
    intro n; apply (hdiff n).continuousOn
  have F_cts_sphere : ∀ n, ContinuousOn (F n) (sphere z R) := by
    intro n; apply (F_cts_ball n).mono sphere_subset_closedBall
  rw [DifferentiableOn]
  intro x hx
  have keyb := fun ww =>
    circle_int_uniform_lim_eq_lim_of_int hR f z ww F_cts_sphere
      (hlim.mono sphere_subset_closedBall)
  rw [DifferentiableWithinAt]
  have hf : ContinuousOn f (closedBall z R) :=
    by
    apply TendstoUniformlyOn.continuousOn hlim
    simp only [eventually_atTop, imp_true_iff, exists_const, F_cts_ball]
  have HF := circleIntegralForm_differentiableOn hR z (hf.mono sphere_subset_closedBall)
  clear hf F_cts_ball F_cts_sphere hdiff
  rw [DifferentiableOn] at HF
  have HF2 := HF x hx
  clear HF
  simp only [hx, forall_true_left, DifferentiableWithinAt] at HF2
  obtain ⟨D, hD⟩ := HF2
  apply circle_integral_unif_of_diff_has_fderiv z R hlim F_alt x hx keyb D hD
#align complex.uniform_of_diff_circle_int_is_diff Complex.uniform_of_diff_circle_int_is_diff

end Complex