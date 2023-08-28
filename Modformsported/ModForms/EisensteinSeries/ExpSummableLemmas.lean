import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.Calculus.Series
import Modformsported.ModForms.EisensteinSeries.TsumLemmas
import Modformsported.ForMathlib.ModForms2
import Modformsported.ModForms.HolomorphicFunctions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic 
import Modformsported.ModForms.EisensteinSeries.EisensteinSeriesIndexLemmas
import Modformsported.ModForms.EisensteinSeries.IteratedDerivLemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

--local notation "ℍ" => UpperHalfPlane

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

theorem exp_upperHalfPlane_lt_one (z : ℍ) : Complex.abs (Complex.exp (2 * ↑π * I * z)) < 1 :=
  by
  rw [← UpperHalfPlane.re_add_im]
  rw [mul_add]
  rw [exp_add]
  simp only [AbsoluteValue.map_mul]
  have h1 : Complex.abs (exp (2 * ↑π * I * ↑z.re)) = Complex.abs (exp (2 * ↑π * ↑z.re * I)) := by
    ring_nf
  rw [h1]
  norm_cast
  have := abs_exp_of_real_mul_I (2 * π * z.re)
  rw [this]
  simp only [of_real_mul, of_real_bit0, of_real_one, one_mul]
  have h2 :
    Complex.abs (exp (2 * ↑π * I * (↑z.im * I))) = Complex.abs (exp (2 * ↑π * (↑z.im * I ^ 2))) :=
    by ring_nf
  rw [h2]
  simp only [I_sq, mul_neg, mul_one]
  norm_cast
  simp only [Real.abs_exp, Real.exp_lt_one_iff, Right.neg_neg_iff]
  apply mul_pos
  apply Real.two_pi_pos
  exact z.2

theorem summable_iter_derv' (k : ℕ) (y : ℍ') :
    Summable fun n : ℕ => (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * y) :=
  by
  apply summable_of_summable_norm
  simp
  have hv1 :
    ∀ b : ℕ,
      (b : ℝ) ^ k * Complex.abs (Complex.exp (2 * ↑π * I * y)) ^ (b : ℕ) =
        b ^ k * Complex.abs (Complex.exp (2 * ↑π * I * b * y)) :=
    by
    intro b
    rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
  simp_rw [mul_pow]
  have h2ne : (2 : ℝ) ^ k ≠ 0 := by apply pow_ne_zero; exact NeZero.ne 2
  simp_rw [mul_assoc]
  rw [summable_mul_left_iff h2ne]
  rw [summable_mul_left_iff _]
  simp_rw [← mul_assoc]
  apply Summable.congr _ hv1
  apply summable_pow_mul_geometric_of_norm_lt_1
  simp
  apply exp_upperHalfPlane_lt_one
  exact TopologicalSemiring.mk
  apply pow_ne_zero
  simpa using Real.pi_ne_zero

theorem summable_pow_mul_exp {k : ℕ} (z : ℍ) :
    Summable fun i : ℕ+ => Complex.abs (2 * ↑i ^ (k + 1) * exp (2 * ↑π * I * ↑z * ↑i)) :=
  by
  simp
  have h2ne : (2 : ℝ) ≠ 0 := NeZero.ne 2
  simp_rw [mul_assoc]
  rw [summable_mul_left_iff h2ne]
  simp_rw [← coe_coe]
  have hv1 :
    ∀ b : ℕ+,
      Complex.abs (Complex.exp (2 * ↑π * I * z * b)) =
        Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
    by
    intro b
    rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
  simp_rw [← mul_assoc]
  simp_rw [hv1]
  simp_rw [coe_coe]
  have lj :=
    nat_pos_tsum fun x : ℕ => (x : ℝ) ^ (k + 1) * Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ x
  simp at lj 
  rw [lj]
  apply summable_pow_mul_geometric_of_norm_lt_1
  simp
  apply exp_upperHalfPlane_lt_one

theorem exp_iter_deriv (n m : ℕ) :
    (iteratedDeriv n fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) = fun t =>
      (2 * ↑π * I * m) ^ n * Complex.exp (2 * ↑π * I * m * t) :=
  by
  induction' n with n IH
  simp
  funext x
  rw [iteratedDeriv_succ]
  rw [IH]
  simp
  ring

theorem iteratedDerivWithin_of_is_open (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) ℍ')
      (iteratedDeriv n fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) ℍ' :=
  by
  induction' n with n IH
  · intro x hx
    simp
  · intro x hx
    rw [iteratedDeriv_succ, iteratedDerivWithin_succ]
    dsimp
    rw [derivWithin_of_open upper_half_plane_isOpen]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [upper_half_plane_is_open.mem_nhds hx]
    apply IH
    exact hx
    apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen hx

theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) ℍ')
      (fun t => (2 * ↑π * I * m) ^ n * Complex.exp (2 * ↑π * I * m * t)) ℍ' :=
  by
  apply eq_on.trans (iteratedDerivWithin_of_is_open n m)
  rw [eq_on]
  intro x hx
  apply congr_fun (exp_iter_deriv n m)

theorem exp_iter_deriv_apply (n m : ℕ) (x : ℂ) :
    ((iteratedFDeriv ℂ n fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) x fun i : Fin n => 1) =
      (2 * ↑π * I * m) ^ n * Complex.exp (2 * ↑π * I * m * x) :=
  by apply congr_fun (exp_iter_deriv n m)

def uexp (n : ℕ) : ℍ' → ℂ := fun z => Complex.exp (2 * ↑π * I * z * n)

def funn (K : Set ℂ) (hk1 : K ⊆ upperHalfSpace) (hk2 : IsCompact K) : ContinuousMap K ℂ
    where toFun := fun r : K => Complex.exp (2 * ↑π * I * r)

def funnN (K : Set ℂ) (hk1 : K ⊆ upperHalfSpace) (hk2 : IsCompact K) (n k : ℕ) : ContinuousMap K ℂ
    where toFun := fun r : K => (2 * π * I * n) ^ k * Complex.exp (2 * ↑π * I * r)

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ↥upperHalfSpace) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) upperHalfSpace z)
      ↑r :=
  by
  simp at *
  have hh :
    DifferentiableOn ℂ (fun t => (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * t)) ℍ' := by
    apply Differentiable.differentiableOn; simp
  apply DifferentiableOn.differentiableAt
  apply DifferentiableOn.congr hh
  intro x hx
  apply exp_iter_deriv_within k n hx
  apply upper_half_plane_is_open.mem_nhds r.2

theorem der_iter_eq_der2 (k n : ℕ) (r : ↥upperHalfSpace) :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ') ℍ'
        ↑r :=
  by
  simp
  apply symm
  apply DifferentiableAt.derivWithin
  apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ↥upperHalfSpace) :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ') ↑r =
      iteratedDerivWithin (k + 1) (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ' ↑r :=
  by
  rw [der_iter_eq_der2 k n r]
  rw [iteratedDerivWithin_succ]
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem cray (n : ℕ) : 0 ≤ 2 * |π| * n :=
  by
  apply mul_nonneg
  apply mul_nonneg
  linarith
  simp
  apply Nat.cast_nonneg

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          Complex.abs
              (deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ') r) ≤
            u n :=
  by
  have : CompactSpace K := by rw [← isCompact_univ_iff]; rw [isCompact_iff_isCompact_univ] at hK2 ;
    apply hK2
  have hg := BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [funn]
    simp only [ContinuousMap.coe_mk, norm_eq_abs]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by simp only [norm_nonneg]
  have hu : Summable fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ (k + 1) * r ^ n) :=
    by
    simp
    simp_rw [mul_pow]
    have h2ne : (2 : ℝ) ^ (k + 1) ≠ 0 := by apply pow_ne_zero; exact NeZero.ne 2
    simp_rw [mul_assoc]
    rw [summable_mul_left_iff h2ne]
    rw [summable_mul_left_iff _]
    apply summable_pow_mul_geometric_of_norm_lt_1
    simp at *
    apply hr
    exact TopologicalSemiring.mk
    apply pow_ne_zero
    simpa using Real.pi_ne_zero
  refine' ⟨fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ (k + 1) * r ^ n), hu, _⟩
  intro n t
  have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
  simp at *
  simp_rw [go]
  have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
  simp only [Subtype.val_eq_coe, opens.coe_mk] at *
  rw [h1]
  simp
  have ineqe : Complex.abs (Complex.exp (2 * π * I * n * t)) ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      Complex.abs (Complex.exp (2 * π * I * n * t)) =
        Complex.abs (Complex.exp (2 * π * I * t)) ^ n :=
      by rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
    rw [hw1]
    apply le_of_pow'
    apply complex.abs.nonneg
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)) t
    simp at *
    exact this
  apply mul_le_mul
  simp
  simp at ineqe 
  convert ineqe
  apply complex.abs.nonneg
  apply pow_nonneg (cray n)

theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * Complex.abs (Complex.exp (2 * ↑π * I * n * r)) ≤ u n :=
  by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]; rw [isCompact_iff_isCompact_univ] at hK2 
    apply hK2
  have hg := BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [funn]
    simp only [ContinuousMap.coe_mk, norm_eq_abs]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by simp only [norm_nonneg]
  have hu : Summable fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ k * r ^ n) :=
    by
    simp only [AbsoluteValue.map_mul, Complex.abs_pow, Complex.abs_two, abs_of_real, abs_I, mul_one,
      abs_cast_nat, BoundedContinuousFunction.norm_mkOfCompact, abs_norm]
    simp_rw [mul_pow]
    have h2ne : (2 : ℝ) ^ k ≠ 0 := by apply pow_ne_zero; exact NeZero.ne 2
    simp_rw [mul_assoc]
    rw [summable_mul_left_iff h2ne]
    rw [summable_mul_left_iff _]
    apply summable_pow_mul_geometric_of_norm_lt_1
    simp only [norm_norm, BoundedContinuousFunction.norm_mkOfCompact, norm_nonneg, Ne.def] at *
    apply hr
    exact TopologicalSemiring.mk
    apply pow_ne_zero
    simpa using Real.pi_ne_zero
  refine' ⟨fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ k * r ^ n), hu, _⟩
  intro n t
  have ineqe : Complex.abs (Complex.exp (2 * π * I * n * t)) ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      Complex.abs (Complex.exp (2 * π * I * n * t)) =
        Complex.abs (Complex.exp (2 * π * I * t)) ^ n :=
      by rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
    rw [hw1]
    apply le_of_pow'
    apply complex.abs.nonneg
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (funn K hK1 hK2)) t
    simp only [norm_norm, BoundedContinuousFunction.norm_mkOfCompact, norm_nonneg,
      AbsoluteValue.map_mul, Complex.abs_pow, Complex.abs_two, abs_of_real, abs_I, mul_one,
      abs_cast_nat, BoundedContinuousFunction.mkOfCompact_apply, norm_eq_abs, abs_norm] at *
    exact this
  simp only [AbsoluteValue.map_mul, Complex.abs_pow, Complex.abs_two, abs_of_real, abs_I, mul_one,
    abs_cast_nat, BoundedContinuousFunction.norm_mkOfCompact, abs_norm]
  apply mul_le_mul
  simp only
  simp only [norm_norm, BoundedContinuousFunction.norm_mkOfCompact] at ineqe 
  convert ineqe
  apply complex.abs.nonneg
  apply pow_nonneg (cray n)

theorem exp_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ') :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ' x =
      ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ' x :=
  by
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero]
  rw [iteratedDerivWithin_succ]
  have HH :
    derivWithin (iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ') ℍ'
        x =
      derivWithin
        (fun z =>
          ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ' z)
        ℍ' x :=
    by
    apply derivWithin_congr
    intro y hy
    apply IH ⟨y, hy⟩
    apply IH x
  simp_rw [HH]
  rw [deriv_tsum_fun']
  simp only
  apply tsum_congr
  intro b
  rw [iteratedDerivWithin_succ]
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen x.2
  exact upper_half_plane_isOpen
  exact x.2
  intro y hy
  apply Summable.congr (summable_iter_derv' k ⟨y, hy⟩)
  intro b
  apply symm
  apply exp_iter_deriv_within k b hy
  intro K hK1 hK2
  simp only
  apply iter_deriv_comp_bound2 K hK1 hK2 k
  apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen x.2

theorem exp_series_ite_deriv_uexp'' (k : ℕ) (x : ℍ') :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ' x =
      ∑' n : ℕ, (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * x) :=
  by
  rw [exp_series_ite_deriv_uexp2 k x]
  apply tsum_congr
  intro b
  apply exp_iter_deriv_within k b x.2

theorem exp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ')
      (fun x : ℂ => ∑' n : ℕ, (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * x)) ℍ' :=
  by
  intro x hx
  apply exp_series_ite_deriv_uexp'' k ⟨x, hx⟩

theorem uexp_contDiffOn (k n : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => Complex.exp (2 * ↑π * I * n * z)) ℍ' :=
  by
  apply ContDiff.contDiffOn
  apply ContDiff.cexp
  apply ContDiff.mul
  apply contDiff_const
  apply contDiff_id

theorem tsum_uexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ' :=
  by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm
  apply DifferentiableOn.congr _ (exp_series_ite_deriv_uexp''' m)
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  apply hasDerivWithinAt_tsum_fun _ upper_half_plane_isOpen
  apply hx
  intro y hy
  apply summable_iter_derv' m ⟨y, hy⟩
  intro K hK1 hK2
  have := iter_deriv_comp_bound3 K hK1 hK2 (m + 1)
  obtain ⟨u, hu, hu2⟩ := this
  refine' ⟨u, hu, _⟩
  intro n r
  have HU2 := hu2 n r
  simp
  apply le_trans _ HU2
  apply le_of_eq
  ring
  intro n r
  apply Differentiable.differentiableAt
  simp only [Differentiable.mul, differentiable_const, Differentiable.cexp, differentiable_id']
  exact at_top_ne_bot

theorem iter_der_within_add (k : ℕ+) (x : ℍ') :
    iteratedDerivWithin k
        (fun z => ↑π * I - (2 * ↑π * I) • ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ' x =
      -(2 * ↑π * I) * ∑' n : ℕ, (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x) :=
  by
  rw [iter_der_within_const_neg k k.2 x]
  simp
  have :=
    iter_der_within_neg' k x fun z => (2 * ↑π * I) • ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)
  simp at this 
  rw [this]
  rw [neg_eq_neg_one_mul]
  have t2 :=
    iter_der_within_const_mul' k x (2 * ↑π * I) fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)
  simp at t2 
  rw [t2]
  simp
  have h3 := exp_series_ite_deriv_uexp'' k x
  simp at h3 
  left
  apply h3
  apply tsum_uexp_contDiffOn k
  have := ContDiffOn.const_smul (2 * ↑π * I) (tsum_uexp_contDiffOn k)
  simpa using this

