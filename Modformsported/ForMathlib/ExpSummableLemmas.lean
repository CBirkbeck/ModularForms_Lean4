import Modformsported.ForMathlib.ModForms2
import Modformsported.ForMathlib.TsumLemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousFunction.Compact

noncomputable section

open ModularForm  UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

--local notation "ℍ" => UpperHalfPlane

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

theorem exp_upperHalfPlane_lt_one (z : ℍ) : Complex.abs (Complex.exp (2 * ↑π * I * z)) < 1 := by
  simp only [abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
    mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, coe_re, coe_im, zero_sub,
    Real.exp_lt_one_iff, neg_neg_iff_pos]
  positivity

theorem summable_iter_derv' (k : ℕ) (y : ℍ') :
    Summable fun n : ℕ => (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * y) :=
  by
  apply Summable.of_norm
  simp only [Opens.coe_mk, norm_mul, norm_pow, IsROrC.norm_ofNat, norm_eq_abs, abs_ofReal, abs_I,
    mul_one, norm_nat, abs_natCast, mul_pow]
  simp_rw [mul_assoc]
  rw [summable_mul_left_iff (pow_ne_zero _ two_ne_zero)]
  rw [summable_mul_left_iff (pow_ne_zero _ (abs_ne_zero.mpr Real.pi_ne_zero))]
  simp_rw [← mul_assoc]
  have : Summable fun n : ℕ => (n : ℝ) ^ k * Complex.abs (Complex.exp (2 * ↑π * I * y)) ^ n := by
    apply summable_pow_mul_geometric_of_norm_lt_1
    simp only [Real.norm_eq_abs, Complex.abs_abs]
    apply exp_upperHalfPlane_lt_one
  apply this.congr
  intro n
  rw [← Complex.abs_pow, one_pow, one_mul, ← exp_nat_mul]
  ring_nf

theorem summable_pow_mul_exp {k : ℕ} (z : ℍ) :
    Summable fun i : ℕ+ => Complex.abs (2 * ↑i ^ (k + 1) * exp (2 * ↑π * I * ↑z * ↑i)) :=
  by
  simp
  have h2ne : (2 : ℝ) ≠ 0 := NeZero.ne 2
  simp_rw [mul_assoc]
  rw [summable_mul_left_iff h2ne]
  have hv1 :
    ∀ b : ℕ+,
      Complex.abs (Complex.exp (2 * ↑π * I * z * b)) =
        Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
    by
    intro b
    norm_cast
    rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
  simp_rw [← mul_assoc]
  simp_rw [hv1]
  have lj :=
    nat_pos_tsum2 fun x : ℕ => (x : ℝ) ^ (k + 1) * Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ x
  norm_cast at *
  simp only [PNat.pow_coe, Nat.cast_pow, map_pow, abs_natCast, ofReal_mul, ofReal_ofNat] at *
  rw [lj ]
  apply summable_pow_mul_geometric_of_norm_lt_1
  simp
  apply exp_upperHalfPlane_lt_one
  simp

section
variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {F : Type u_2}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)

theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  unfold iteratedDerivWithin iteratedDeriv
  intro x hx
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := 𝕜) (F := F) (E := 𝕜) (f := f) n hs hx]
end

theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) ℍ')
      (fun t => (2 * ↑π * I * m) ^ n * Complex.exp (2 * ↑π * I * m * t)) ℍ' :=
  by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen _ _ _ upper_half_plane_isOpen)
  rw [EqOn]
  intro x _
  apply congr_fun (iteratedDeriv_cexp_const_mul ..)

theorem exp_iter_deriv_apply (n m : ℕ) (x : ℂ) :
    ((iteratedFDeriv ℂ n fun s : ℂ => Complex.exp (2 * ↑π * I * m * s)) x fun i : Fin n => 1) =
      (2 * ↑π * I * m) ^ n * Complex.exp (2 * ↑π * I * m * x) :=
  by apply congr_fun (iteratedDeriv_cexp_const_mul ..)

def uexp (n : ℕ) : ℍ' → ℂ := fun z => Complex.exp (2 * ↑π * I * z * n)

def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * I * r)

/-
def funnN (K : Set ℂ) (n k : ℕ) : ContinuousMap K ℂ
    where toFun := fun r : K => (2 * π * I * n) ^ k * Complex.exp (2 * ↑π * I * r)
-/

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ↥upperHalfSpace) :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) upperHalfSpace z) ↑r :=
  by
  have hh :
    DifferentiableOn ℂ (fun t => (2 * ↑π * I * n) ^ k * Complex.exp (2 * ↑π * I * n * t)) ℍ' := by
    apply Differentiable.differentiableOn;
    apply Differentiable.const_mul
    apply Differentiable.cexp
    apply Differentiable.const_mul
    apply differentiable_id
  apply DifferentiableOn.differentiableAt
  apply DifferentiableOn.congr hh
  intro x hx
  apply exp_iter_deriv_within k n hx
  apply upper_half_plane_isOpen.mem_nhds r.2


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

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          Complex.abs
              (deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * I * n * s)) ℍ') r) ≤
            u n :=
  by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]
    rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk, norm_eq_abs]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by simp only [norm_nonneg]
  have hu : Summable fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ (k + 1) * r ^ n) :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k+1))* ((n) ^ (k + 1) *Complex.abs (r ^ n)) =
      Complex.abs ((2 * ↑π * I * n) ^ (k + 1) * r ^ n) := by
        intro n
        rw [←mul_assoc]
        norm_cast
        simp only [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow, abs_ofReal,
          abs_norm, map_mul, mul_eq_mul_right_iff]
        constructor
        norm_cast
        simp only [Nat.cast_pow, ofReal_mul, ofReal_ofNat, map_pow, map_mul, Complex.abs_two, abs_ofReal, abs_I,
          mul_one, abs_natCast]
        have hh : |2 * π| =2 * π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]

    simp only [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow, abs_ofReal, abs_norm]
    apply summable_pow_mul_geometric_of_norm_lt_1
    simp only [norm_norm]
    apply hr
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  refine' ⟨fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ (k + 1) * r ^ n), hu, _⟩
  intro n t
  have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
  simp at *
  simp_rw [go]
  have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
  norm_cast at *
  simp at *
  rw [h1]
  simp
  have ineqe : Complex.abs (Complex.exp (2 * π * I * n * t)) ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      Complex.abs (Complex.exp (2 * π * I * n * t)) =
        Complex.abs (Complex.exp (2 * π * I * t)) ^ n := by
          norm_cast
          rw [← Complex.abs_pow];
          congr;
          rw [← exp_nat_mul];
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left
    apply Complex.abs.nonneg
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    simp at *
    exact this
  apply mul_le_mul
  simp
  simp at ineqe
  convert ineqe
  apply Complex.abs.nonneg
  positivity

theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * Complex.abs (Complex.exp (2 * ↑π * I * n * r)) ≤ u n :=
  by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]; rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk, norm_eq_abs]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by simp only [norm_nonneg]
  have hu : Summable fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ (k ) * r ^ n) :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k))* ((n) ^ (k ) *Complex.abs (r ^ n)) =
      Complex.abs ((2 * ↑π * I * n) ^ (k ) * r ^ n) := by
        intro n
        rw [←mul_assoc]
        norm_cast
        simp only [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow, abs_ofReal,
          abs_norm, map_mul, mul_eq_mul_right_iff]
        constructor
        norm_cast
        simp only [Nat.cast_pow, ofReal_mul, ofReal_ofNat, map_pow, map_mul, Complex.abs_two, abs_ofReal, abs_I,
          mul_one, abs_natCast]
        have hh : |2 *π| = 2 * π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]

    simp only [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow, abs_ofReal, abs_norm]
    apply summable_pow_mul_geometric_of_norm_lt_1
    simp only [norm_norm]
    apply hr
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  refine' ⟨fun n : ℕ => Complex.abs ((2 * ↑π * I * n) ^ k * r ^ n), hu, _⟩
  intro n t
  have ineqe : Complex.abs (Complex.exp (2 * π * I * n * t)) ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      Complex.abs (Complex.exp (2 * π * I * n * t)) =
        Complex.abs (Complex.exp (2 * π * I * t)) ^ n := by
        norm_cast
        rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left
    apply Complex.abs.nonneg
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    simp  [norm_norm, BoundedContinuousFunction.norm_mkOfCompact, norm_nonneg,
      AbsoluteValue.map_mul, Complex.abs_pow, Complex.abs_two,  abs_I, mul_one,
      abs_natCast, BoundedContinuousFunction.mkOfCompact_apply, norm_eq_abs, abs_norm] at *
    exact this
  simp [AbsoluteValue.map_mul, Complex.abs_pow, Complex.abs_two,  abs_I, mul_one,
    abs_natCast, BoundedContinuousFunction.norm_mkOfCompact, abs_norm]
  apply mul_le_mul
  rfl
  simp only [norm_norm, BoundedContinuousFunction.norm_mkOfCompact] at ineqe
  convert ineqe
  norm_cast
  apply Complex.abs.nonneg
  positivity

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
  intro m _
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
  simp only [deriv_const_mul_field', map_mul, map_pow, Complex.abs_two, abs_ofReal,
    abs_I, mul_one,abs_natCast, ge_iff_le]
  apply le_trans _ HU2
  apply le_of_eq
  norm_cast
  rw [deriv_cexp]
  rw [deriv_const_mul]
  simp only [ofReal_mul, ofReal_ofNat, deriv_id'', mul_one, map_mul, Complex.abs_two, abs_ofReal,
    abs_I, abs_natCast]
  ring
  apply differentiable_id.differentiableAt
  apply Differentiable.differentiableAt
  apply Differentiable.const_mul
  apply differentiable_id'
  intro n r
  apply Differentiable.differentiableAt
  apply Differentiable.mul
  apply Differentiable.pow
  apply differentiable_const
  apply Differentiable.cexp
  apply differentiable_id'.const_mul



theorem iter_der_within_add (k : ℕ+) (x : ℍ') :
    iteratedDerivWithin k
        (fun z => ↑π * I - (2 * ↑π * I) • ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ' x =
      -(2 * ↑π * I) * ∑' n : ℕ, (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x) :=
  by
  have := iteratedDerivWithin_const_neg x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn k.2 (↑π * I)
    (f := fun z => (2 * ↑π * I) • ∑' (n : ℕ), cexp (2 * ↑π * I * ↑n * z))
  erw [this]
  simp
  have :=
    iteratedDerivWithin_neg' x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn (n := k)
      (f := fun z => (2 * ↑π * I) • ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z))
  simp at this
  erw [this]
  · rw [neg_eq_neg_one_mul]
    have t2 :=
      iteratedDerivWithin_const_mul x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn (n := k)
        (2 * ↑π * I) (f := fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z))
    simp at t2
    rw [t2]
    · simp
      have h3 := exp_series_ite_deriv_uexp'' k x
      simp at h3
      left
      apply h3
    · apply tsum_uexp_contDiffOn k
  · have := ContDiffOn.const_smul (2 * ↑π * I) (tsum_uexp_contDiffOn k)
    simpa using this
