import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Modformsported.ForMathlib.EisensteinSeries.bounds

noncomputable section

open Complex

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries

/-- Auxilary function used for bounding Eisentein series-/
def lowerBound1 (z : ℍ) : ℝ :=
  ((z.1.2 ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)))

theorem lowerBound1_pos (z : ℍ) : 0 < lowerBound1 z := by
  rw [lowerBound1]
  have H1 := upper_half_im_pow_pos z 2
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ))  := by
    norm_cast
    apply_rules [pow_pos, add_pos_of_nonneg_of_pos, pow_two_nonneg]
  have := div_pos H1 H2
  norm_cast at *

/-- This function is used to give an upper bound on Eisenstein series-/
def r (z : ℍ) : ℝ :=
  min (Real.sqrt (z.1.2 ^ (2))) (Real.sqrt (lowerBound1 z))

theorem r_pos (z : ℍ) : 0 < r z :=
  by
  have H := z.property; simp at H
  rw [r]
  simp only [lt_min_iff, Real.sqrt_pos, UpperHalfPlane.coe_im]
  constructor
  have := upper_half_im_pow_pos z 2
  norm_cast at *
  apply lowerBound1_pos

theorem r_ne_zero (z : ℍ) :  r z ≠ 0 := ne_of_gt (r_pos z)

lemma r_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ)  (hn : 1 ≤ n) :
  0 < (Complex.abs ((r z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  apply Complex.abs.pos
  apply mul_ne_zero
  norm_cast
  apply pow_ne_zero
  apply r_ne_zero
  norm_cast
  apply pow_ne_zero
  linarith

lemma pow_two_of_nonzero_ge_one (a : ℤ) (ha : a  ≠ 0) : 0 ≤ a^2 - 1  := by
  simp only [sub_nonneg, one_le_sq_iff_one_le_abs, ge_iff_le]
  exact Int.one_le_abs ha

theorem lowbound_ (z : ℍ) (δ : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (z.1.2 ^ 2 ) / (z.1.1 ^ 2 + z.1.2 ^ 2) ≤
      (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 := by
  have H1 : (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 =
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1 + n^2 := by
    ring
  have H4 :
    (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
      n * 2 * δ * z.1.1   +
        n^2) * (z.1.1 ^ 2 + z.1.2 ^ 2) -
    (z.1.2 ^ 2) =
      (δ * (z.1.1 ^ 2 + z.1.2 ^ 2)+ n * z.1.1)^2 + (n^2-1)* (z.1.2)^2 := by
     norm_num
     ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  apply add_nonneg
  apply pow_two_nonneg
  apply mul_nonneg
  norm_cast
  apply pow_two_of_nonzero_ge_one n hn
  apply pow_two_nonneg
  apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, upper_half_im_pow_pos z 2]

theorem auxlem1 (z : ℍ) (δ : ℝ) : r z ≤ Complex.abs ((z : ℂ) + δ)  := by
    rw [r]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt ((z : ℂ).im ^ 2) ≤
        Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) :=
      by
      rw [Real.sqrt_le_sqrt_iff]
      norm_cast
      nlinarith; nlinarith
    simp at *
    left
    norm_cast
    rw [normSq_apply]
    simp
    norm_cast at *

theorem auxlem2_ (z : ℍ) (δ : ℝ) (n : ℤ) (h : n ≠ 0) : r z ≤ Complex.abs (δ * (z : ℂ) + n) := by
  rw [r]
  rw [Complex.abs]
  simp
  have H1 :
    Real.sqrt (lowerBound1 z) ≤
      Real.sqrt
        ((δ * (z : ℂ).re + n) * (δ * (z : ℂ).re + n) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
    by
    rw [lowerBound1]
    rw [Real.sqrt_le_sqrt_iff]
    have := lowbound_ z δ n h
    rw [← pow_two]
    rw [← pow_two]
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at *
    norm_cast at *
    nlinarith
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1
  rw [normSq_apply]
  right
  simp at *
  norm_cast

theorem baux_ (a : ℝ) (k : ℤ) (hk : 0 ≤ k) (b : ℂ) (h : 0 ≤ a) (h2 : a ≤ Complex.abs b) :
    a ^ k ≤ Complex.abs (b ^ k) := by
  lift k to ℕ using hk
  norm_cast at *
  simp only [Complex.cpow_int_cast, map_pow]
  norm_cast at *
  apply pow_le_pow_left h h2

theorem baux2_ (z : ℍ) (k : ℤ) : Complex.abs (r z ^ k) = r z ^ k := by
  have ha := (r_pos z).le
  have := Complex.abs_of_nonneg ha
  rw [←this]
  simp  [abs_ofReal, cpow_nat_cast, map_pow, _root_.abs_abs, Real.rpow_nat_cast]

theorem auxlem3_ (z : ℍ) (x : ℤ × ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((r z : ℂ) ^ k) ≤ Complex.abs (((z : ℂ) + (x.2 : ℂ) / (x.1 : ℂ)) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (r z ^ k) = r z ^ k := by apply baux2_
  norm_cast at H1
  rw [H1]
  have := auxlem1 z (x.2 / x.1 : ℝ)
  norm_cast at this
  lift k to ℕ using hk
  norm_cast at *
  simp only [Complex.cpow_int_cast, map_pow]
  simp
  norm_cast at *
  apply pow_le_pow_left (r_pos _).le
  simp at *
  convert this




theorem auxlem4 (z : ℍ) (x : ℤ × ℤ) (k : ℤ) (hk : 0 ≤ k) :
    Complex.abs ((r z : ℂ) ^ k) ≤ Complex.abs (((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (r z ^ k) = r z ^ k := by apply baux2_
  norm_cast at H1
  rw [H1]
  have := auxlem2_ z (x.1 / x.2 : ℝ) 1 one_ne_zero
  norm_cast at this
  lift k to ℕ using hk
  norm_cast at *
  simp only [Complex.cpow_int_cast, map_pow]
  simp
  norm_cast at *
  apply pow_le_pow_left (r_pos _).le
  simp at *
  convert this
