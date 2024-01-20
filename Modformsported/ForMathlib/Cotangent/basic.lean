/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as  described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.ExpSummableLemmas

noncomputable section

open Metric Filter Function Complex

open scoped Interval Real Topology BigOperators Nat Classical

local notation "ℍ" => UpperHalfPlane

def cot (z : ℂ) :=
  Complex.cos z / Complex.sin z

theorem cot_exp (z : ℂ) :
    cot (↑π * z) = (Complex.exp (2 * ↑π * I * z) + 1) / (I * (1 - Complex.exp (2 * ↑π * I * z))) :=
  by
  rw [cot, sin, cos]
  field_simp
  have h1 :
    exp (↑π * z * I) + exp (-(↑π * z * I)) = exp (-(↑π * z * I)) * (exp (2 * ↑π * z * I) + 1) :=
    by
    rw [mul_add]
    rw [← exp_add]
    simp
    apply congr_arg
    ring
  have h2 :
    (exp (-(↑π * z * I)) - exp (↑π * z * I)) * I =
      I * exp (-(↑π * z * I)) * (1 - exp (2 * ↑π * z * I)) :=
    by
    rw [mul_sub]
    simp_rw [mul_assoc]
    rw [← exp_add]
    ring_nf
  rw [h1, h2]
  have h22 :
    I * exp (-(↑π * z * I)) * (1 - exp (2 * ↑π * z * I)) =
      exp (-(↑π * z * I)) * (I * (1 - exp (2 * ↑π * z * I))) :=
    by ring
  rw [h22]
  rw [mul_div_mul_left]
  have h3 : Complex.exp (2 * ↑π * I * z) = Complex.exp (2 * ↑π * z * I) := by apply congr_arg; ring
  simp_rw [h3]
  apply exp_ne_zero

theorem div_one_sub_exp (z : ℍ) :
    1 / (1 - Complex.exp (2 * ↑π * I * z)) = ∑' n : ℕ, Complex.exp (2 * ↑π * I * z * n) :=
  by
  simp
  apply symm
  have h :
    ∑' n : ℕ, Complex.exp (2 * ↑π * I * z * n) = ∑' n : ℕ, Complex.exp (2 * ↑π * I * z) ^ n :=
    by
    apply tsum_congr
    intro b
    norm_cast
    rw [← exp_nat_mul]
    ring_nf
  rw [h]
  norm_cast
  apply tsum_geometric_of_norm_lt_1
  simpa using exp_upperHalfPlane_lt_one z

variable {R : Type _} [NormedRing R] [CompleteSpace R]

theorem geo_succ (x : R) (h : ‖x‖ < 1) : ∑' i : ℕ, x ^ (i + 1) = ∑' i : ℕ, x ^ i - 1 :=
  by
  apply symm
  rw [sub_eq_iff_eq_add]
  rw [tsum_eq_zero_add]
  simp only [pow_zero]
  apply add_comm
  apply NormedRing.summable_geometric_of_norm_lt_1 x h

theorem geom_series_mul_add (x : R) (h : ‖x‖ < 1) : x * ∑' i : ℕ, x ^ i = ∑' i : ℕ, x ^ (i + 1) :=
  by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).hasSum.mul_left x
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have :
    Tendsto (fun n : ℕ => ∑ i in Finset.range (n + 1), x ^ i - 1) atTop
      (𝓝 (∑' i : ℕ, x ^ (i + 1))) :=
    by
    have hj := geo_succ x h
    rw [hj]
    apply Tendsto.sub_const
    simp_rw [Finset.sum_range_succ]
    have hp : tsum (fun (i : ℕ)=> x^i) = tsum (fun (i : ℕ)=> x^i) + 0 := by simp
    rw [hp]
    apply Tendsto.add
    apply HasSum.tendsto_sum_nat
    apply Summable.hasSum
    apply NormedRing.summable_geometric_of_norm_lt_1 x h
    apply tendsto_pow_atTop_nhds_0_of_norm_lt_1 h
  convert ← this
  have hh := @geom_sum_succ _ _ x
  rw [hh]
  simp only [add_sub_cancel]
  rw [Finset.mul_sum]

theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : ℕ, x ^ i = 2 * ∑' i : ℕ, x ^ i - 1 :=
  by
  rw [add_mul]
  simp only [one_mul]
  rw [geom_series_mul_add x h]
  rw [geo_succ x h]
  rw [two_mul]
  abel

theorem pi_cot_q_exp (z : ℍ) :
    ↑π * cot (↑π * z) = ↑π * I - 2 * ↑π * I * ∑' n : ℕ, Complex.exp (2 * ↑π * I * z * n) :=
  by
  rw [cot_exp]
  have h1 :
    ↑π * ((exp (2 * ↑π * I * ↑z) + 1) / (I * (1 - exp (2 * ↑π * I * ↑z)))) =
      -↑π * I * ((exp (2 * ↑π * I * ↑z) + 1) * (1 / (1 - exp (2 * ↑π * I * ↑z)))) :=
    by
    rw [div_mul_eq_div_mul_one_div]
    simp
    ring
  rw [h1]
  rw [div_one_sub_exp z]
  rw [add_comm]
  have := geom_series_mul_one_add (Complex.exp (2 * π * I * (z : ℂ))) (exp_upperHalfPlane_lt_one _)
  have hh :
    ∑' n : ℕ, Complex.exp (2 * ↑π * I * z * n) = ∑' n : ℕ, Complex.exp (2 * ↑π * I * z) ^ n :=
    by
    apply tsum_congr
    intro b
    norm_cast
    rw [← exp_nat_mul]
    ring_nf
  rw [hh]
  norm_cast at *
  simp at *
  rw [this]
  ring
