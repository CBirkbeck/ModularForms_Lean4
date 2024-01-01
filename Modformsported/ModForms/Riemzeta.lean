import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real


universe u v

open Complex

open scoped BigOperators

noncomputable section

/-! ### Riemann zeta function -/


def rie (k : ℝ) : ℕ → ℝ := fun x => 1 / (x : ℝ) ^ k

/-- The `Riemann zeta function` defined on the real numbers.
It is defined as the infinite sum of the reciprocals of the naturals to the power `k`. We check it is summable at the end for real `k` greater than 1.-/
def rZ (k : ℝ) : ℝ :=
  ∑' x : ℕ, rie k x

theorem RZ_is_summmable (k : ℝ) (h : 1 < k) : Summable (rie k) := by
  have := Real.summable_nat_rpow_inv.2 h
  convert this
  simp [rie]


theorem int_RZ_is_summmable (k : ℤ) (h : 1 < k) : Summable (rie k) := by
  apply RZ_is_summmable
  norm_cast

theorem rZ_pos (k : ℝ) (h : 1 < k) : 0 < rZ k :=
  by
  rw [rZ]
  apply tsum_pos (RZ_is_summmable k h) _ 1
  rw [rie]
  simp
  intro b
  simp_rw [rie]
  simp
  apply Real.rpow_nonneg_of_nonneg
  norm_cast
  linarith
