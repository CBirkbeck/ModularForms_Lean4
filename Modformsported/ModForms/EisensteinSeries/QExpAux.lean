import Project.ModForms.EisensteinSeries.EisenIsHolo
import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Project.ModForms.Riemzeta
import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.Calculus.Series
import Project.ModForms.EisensteinSeries.CotIden
import Project.ModForms.EisensteinSeries.TsumLemmas
import Project.ModForms.EisensteinSeries.AuxpLemmas
import Project.ModForms.EisensteinSeries.ExpSummableLemmas

#align_import mod_forms.Eisenstein_Series.q_exp_aux

--import mod_forms.Eisenstein_Series.Eisenstein_series_q_expansions
--import mod_forms.Eisenstein_Series.Eisenstein_series_q_expansions
noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ'" => (⟨UpperHalfPlane.upperHalfSpace, upper_half_plane_isOpen⟩ : OpenSubs)

local notation "ℍ" => UpperHalfPlane

theorem iter_eqOn_cong (f g : ℂ → ℂ) (hfg : EqOn f g ℍ') (k : ℕ) :
    EqOn (iteratedDerivWithin k f ℍ') (iteratedDerivWithin k g ℍ') ℍ' :=
  by
  induction' k with k hk
  intro x hx
  simp
  apply hfg hx
  intro x hx
  rw [iteratedDerivWithin_succ]
  rw [iteratedDerivWithin_succ]
  apply derivWithin_congr
  intro y hy
  apply hk hy
  apply hk hx
  repeat'
    apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen
    exact hx

theorem iter_exp_eqOn (k : ℕ+) :
    EqOn
      (iteratedDerivWithin k
        (fun z => ↑π * I - (2 * ↑π * I) • ∑' n : ℕ, Complex.exp (2 * ↑π * I * n * z)) ℍ')
      (fun x : ℂ =>
        -(2 * ↑π * I) * ∑' n : ℕ, (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x))
      ℍ' :=
  by
  intro z hz
  apply iter_der_within_add k ⟨z, hz⟩

theorem pos_sum_eq (k : ℕ) (hk : 0 < k) :
    (fun x : ℂ =>
        -(2 * ↑π * I) * ∑' n : ℕ, (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x)) =
      fun x : ℂ =>
      -(2 * ↑π * I) * ∑' n : ℕ+, (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x) :=
  by
  ext1
  simp
  left
  apply symm
  have := tsum_pNat fun n : ℕ => (2 * ↑π * I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * n * x)
  simp at this 
  apply this hk

theorem series_eql' (z : ℍ) :
    ↑π * I - 2 * ↑π * I * ∑' n : ℕ, Complex.exp (2 * ↑π * I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)) :=
  by
  rw [← pi_cot_q_exp z]
  have h := cot_series_rep z
  rw [sub_eq_iff_eq_add'] at h 
  exact h

theorem q_exp_iden'' (k : ℕ) (hk : 3 ≤ k) :
    EqOn (fun z : ℂ => (-1 : ℂ) ^ (k - 1) * (k - 1)! * ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k)
      (fun z : ℂ =>
        -(2 * ↑π * I) * ∑' n : ℕ+, (2 * ↑π * I * n) ^ (k - 1) * Complex.exp (2 * ↑π * I * n * z))
      ℍ' :=
  by
  have := (aux_iter_der_tsum_eqOn k hk).symm
  apply eq_on.trans this
  have hkpos : 0 < k - 1 := by
    apply Nat.sub_pos_of_lt
    linarith
  have h2 := (iter_exp_eqOn (⟨k - 1, hkpos⟩ : ℕ+)).symm
  simp only [one_div, coe_coe, Subtype.coe_mk, neg_mul, Algebra.id.smul_eq_mul] at *
  have h3 := pos_sum_eq (k - 1) hkpos
  simp at h3 
  rw [h3] at h2 
  apply eq_on.symm
  apply eq_on.trans h2
  apply iter_eqOn_cong
  intro z hz
  have H := series_eql' ⟨z, hz⟩
  simp only [Pi.add_apply, tsub_pos_iff_lt, Subtype.coe_mk, one_div, coe_coe] at *
  convert H
  ext1
  apply congr_arg
  ring

theorem exp_comm (n : ℕ) (z : ℍ') : exp (2 * ↑π * I * ↑z * n) = exp (2 * ↑π * I * n * z) :=
  by
  apply congr_arg
  ring

theorem q_exp_iden (k : ℕ) (hk : 3 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * I) ^ k / (k - 1)! * ∑' n : ℕ+, n ^ (k - 1) * Complex.exp (2 * ↑π * I * z * n) :=
  by
  have := q_exp_iden'' k hk z.2
  simp only [one_div, neg_mul, coe_coe, Subtype.val_eq_coe] at *
  have hk2 : (-1 : ℂ) ^ (k - 1) * (k - 1)! ≠ 0 := by
    simp only [Nat.factorial_ne_zero, Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero,
      not_false_iff]
  rw [← mul_right_inj' hk2]
  rw [this]
  have h3 : (-1) ^ (k - 1) * ↑(k - 1)! * ((-(2 * ↑π * I)) ^ k / ↑(k - 1)!) = -(2 * ↑π * I) ^ k :=
    by
    rw [mul_div]; rw [div_eq_mul_one_div]; rw [div_eq_inv_mul]; simp_rw [← mul_assoc];
    nth_rw 2 [neg_pow]
    ring_nf; nth_rw 2 [mul_comm]; simp_rw [← mul_assoc]; rw [mul_inv_cancel]; simp
    have hf : (-1 : ℂ) ^ k * (-1) ^ (k - 1) = -1 :=
      by
      rw [← pow_add]
      have hkk : k + (k - 1) = 2 * k - 1 :=
        by
        rw [← Nat.add_sub_assoc]
        rw [two_mul]
        linarith
      rw [hkk]
      apply Odd.neg_one_pow
      apply Nat.Even.sub_odd
      nlinarith
      rw [Nat.even_mul]
      left
      exact even_two
      exact odd_one
    rw [mul_assoc]
    rw [hf]
    ring
    norm_cast
    apply Nat.factorial_ne_zero
  rw [← mul_assoc]
  rw [h3]
  have hee :
    ∑' n : ℕ+, (2 * ↑π * I * ((n : ℕ) : ℂ)) ^ (k - 1) * exp (2 * ↑π * I * ((n : ℕ) : ℂ) * ↑z) =
      (2 * ↑π * I) ^ (k - 1) * ∑' n : ℕ+, n ^ (k - 1) * exp (2 * ↑π * I * ↑z * n) :=
    by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro b
    rw [← mul_assoc]
    rw [← mul_pow]
    simp only [coe_coe, mul_eq_mul_left_iff]
    left
    exact (exp_comm b z).symm
  rw [hee]
  rw [← mul_assoc]
  have he2 : 2 * ↑π * I * (2 * ↑π * I) ^ (k - 1) = (2 * ↑π * I) ^ k :=
    by
    have hke : k = 1 + (k - 1) := by
      apply symm; apply Nat.add_sub_of_le
      linarith
    nth_rw 2 [hke]
    rw [pow_add]
    simp
  rw [he2]
  simp

