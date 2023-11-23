/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Modformsported.ModForms.Riemzeta
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.Calculus.Series
import Modformsported.ForMathlib.TsumLemmas
import Modformsported.ForMathlib.IteratedDerivLemmas
import Modformsported.ForMathlib.ExpSummableLemmas
import Modformsported.ForMathlib.AuxpLemmas
import Modformsported.ForMathlib.Cotangent.CotangentIdentity
import Modformsported.ForMathlib.QExpAux
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.NumberTheory.ArithmeticFunction



noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open Nat.ArithmeticFunction

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)


def eisensteinSeriesOfWt_ (k : ℤ) :=
  if h : 3 ≤ k then EisensteinSeriesModularForm k h else 0

local notation "G[" k "]" => eisensteinSeriesOfWt_ k

/-
def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6
-/
open scoped DirectSum BigOperators

--local notation "ℍ" => UpperHalfPlane

theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta (k)) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k :=
  by
  have hkk : 1 < (k ) := by
    linarith
  rw [tsum_prod, sum_int_even]
  · simp  [algebraMap.coe_zero, MulZeroClass.zero_mul, zero_add, one_div,
      Int.cast_ofNat, add_left_inj]

    rw [sum_int_even]
    simp  [algebraMap.coe_zero, Int.cast_ofNat, Real.rpow_nat_cast, one_div]
    have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by convert inv_zero; norm_cast; apply zero_pow'; linarith
    have h00 : ((0 ^ k : ℕ) : ℝ)⁻¹ = 0 := by convert inv_zero; norm_cast; apply zero_pow'; linarith
    norm_cast at *
    rw [h0]
    simp only [zero_add, mul_eq_mul_left_iff, bit0_eq_zero, one_ne_zero, or_false_iff]
    norm_cast
    simp
    rw [zeta_nat_eq_tsum_of_gt_one hkk, ← tsum_pNat]
    apply tsum_congr
    intro b
    norm_cast
    simp
    simp
    linarith
    intro n
    apply congr_arg
    apply symm
    norm_cast
    apply Even.neg_pow hk2
    simp
    have :=Complex.summable_nat_pow_inv.2  hkk
    simpa using this
  · intro n
    simp only [one_div, Int.cast_neg, neg_mul]
    apply symm
    rw [int_sum_neg]
    congr
    funext d
    simp only [Int.cast_neg, inv_inj]
    ring_nf
    convert Even.neg_pow hk2 ((z : ℂ) * n + d)
    norm_cast
    ring
    norm_cast
    ring
  have hkz : 3 ≤ (k : ℤ) := by linarith
  · apply prod_sum _ (Eisenstein_tsum_summable k z hkz)
  have hkz : 3 ≤ (k : ℤ) := by linarith
  · apply Eisenstein_tsum_summable k z hkz

theorem sigma_eq_sum_div' (k n : ℕ) : sigma k n = ∑ d : ℕ in Nat.divisors n, (n / d) ^ k :=
  by
  simp [sigma]
  rw [← Nat.sum_div_divisors]

theorem eisen_iden (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z = Eisenstein_tsum k z :=
  by
  simp_rw [eisensteinSeriesOfWt_]
  simp only [hk, dif_pos]
  rw [EisensteinSeriesModularForm]
  simp_rw [Eisenstein_SIF]
  rfl

instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2

/-
instance natPosMul :  MulAction ℕ+ ℍ where
  one_smul z := by

  mul_smul z x := by sorry


  mul_smul x y z := Subtype.ext <| mul_smul (x : ℝ) y (z : ℂ)



  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2
  one_smul z := by

  mul_smul x y z := by
    dsimp; simp; simp_rw [← mul_assoc]
-/


theorem natPosSMul_apply (c : ℕ+) (z : ℍ) : ((c  • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := by rfl

theorem aux_inequality_one (a b k : ℕ) (hb : 0 < b) (h : a ≤ b) : a ^ k ≤ 2 * b ^ (k + 1) :=
  by
  have h1 : a ^ k ≤ b ^ k := pow_mono_right k h
  apply le_trans h1
  have h2 : b ^ k ≤ b ^ (k + 1) := by apply Nat.pow_le_pow_of_le_right hb; linarith
  apply le_trans h2
  apply le_mul_of_one_le_left
  apply pow_nonneg
  simp only [zero_le']
  linarith

theorem aux_inequality_two (z : ℍ) (k : ℕ) (n : Σ x : ℕ+, Nat.divisorsAntidiagonal x) :
    ‖(n.2.1.1 : ℂ) ^ k * Complex.exp (2 * ↑π * I * z * n.2.1.1 * n.2.1.2)‖ ≤
      Complex.abs (2 * n.1 ^ (k + 1) * Complex.exp (2 * ↑π * I * z * n.1)) :=
  by
  simp [ norm_eq_abs, AbsoluteValue.map_mul, Complex.abs_pow, abs_cast_nat, Complex.abs_two]
  have hn := n.2.2
  simp only [Nat.mem_divisorsAntidiagonal, Ne.def, PNat.ne_zero, not_false_iff,
    and_true_iff] at *
  norm_cast
  simp_rw [← hn]
  have gt : ∀ a b : ℕ, ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := Nat.cast_mul
  rw [gt]
  rw [← mul_assoc]
  simp  [Nat.cast_pow, ofReal_mul, PNat.pow_coe, Nat.cast_mul, algebraMap.coe_one]
  rw [mul_le_mul_right _]
  have J := Nat.fst_mem_divisors_of_mem_antidiagonal n.2.2
  simp only [Nat.mem_divisors, Ne.def, PNat.ne_zero, not_false_iff,
    and_true_iff] at J
  have J2 := Nat.le_of_dvd ?_ J
  norm_cast
  apply aux_inequality_one
  apply n.1.2
  exact J2
  apply n.1.2
  simp only [AbsoluteValue.pos_iff, Ne.def]
  apply Complex.exp_ne_zero



theorem anti_diag_card_le (n : ℕ+) : (Nat.divisorsAntidiagonal n).card ≤ n ^ 2 :=
  by
  classical!
  simp_rw [Nat.divisorsAntidiagonal]
  have H := Finset.card_filter_le (Finset.Ico 1 (n + 1 : ℕ) ×ˢ Finset.Ico 1 (n + 1 : ℕ))
    ((fun (x : ℕ × ℕ) => x.fst * x.snd = n))
  norm_cast at *
  simp at *
  rw [pow_two]
  convert H

theorem summable1 {k : ℕ} (z : ℍ) :
    Summable fun p : Σ b : ℕ+, ↥(Nat.divisorsAntidiagonal b) =>
      ((sigmaAntidiagonalEquivProd p).fst : ℂ) ^ k *
        exp
          (2 * ↑π * I * ↑z * (sigmaAntidiagonalEquivProd p).fst *
            (sigmaAntidiagonalEquivProd p).snd) :=
  by
  have := summable_of_norm_bounded _ ?_ (aux_inequality_two z k)
  apply this
  rw [summable_sigma_of_nonneg]
  constructor
  apply fun n => (hasSum_fintype _).summable
  simp only [ AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_cast_nat]
  apply summable_of_nonneg_of_le _ _ (@summable_pow_mul_exp (k + 2) z)
  intro x
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  norm_cast
  apply mul_nonneg
  exact (Nat.divisorsAntidiagonal x).card.cast_nonneg
  apply mul_nonneg
  simp [Nat.cast_mul, algebraMap.coe_one, zero_le_mul_right, Nat.cast_pos,
    PNat.pos, zero_le_bit0, zero_le_one]
  apply Complex.abs.nonneg
  intro b
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul,
    AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_cast_nat]
  have hk :
    2 * (b : ℝ) ^ (k + 2 + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b)) =
      b ^ 2 * (2 * b ^ (k + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b))) :=
    by
    norm_cast
    simp
    ring
  norm_cast at *
  simp at *
  rw [hk]
  have ht := anti_diag_card_le b
  refine' mul_le_mul _ _ _ _
  norm_cast
  simp
  simp
  nlinarith
  intro x
  apply Complex.abs.nonneg

theorem sum_sigma_fn_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * I * z * c.1 * c.2) =
      ∑' e : ℕ+,
        ∑ x : Nat.divisorsAntidiagonal e,
          x.1.1 ^ k * Complex.exp (2 * ↑π * I * z * x.1.1 * x.1.2) :=
  by
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [tsum_sigma']
  congr
  funext
  rw [tsum_fintype]
  congr
  apply fun n => (hasSum_fintype _).summable
  apply summable1


theorem div_mul_aux (k : ℕ) (z : ℍ) (n : ℕ) :
    ∑ x : ℕ in n.divisors, ↑(n / x) ^ k * exp (2 * (↑π * (I * (↑z * (↑(n / x) * ↑x))))) =
      ∑ x : ℕ in n.divisors, ↑(n / x) ^ k * exp (2 * (↑π * (I * (↑z * n)))) :=
  by
  apply Finset.sum_congr
  rfl
  funext
  intro x hx
  congr
  norm_cast
  apply Nat.div_mul_cancel
  rw [Nat.mem_divisors] at hx
  exact hx.1

theorem tsum_sigma_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * I * z * e) :=
  by
  simp_rw [sigma_eq_sum_div',sum_sigma_fn_eq z]
  apply tsum_congr
  intro n
  have :=
    @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
      (x : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * z * x * y)) n
  simp only [Finset.univ_eq_attach, cpow_nat_cast, EisensteinSeries.uhc, Nat.cast_sum, Nat.cast_pow,
    Nat.isUnit_iff] at *
  simp_rw [mul_assoc] at *
  norm_cast at *
  simp at *
  have dma := div_mul_aux k z n
  simp only [Nat.isUnit_iff, cpow_nat_cast, EisensteinSeries.uhc] at dma
  rw [dma] at this
  have hr :
    (∑ x : ℕ in (n : ℕ).divisors, ↑(↑n / x) ^ k) * exp (2 * (↑π * (I * (↑z * ↑n)))) =
      ∑ x : ℕ in (n : ℕ).divisors, ↑(↑n / x) ^ k * exp (2 * (↑π * (I * (↑z * (n : ℕ))))) :=
    by
    simp
    apply Finset.sum_mul
  simp at *
  rw [hr, ← this, ←(sumaux _)]
  simp only [Finset.univ_eq_attach]


theorem a1 {k : ℕ} (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * ↑z * e * c) :=
  by
  have h2ne : (e : ℂ) ^ (k - 1) ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, PNat.ne_zero, false_and, not_false_eq_true]
  rw [summable_mul_left_iff h2ne]
  have hv1 :
    ∀ b : ℕ+, Complex.exp (2 * ↑π * I * z * e * b) = Complex.exp (2 * ↑π * I * z * e) ^ (b : ℕ) :=
    by
    intro b
    simp
    rw [← exp_nat_mul]; ring_nf
  simp_rw [hv1]
  have HH :  Complex.abs ( Complex.exp (2 * ↑π * I * z * e) ) < 1 := by
    have hv2 :
      ∀ b : ℕ+,
        Complex.abs (Complex.exp (2 * ↑π * I * z * b)) =
          Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
      by
      intro b
      norm_cast
      rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
    rw [hv2 e]
    norm_cast
    apply pow_lt_one
    apply Complex.abs.nonneg
    apply exp_upperHalfPlane_lt_one
    simp
  simp only [Ne.def, PNat.ne_zero, not_false_iff]
  rw [←norm_eq_abs] at HH
  rw  [← summable_geometric_iff_norm_lt_1] at HH
  simp only [EisensteinSeries.uhc, cpow_nat_cast] at *
  apply HH.subtype

theorem a2 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * c * ↑z * e) :=
  by
  have := @a1 k e z
  apply this.congr
  intro b
  ring_nf

theorem a3 {k : ℕ} (h : 2 ≤ k) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ (k - 1) * exp (2 * ↑π * I * e * ↑z * c) :=
  by
  have hkk : 1 ≤ (k : ℤ) := by linarith
  have hv1 :
    ∀ b : ℕ+, Complex.exp (2 * ↑π * I * e * z * b) = Complex.exp (2 * ↑π * I * e * z) ^ (b : ℕ) :=
    by
    intro b
    simp
    rw [← exp_nat_mul]; ring_nf
  simp_rw [hv1]
  have lj := nat_pos_tsum2 fun x : ℕ => (x : ℂ) ^ (k - 1) * Complex.exp (2 * ↑π * I * e * z) ^ x
  simp [algebraMap.coe_zero,  pow_zero, mul_one, zero_pow_eq_zero, tsub_pos_iff_lt] at lj
  have hk : ¬ (k : ℂ) - 1 = 0 := by
    have : 2 ≤ (k : ℤ) := by linarith
    by_contra h
    rw [sub_eq_zero] at h
    norm_cast at *
    rw [h] at this
    simp at *
  have hl := lj hk
  simp at *
  have HH :  Complex.abs ( Complex.exp (2 * ↑π * I * e * z) ) < 1 := by
    have hv2 :
      ∀ b : ℕ+,
        Complex.abs (Complex.exp (2 * ↑π * I * b * z)) =
          Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
      by
      intro b
      norm_cast
      rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
    rw [hv2 e]
    norm_cast
    apply pow_lt_one
    apply Complex.abs.nonneg
    apply exp_upperHalfPlane_lt_one
    simp
  rw [←norm_eq_abs] at HH
  have H := summable_pow_mul_geometric_of_norm_lt_1 (k - 1) HH
  norm_cast at *
  apply H.subtype

theorem a4 {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * I * ↑c * ↑z * ↑b)) :=
  by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonall]
  simp_rw [uncurry]
  simp
  have := @summable1 (k - 1) z
  rw [sigmaAntidiagonalEquivProd] at this
  simp at *
  apply this.congr
  intro x
  simp_rw [mapdiv]
  simp
  norm_cast
  simp
  left
  apply congr_arg
  ring



theorem Eisenstein_Series_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z =
      2 * (riemannZeta (k)) +
        2 * ((-2 * ↑π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * I * z * n) :=
  by
  have hkk : 1 ≤ (k : ℤ) := by linarith
  rw [eisen_iden k hk]
  rw [Eisenstein_tsum]
  simp_rw [eise]
  norm_cast at hk
  have := q_exp_iden_2 k hk hk2 z
  have t2 := q_exp_iden k ?_
  have t4 :
    ∑' c : ℕ+, ∑' d : ℤ, 1 / (((c • z : ℍ) : ℂ) + d) ^ k =
      ∑' e : ℕ+,
        (-2 * ↑π * I) ^ k / (k - 1)! *
          ∑' n : ℕ+, n ^ (k - 1) * Complex.exp (2 * ↑π * I * e * z * n) :=
    by congr; funext c; rw [t2 (c • z : ℍ)]; rw [natPosSMul_apply c z]; rw [← mul_assoc]
  simp only [EisensteinSeries.uhc, Int.cast_ofNat, cpow_nat_cast, one_div, neg_mul, ge_iff_le] at *
  rw [this]
  simp [natPosSMul_apply,  one_div, ofReal_mul, Int.cast_neg,
    algebraMap.coe_one, neg_mul, ofReal_neg, add_right_inj] at *
  rw [mul_assoc]
  congr
  norm_cast at *
  simp only [ofReal_mul, ofReal_ofNat, ge_iff_le]
  convert t4
  simp only
  rw [tsum_mul_left]
  simp
  left
  have H := @tsum_sigma_eqn (k - 1) z
  simp [ge_iff_le, ofReal_mul, ofReal_ofNat, PNat.pow_coe, Nat.cast_pow] at *
  rw [← H]
  rw [tsum_comm']
  rw [tsum_prod']
  · apply tsum_congr
    intro b
    apply tsum_congr
    intro c
    simp only [ge_iff_le, mul_eq_mul_left_iff, tsub_pos_iff_lt]
    left
    apply congr_arg
    ring
  · rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonall]
    have := @summable1 (k-1) z
    apply this.congr
    intro b
    simp only [ge_iff_le, cpow_nat_cast,  EisensteinSeries.uhc]
    norm_cast
  · intro e
    have := @a1 k e z
    simp at *
    apply this.congr
    intro b
    norm_cast
  · have := a4 hkk z
    apply this.congr
    intro b
    norm_cast
  · intro b
    have := a2 k b z
    apply this.congr
    intro t
    norm_cast
  · intro c
    have hkl : 2 ≤ k := by linarith
    have := a3 hkl c z
    apply this.congr
    intro i
    norm_cast
  · exact hk

theorem Eisenstein_Series_q_expansion_Bernoulli (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z =
      2 * ((-1) ^ (k / 2 + 1) * 2 ^ (2 * (k / 2) - 1) * π ^ k * bernoulli k / k !) +
        2 * ((-2 * ↑π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * I * z * n) :=
  by
  have := Eisenstein_Series_q_expansion k hk hk2 z
  norm_cast at *
  simp at *
  rw [this]
  simp
  have hke := hk2
  rw [even_iff_exists_two_mul] at hk2
  obtain ⟨c, hc⟩ := hk2
  have t2 : k / 2 = c := by
    apply Nat.div_eq_of_eq_mul_left
    linarith
    rw [mul_comm]
    exact hc
  have hk2_ne_0 : k / 2 ≠ 0 := by
    rw [t2]
    linarith
  have hhk : 2 * (k / 2) = k := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    apply hke
  have H := riemannZeta_two_mul_nat hk2_ne_0
  norm_cast at *
  rw [hhk] at H
  simp at *
  rw [H]
  have h0 : (-1) ^ ((k / 2 + 1) : ℕ) = (-1) ^ ((k : ℂ) / 2 + 1) := by
    have h00:  (k : ℂ)/2 = (((k/2) : ℕ) : ℂ) := by
      norm_cast
      rw [t2]
      rw [hc]
      simp
      field_simp
      ring
    rw [h00]
    simp
  norm_cast at *
  simp at *
  rw [h0]
  have h1 : 2 ^ (2 * ((k : ℂ) / 2) - 1) = 2 ^ ((k - 1) : ℕ) := by
    have h11 : (2 * ((k : ℂ) / 2) - 1) = ((k-1 : ℕ) : ℂ) := by
      have h111 : (((k-1): ℕ) : ℂ)=  (k: ℂ)-1 := by
        have hkk : 1 ≤ k := by linarith
        have := Int.ofNat_sub hkk
        norm_cast at *
      rw [h111]
      rw [hc]
      ring
    rw [h11]
  norm_cast at h1
  simp at h1
  rw [h1]



theorem i_pow_4 : I ^ 4 = 1 := by
    have h0 : I^4 = I^2 * I^2 := by
      norm_cast
      ring
    rw [h0]
    simp only [cpow_two, I_sq, mul_neg, mul_one, neg_neg]

theorem auxeq (r : ℝ) (hr : 0 < r) : (r : ℂ) ≠ 0 :=
  by
  by_contra h
  rw [Complex.ext_iff] at h
  simp at h
  rw [h] at hr
  simp at hr


theorem ineq : 0 ≤ 16 * π ^ 4 / ((2 + 1) * 2) :=
  by
  apply div_nonneg
  simp
  apply mul_nonneg
  linarith
  norm_cast
  apply pow_nonneg
  apply Real.pi_pos.le
  linarith

lemma rieamannZeta_4_eq_complex_abs : riemannZeta (4) = Complex.abs (riemannZeta (4)) := by
  rw [riemannZeta_four]
  apply symm
  norm_num
  norm_cast
  congr
  rw [abs_eq_self]
  apply Real.pi_pos.le
  apply abs_of_nat

theorem Eisen_4_non_zero : G[(4 : ℕ)] ≠ 0 := by
  by_contra h
  have H : (G[(4 : ℕ)] : ℍ → ℂ) = 0 := by simp only [h, coe_zero]
  rw [funext_iff] at H
  have H2 := H (⟨I, by simp only [I_im, zero_lt_one]⟩ : ℍ)
  have hk : 3 ≤ (4 : ℤ) := by linarith
  have hk2 : Even 4 := by simp only [even_bit0]
  have H3 := Eisenstein_Series_q_expansion 4 hk hk2 (⟨I, by simp⟩ : ℍ)
  simp only [Pi.zero_apply] at H2
  have r1 : (-2 * ↑π * I) ^ (4 ) / (4 - 1)! = 16 * π ^ 4 / 3! := by
    simp
    norm_cast
    ring_nf
    have  := i_pow_4
    norm_cast at this
    rw [this]
    simp only [one_mul]
    simp
    field_simp
    norm_cast
    ring
  simp only [Nat.cast_ofNat,
    ge_iff_le, Nat.succ_sub_succ_eq_sub, tsub_zero,  EisensteinSeries.uhc] at H3
  rw [r1] at H3
  have r2 : ∀ n : ℤ, Complex.exp (2 * ↑π * I * I * n) = Complex.exp (-2 * π * n) :=
    by
    intro n
    simp only [neg_mul]
    congr
    have : 2 * ↑π * I * I * ↑n = 2 * ↑π * (I * I) * ↑n := by ring
    rw [this]
    rw [I_mul_I]
    ring
  simp at H3
  have r3 :
    ∑' n : ℕ+, ↑(sigma 3 n) * Complex.exp (2 * ↑π * I * I * n) =
      ∑' n : ℕ+, sigma 3 n * Complex.exp (-2 * ↑π * n) :=
    by
      apply tsum_congr
      intro b
      simp
      left
      have := r2 b
      simp at *
      rw [this]
  simp at *
  rw [r3] at H3
  norm_cast at H3
  have H4 : 0 ≤ ∑' n : ℕ+, ↑(sigma 3 n) * Real.exp (↑(-2 : ℤ) * π * ↑n) :=
    by
    apply tsum_nonneg; intro b; apply mul_nonneg; norm_cast;
    simp only [zero_le]
    apply (Real.exp_pos _).le
  have H5 : 0 < 2 *Complex.abs (riemannZeta (4)) := by
    apply mul_pos; linarith;
    rw [riemannZeta_four]
    simp only [ofReal_pow, map_div₀, map_pow, abs_ofReal]
    apply div_pos
    apply pow_pos
    simp only [abs_pos, ne_eq]
    apply Real.pi_ne_zero
    simp only [AbsoluteValue.pos_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  let ε :=
    2 * Complex.abs (riemannZeta (4)) +
      2 * (16 * π ^ 4 / ↑((2 + 1) * 2)) * ∑' n : ℕ+, ↑(sigma 3 n) * Real.exp (-(2 : ℕ)  * π * ↑n)
  have H7 : G[(4 : ℕ)] (⟨I, by simp only [I_im, zero_lt_one]⟩ : ℍ) = ↑ε := by
    simp at *
    rw [H3]
    congr
    norm_cast
    apply rieamannZeta_4_eq_complex_abs
    norm_cast
    exact one_add_one_eq_two
  have H5 : 0 < ε := by
    apply Left.add_pos_of_pos_of_nonneg H5;
    apply mul_nonneg;
    simp;
    apply ineq;
    norm_cast at *
  have H8 := auxeq ε H5
  rw [← H7] at H8
  apply absurd H8
  simpa using H2
