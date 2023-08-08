import Project.ModForms.EisensteinSeries.EisenIsHolo
import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Project.ModForms.Riemzeta
import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.Calculus.Series
import Project.ModForms.EisensteinSeries.TsumLemmas
import Project.ModForms.EisensteinSeries.IteratedDerivLemmas
import Project.ModForms.EisensteinSeries.ExpSummableLemmas
import Project.ModForms.EisensteinSeries.AuxpLemmas
import Project.ModForms.EisensteinSeries.CotIden
import Project.ModForms.EisensteinSeries.QExpAux
import Mathbin.NumberTheory.ZetaFunction

#align_import mod_forms.Eisenstein_Series.Eisenstein_series_q_expansions

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ'" => (⟨UpperHalfPlane.upperHalfSpace, upper_half_plane_isOpen⟩ : OpenSubs)

def eisensteinSeriesOfWt_ (k : ℤ) :=
  if h : 3 ≤ k then eisensteinSeriesIsModularForm k h else 0

local notation "G[" k "]" => eisensteinSeriesOfWt_ k

/-
def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6
-/
open scoped DirectSum BigOperators

local notation "ℍ" => UpperHalfPlane

theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * rZ k + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * z + d) ^ k :=
  by
  rw [rZ, tsum_prod, sum_int_even]
  · simp only [algebraMap.coe_zero, MulZeroClass.zero_mul, zero_add, one_div, coe_coe,
      Int.cast_ofNat, add_left_inj]
    rw [rie, sum_int_even]
    simp only [algebraMap.coe_zero, coe_coe, Int.cast_ofNat, Real.rpow_nat_cast, one_div]
    have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by convert inv_zero; norm_cast; apply zero_pow'; linarith
    have h00 : ((0 ^ k : ℕ) : ℝ)⁻¹ = 0 := by convert inv_zero; norm_cast; apply zero_pow'; linarith
    rw [h0]
    simp only [zero_add, mul_eq_mul_left_iff, bit0_eq_zero, one_ne_zero, or_false_iff]
    rw [← tsum_coe, ← tsum_pNat]
    congr
    funext
    norm_cast
    simp only [of_real_inv, of_real_nat_cast]
    norm_cast
    apply h00
    intro n
    apply congr_arg
    apply symm
    norm_cast
    apply Even.neg_pow hk2
    have H := int_RZ_is_summmable k _
    rw [rie] at H 
    apply summable_int_of_summable_nat
    apply complex_rie_summable k hk
    have HG : (fun n : ℕ => ((-(n : ℤ) : ℂ) ^ k)⁻¹) = fun n : ℕ => ((n : ℂ) ^ k)⁻¹ :=
      by
      funext
      apply congr_arg
      rw [← coe_coe]
      apply Even.neg_pow hk2
    simp only [Int.cast_neg, Int.cast_ofNat, Real.rpow_nat_cast, one_div,
      Real.summable_nat_pow_inv] at *
    rw [HG]
    apply complex_rie_summable k hk
    norm_cast
    linarith
  · intro n
    simp only [one_div, Int.cast_neg, neg_mul]
    apply symm
    rw [int_sum_neg]
    congr
    funext
    simp only [Int.cast_neg, inv_inj]
    ring_nf
    convert Even.neg_pow hk2 ((z : ℂ) * n + d)
    ring
    apply summable_factor n z k hk
  · apply prod_sum _ (Eisenstein_series_is_summable k z hk)
  · apply Eisenstein_series_is_summable k z hk

def sigmaFn (k n : ℕ) : ℕ :=
  ∑ d : ℕ in Nat.divisors n, d ^ k

def sigmaFn' (k n : ℕ) : ℕ :=
  ∑ d : ℕ in Nat.divisors n, (n / d) ^ k

theorem sigmaFn_eql (k n : ℕ) : sigmaFn k n = sigmaFn' k n :=
  by
  simp_rw [sigmaFn, sigmaFn']
  rw [← Nat.sum_div_divisors]

def sigma' (k n : ℕ) : ℤ :=
  ∑ x in Nat.divisorsAntidiagonal n, x.1 ^ k

theorem sigme_fn_one (k : ℕ) : sigmaFn k 1 = 1 :=
  by
  rw [sigmaFn, Nat.divisors_one]
  simp_rw [Finset.sum_singleton]
  simp

theorem sigmaFn_nonneg (k n : ℕ) : 0 ≤ sigmaFn k n :=
  by
  rw [sigmaFn]
  apply Finset.sum_nonneg
  intro i hi
  apply pow_nonneg
  linarith

theorem eisen_iden (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z = eisensteinSeriesOfWeight_ k z :=
  by
  simp_rw [eisensteinSeriesOfWt_]
  simp only [hk, dif_pos]
  rw [Eisenstein_series_is_modular_form]
  simp_rw [Eisenstein_is_slash_inv]
  rfl

instance natPosMul : MulAction ℕ+ ℍ
    where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2
  one_smul z := by simp
  mul_smul x y z := by dsimp; simp; simp_rw [← mul_assoc]

theorem auxnpm (c : ℕ+) (z : ℍ) : ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := by rfl

theorem ine (a b k : ℕ) (hb : 0 < b) (h : a ≤ b) : a ^ k ≤ 2 * b ^ (k + 1) :=
  by
  have h1 : a ^ k ≤ b ^ k := pow_mono_right k h
  apply le_trans h1
  have h2 : b ^ k ≤ b ^ (k + 1) := by apply Nat.pow_le_pow_of_le_right hb; linarith
  apply le_trans h2
  apply le_mul_of_one_le_left
  apply pow_nonneg
  simp only [zero_le']
  linarith

theorem ineqauxx (z : ℍ) (k : ℕ) (n : Σ x : ℕ+, Nat.divisorsAntidiagonal x) :
    ‖(n.2.1.1 : ℂ) ^ k * Complex.exp (2 * ↑π * I * z * n.2.1.1 * n.2.1.2)‖ ≤
      Complex.abs (2 * n.1 ^ (k + 1) * Complex.exp (2 * ↑π * I * z * n.1)) :=
  by
  simp only [Subtype.val_eq_coe, norm_eq_abs, AbsoluteValue.map_mul, Complex.abs_pow, abs_cast_nat,
    coe_coe, Complex.abs_two]
  have hn := n.2.2
  simp only [Subtype.val_eq_coe, Nat.mem_divisorsAntidiagonal, Ne.def, PNat.ne_zero, not_false_iff,
    and_true_iff] at *
  norm_cast
  simp_rw [← hn]
  have gt : ∀ a b : ℕ, ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := Nat.cast_mul
  rw [GT.gt]
  rw [← mul_assoc]
  simp only [Nat.cast_pow, of_real_mul, of_real_bit0, PNat.pow_coe, Nat.cast_mul, Nat.cast_bit0,
    algebraMap.coe_one]
  rw [mul_le_mul_right _]
  have J := Nat.fst_mem_divisors_of_mem_antidiagonal n.2.2
  simp only [Subtype.val_eq_coe, Nat.mem_divisors, Ne.def, PNat.ne_zero, not_false_iff,
    and_true_iff] at J 
  have J2 := Nat.le_of_dvd _ J
  norm_cast
  apply ine
  apply n.1.2
  exact J2
  apply n.1.2
  exact Real.hasZero
  exact OrderedSemiring.toMulPosMono
  exact MulPosReflectLT.toMulPosMonoRev
  simp only [AbsoluteValue.pos_iff, Ne.def]
  apply Complex.exp_ne_zero

theorem anti_diag_card_le (n : ℕ+) : (Nat.divisorsAntidiagonal n).card ≤ n ^ 2 :=
  by
  classical!
  simp_rw [Nat.divisorsAntidiagonal]
  apply le_trans (Finset.card_filter_le _ _)
  simp
  rw [pow_two]

theorem summable1 {k : ℕ} (z : ℍ) :
    Summable fun p : Σ b : ℕ+, ↥(Nat.divisorsAntidiagonal b) =>
      ((sigmaAntidiagonalEquivProd p).fst : ℂ) ^ k *
        exp
          (2 * ↑π * I * ↑z * (sigmaAntidiagonalEquivProd p).fst *
            (sigmaAntidiagonalEquivProd p).snd) :=
  by
  have := summable_of_norm_bounded _ _ (ineqauxx z k)
  apply this
  rw [summable_sigma_of_nonneg]
  constructor
  apply fun n => (hasSum_fintype _).Summable
  exact fintypeOfOption
  simp only [coe_coe, AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_cast_nat]
  apply summable_of_nonneg_of_le _ _ (@summable_pow_mul_exp (k + 2) z)
  intro x
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  norm_cast
  apply mul_nonneg
  exact (Nat.divisorsAntidiagonal x).card.cast_nonneg
  apply mul_nonneg
  simp only [Nat.cast_mul, Nat.cast_bit0, algebraMap.coe_one, zero_le_mul_right, Nat.cast_pos,
    PNat.pos, zero_le_bit0, zero_le_one]
  apply complex.abs.nonneg
  intro b
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, coe_coe,
    AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_cast_nat]
  have hk :
    2 * (b : ℝ) ^ (k + 2 + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b)) =
      b ^ 2 * (2 * b ^ (k + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b))) :=
    by ring
  simp_rw [← coe_coe]
  rw [hk]
  have ht := anti_diag_card_le b
  refine' mul_le_mul _ _ _ _
  simp only [coe_coe]
  norm_cast
  apply ht
  refine' Eq.le _
  rfl
  simp only [coe_coe, zero_le_mul_left, zero_lt_mul_right, pow_pos, Nat.cast_pos, PNat.pos,
    zero_lt_bit0, zero_lt_one, map_nonneg]
  nlinarith
  intro x
  apply complex.abs.nonneg

theorem sum_sigma_fn_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * I * z * c.1 * c.2) =
      ∑' e : ℕ+,
        ∑ x : Nat.divisorsAntidiagonal e,
          x.1.1 ^ k * Complex.exp (2 * ↑π * I * z * x.1.1 * x.1.2) :=
  by
  rw [← sigma_antidiagonal_equiv_prod.tsum_eq]
  rw [tsum_sigma']
  congr
  funext
  rw [tsum_fintype]
  congr
  apply fun n => (hasSum_fintype _).Summable
  exact fintypeOfOption
  apply summable1
  exact T25Space.t2Space

theorem div_mul_aux {k : ℕ} (z : ℍ) (n : ℕ) :
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

theorem sum_sigmaFn_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigmaFn k e * Complex.exp (2 * ↑π * I * z * e) :=
  by
  simp_rw [sigmaFn_eql]
  rw [sum_sigma_fn_eq z]
  congr
  funext
  rw [sigmaFn']
  have :=
    Nat.sum_divisorsAntidiagonal' fun x => fun y =>
      (x : ℂ) ^ k * Complex.exp (2 * ↑π * I * z * x * y)
  simp only [Subtype.val_eq_coe, Nat.cast_sum, Nat.cast_pow, coe_coe] at *
  simp_rw [mul_assoc] at *
  rw [div_mul_aux _ _] at this 
  rw [← coe_coe]
  have hr :
    (∑ x : ℕ in (e : ℕ).divisors, ↑(↑e / x) ^ k) * exp (2 * (↑π * (I * (↑z * ↑e)))) =
      ∑ x : ℕ in (e : ℕ).divisors, ↑(↑e / x) ^ k * exp (2 * (↑π * (I * (↑z * (e : ℕ))))) :=
    by
    rw [← coe_coe]
    apply Finset.sum_mul
  rw [hr]
  rw [← this]
  have := sumaux (fun x => (x.1 : ℂ) ^ k * Complex.exp (2 * ↑π * I * z * x.1 * x.2)) e
  convert this
  repeat'
    funext
    simp_rw [mul_assoc]

theorem a1 {k : ℕ} (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * ↑z * e * c) :=
  by
  have h2ne : (e : ℂ) ^ (k - 1) ≠ 0 := by apply pow_ne_zero; simp
  rw [summable_mul_left_iff h2ne]
  have hv1 :
    ∀ b : ℕ+, Complex.exp (2 * ↑π * I * z * e * b) = Complex.exp (2 * ↑π * I * z * e) ^ (b : ℕ) :=
    by
    intro b
    rw [← exp_nat_mul]; ring_nf
  simp_rw [hv1]
  apply nat_pos_tsum'
  simp only [coe_coe, summable_geometric_iff_norm_lt_1, norm_eq_abs]
  have hv2 :
    ∀ b : ℕ+,
      Complex.abs (Complex.exp (2 * ↑π * I * z * b)) =
        Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
    by
    intro b
    rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; ring_nf
  simp only [coe_coe, Ne.def] at *
  rw [hv2 e]
  apply pow_lt_one
  apply complex.abs.nonneg
  apply exp_upperHalfPlane_lt_one
  simp only [Ne.def, PNat.ne_zero, not_false_iff]

theorem a2 {k : ℕ} (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * c * ↑z * e) :=
  by
  have := @a1 k e z
  convert this
  funext
  simp only [coe_coe, mul_eq_mul_left_iff]
  left
  ring_nf

theorem a3 {k : ℕ} (h : 2 ≤ k) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ (k - 1) * exp (2 * ↑π * I * e * ↑z * c) :=
  by
  have hv1 :
    ∀ b : ℕ+, Complex.exp (2 * ↑π * I * e * z * b) = Complex.exp (2 * ↑π * I * e * z) ^ (b : ℕ) :=
    by
    intro b
    rw [← exp_nat_mul]; ring_nf
  simp_rw [hv1]
  simp_rw [coe_coe]
  have lj := nat_pos_tsum2 fun x : ℕ => (x : ℂ) ^ (k - 1) * Complex.exp (2 * ↑π * I * e * z) ^ x
  simp only [algebraMap.coe_zero, coe_coe, pow_zero, mul_one, zero_pow_eq_zero, tsub_pos_iff_lt] at
    lj 
  have hk : 1 < k := by linarith
  have hl := lj hk
  simp only [coe_coe] at *
  have H := summable_pow_mul_geometric_of_norm_lt_1 (k - 1)
  have H2 := hl.2 (H _)
  exact H2
  simp only [norm_eq_abs]
  have hv2 :
    ∀ b : ℕ+,
      Complex.abs (Complex.exp (2 * ↑π * I * b * z)) =
        Complex.abs (Complex.exp (2 * ↑π * I * z)) ^ (b : ℕ) :=
    by
    intro b
    rw [← Complex.abs_pow]; congr; rw [← exp_nat_mul]; simp; rw [← mul_assoc]; ring_nf
  simp only [norm_eq_abs, coe_coe] at *
  rw [hv2 e]
  apply pow_lt_one
  apply complex.abs.nonneg
  apply exp_upperHalfPlane_lt_one
  simp only [Ne.def, PNat.ne_zero, not_false_iff]
  exact complete_of_proper

theorem a4 {k : ℕ} (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * I * ↑c * ↑z * ↑b)) :=
  by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonall]
  rw [uncurry]
  simp
  have := @summable1 (k - 1) z
  rw [sigmaAntidiagonalEquivProd] at this 
  simp at *
  convert this
  funext
  simp_rw [mapdiv]
  have hg : 2 * ↑π * I * x.2.1.2 * ↑z * x.2.1.1 = 2 * ↑π * I * z * x.2.1.1 * x.2.1.2 := by simp;
    ring
  simp at *
  left
  rw [hg]

theorem Eisenstein_Series_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z =
      2 * rZ k +
        2 * ((-2 * ↑π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigmaFn (k - 1) n * Complex.exp (2 * ↑π * I * z * n) :=
  by
  rw [eisen_iden k hk hk2]
  rw [Eisenstein_series_of_weight_]
  simp_rw [Eise]
  norm_cast at hk 
  have := q_exp_iden_2 k hk hk2 z
  have t2 := q_exp_iden k _
  have t4 :
    ∑' c : ℕ+, ∑' d : ℤ, 1 / (((c • z : ℍ) : ℂ) + d) ^ k =
      ∑' e : ℕ+,
        (-2 * ↑π * I) ^ k / (k - 1)! *
          ∑' n : ℕ+, n ^ (k - 1) * Complex.exp (2 * ↑π * I * e * z * n) :=
    by congr; funext; rw [t2 (c • z : ℍ)]; rw [auxnpm c z]; rw [← mul_assoc]
  norm_cast
  rw [this]
  simp only [auxnpm, coe_coe, one_div, of_real_mul, of_real_bit0, Int.cast_neg, Int.cast_bit0,
    algebraMap.coe_one, neg_mul, of_real_neg, add_right_inj] at *
  rw [mul_assoc]
  congr
  rw [t4]
  simp only
  rw [tsum_mul_left]
  apply congr_arg
  have H := @sum_sigmaFn_eqn (k - 1) z
  simp_rw [← coe_coe]
  rw [← H]
  rw [tsum_comm']
  rw [tsum_prod']
  simp only [coe_coe]
  congr
  funext
  congr
  funext
  have ho : 2 * ↑π * I * c * ↑z * b = 2 * ↑π * I * z * b * c := by ring
  simp at ho 
  rw [ho]
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonall]
  apply summable1
  intro e
  simp
  apply a1
  exact a4 z
  intro b
  apply a2
  intro c
  apply a3
  repeat' linarith

theorem Eisenstein_Series_q_expansion' (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z =
      2 * riemannZeta k +
        2 * ((-2 * ↑π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigmaFn (k - 1) n * Complex.exp (2 * ↑π * I * z * n) :=
  by
  have := Eisenstein_Series_q_expansion k hk hk2 z
  convert this
  rw [rZ, rie]
  have hkc : 1 < (k : ℂ).re := by simp; linarith
  have hz := zeta_eq_tsum_one_div_nat_cpow hkc
  rw [hz]
  simp
  rw [← tsum_coe]
  apply tsum_congr
  intro b
  simp

theorem Eisenstein_Series_q_expansion_Bernoulli (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (eisensteinSeriesOfWt_ k) z =
      2 * ((-1) ^ (k / 2 + 1) * 2 ^ (2 * (k / 2) - 1) * π ^ k * bernoulli k / k !) +
        2 * ((-2 * ↑π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigmaFn (k - 1) n * Complex.exp (2 * ↑π * I * z * n) :=
  by
  have := Eisenstein_Series_q_expansion' k hk hk2 z
  convert this
  have hke := hk2
  rw [even_iff_exists_two_mul] at hk2 
  obtain ⟨c, hc⟩ := hk2
  have : k / 2 = c := by
    apply Nat.div_eq_of_eq_mul_left
    linarith
    rw [mul_comm]
    exact hc
  have hk2_ne_0 : k / 2 ≠ 0 := by
    rw [this]
    linarith
  have hhk : 2 * (k / 2) = k := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    apply hke
  have H := riemannZeta_two_mul_nat hk2_ne_0
  simp_rw [hhk] at H 
  convert H.symm
  norm_cast
  exact hhk.symm

theorem i_pow_4 : I ^ 4 = 1 := by simp only [I_pow_bit0, neg_one_sq]

theorem auxeq (r : ℝ) (hr : 0 < r) : (r : ℂ) ≠ 0 :=
  by
  by_contra
  rw [Complex.ext_iff] at h 
  simp at h 
  rw [h] at hr 
  simp at hr 
  exact hr

theorem ineq : 0 ≤ 16 * π ^ 4 / ((2 + 1) * 2) :=
  by
  apply div_nonneg
  simp
  apply pow_nonneg
  apply real.pi_pos.le
  linarith

theorem Eisen_4_non_zero : G[(4 : ℕ)] ≠ 0 := by
  by_contra
  have H : (G[(4 : ℕ)] : ℍ → ℂ) = 0 := by simp only [h, coe_zero]
  rw [funext_iff] at H 
  have H2 := H (⟨I, by simp only [I_im, zero_lt_one]⟩ : ℍ)
  have hk : 3 ≤ (4 : ℤ) := by linarith
  have hk2 : Even 4 := by simp only [even_bit0]
  have H3 := Eisenstein_Series_q_expansion 4 hk hk2 (⟨I, by simp⟩ : ℍ)
  simp only [Pi.zero_apply] at H2 
  have r1 : (-2 * ↑π * I) ^ 4 / (4 - 1)! = 16 * π ^ 4 / 3! := by ring; rw [i_pow_4];
    simp only [one_mul]
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
  simp only [Nat.cast_bit0, algebraMap.coe_one, Nat.factorial_succ, Nat.factorial_two, Nat.cast_mul,
    Nat.cast_add, Nat.succ_sub_succ_eq_sub, tsub_zero, Subtype.coe_mk] at H3 
  have r3 :
    ∑' n : ℕ+, ↑(sigmaFn 3 n) * Complex.exp (2 * ↑π * I * I * n) =
      ∑' n : ℕ+, sigmaFn 3 n * Complex.exp (-2 * ↑π * n) :=
    by congr; funext; simp; left; convert r2 n; ring
  rw [r3] at H3 
  norm_cast at H3 
  have H4 : 0 ≤ ∑' n : ℕ+, ↑(sigmaFn 3 n) * Real.exp (↑(-2 : ℤ) * π * ↑n) :=
    by
    apply tsum_nonneg; intro b; apply mul_nonneg; norm_cast; apply sigmaFn_nonneg
    apply (Real.exp_pos _).le
  have H5 : 0 < 2 * rZ 4 := by apply mul_pos; linarith; apply rZ_pos; linarith
  let ε :=
    2 * rZ 4 +
      2 * (16 * π ^ 4 / ↑((2 + 1) * 2)) * ∑' n : ℕ+, ↑(sigmaFn 3 n) * Real.exp (↑(-2 : ℤ) * π * ↑n)
  have H7 : G[(4 : ℕ)] (⟨I, by simp only [I_im, zero_lt_one]⟩ : ℍ) = ↑ε := by rw [H3]
  have H5 : 0 < ε := by apply Left.add_pos_of_pos_of_nonneg H5; apply mul_nonneg; simp; apply ineq;
    apply H4
  have H8 := auxeq ε H5
  rw [← H7] at H8 
  apply absurd H8
  simpa using H2

