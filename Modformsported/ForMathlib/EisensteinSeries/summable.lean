import Modformsported.ForMathlib.TsumLemmas
import Modformsported.ForMathlib.EisensteinSeries.basic
import Modformsported.ForMathlib.EisensteinSeries.bounds
import Modformsported.ForMathlib.EisensteinSeries.lattice_functions
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.PSeries

open Complex

open scoped BigOperators NNReal Classical Filter UpperHalfPlane

open ModularForm

open SlashInvariantForm

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

noncomputable section

theorem linear_ne_zero' (c d : ℤ) (z : ℍ) (h : c ≠ 0) : (c : ℂ) * z + d  ≠ 0 := by
  have := UpperHalfPlane.linear_ne_zero  ![c, d] z ?_
  simp at *
  exact this
  simp [h]

theorem pow_linear_ne_zero' (c d : ℤ) (z : ℍ) (h : c ≠ 0) (k : ℕ) : ((c : ℂ) * z + d)^k  ≠ 0 := by
  norm_cast
  apply pow_ne_zero _ (linear_ne_zero' c d z h)

theorem linear_ne_zero'' (c d : ℤ) (z : ℍ) (h : d ≠ 0) : (c : ℂ) * z + d  ≠ 0 := by
  have := UpperHalfPlane.linear_ne_zero  ![c, d] z ?_
  simp at *
  exact this
  simp [h]

theorem pow_linear_ne_zero'' (c d : ℤ) (z : ℍ) (h : d ≠ 0) (k : ℤ) : ((c : ℂ) * z + d)^k  ≠ 0 := by
  norm_cast
  apply zpow_ne_zero _ (linear_ne_zero'' c d z h)

theorem linear_eq_zero_iff (c d : ℤ) (z : ℍ): (c : ℂ) * z + d  = 0  ↔ c = 0 ∧ d = 0:= by
  constructor
  intro h
  by_contra hc
  simp at hc
  have := linear_ne_zero'' c d z
  by_cases hcc : c = 0
  have H := this (hc hcc)
  norm_cast at *
  have := linear_ne_zero' c d z hcc
  norm_cast
  intro h
  rw [h.1,h.2]
  simp

theorem natpowsinv (x : ℝ) (n : ℤ) (h2 : x ≠ 0) : (x ^ (n - 1))⁻¹ = (x ^ n)⁻¹ * x :=
  by
  have := zpow_sub_one₀ h2 n
  norm_cast
  rw [this]
  have h3 := mul_zpow (x ^ n) x⁻¹ (-1)
  simp at *
  exact h3

namespace EisensteinSeries

section Abs_Eisentein_summable

lemma Eise_on_square_is_bounded_Case1 (k : ℤ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (hn : 1 ≤ n) (hk : 0 ≤ k)
  (C1 :Complex.abs (x.1 : ℂ) = n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  lift k to ℕ using hk
  rw [inv_le_inv]
  have h0 : (x.1 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C1
    simp [Int.cast_zero] at C1
    norm_cast at C1
    rw [← C1] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  have h1 : (↑x.fst * ↑z + ↑x.snd) ^ (k : ℤ) =
    ((x.fst : ℂ) ^ (k : ℤ)) * ((z : ℂ) + (x.2 : ℂ) / ↑x.fst) ^ (k : ℤ) :=
    by
    field_simp
    ring
  rw [h1]
  simp_rw [map_mul Complex.abs]
  norm_cast at *
  have h3 : Complex.abs (n^k : ℕ) = Complex.abs (x.fst^k : ℤ) := by
    have : Complex.abs (x.fst^k : ℤ) = Complex.abs (x.fst)^k := by
      simp only [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C1]
    norm_cast
    simp only [Nat.cast_pow, map_pow, abs_natCast]
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Complex.abs.nonneg _)
  have := auxlem2 z x k
  simp at this
  norm_cast at *
  convert this
  simp only [_root_.abs_pow]
  simp only [map_pow]
  apply Complex.abs.pos (pow_linear_ne_zero' _ _ _ _ _)
  intro hx
  rw [hx] at C1
  simp [Int.cast_zero] at C1
  norm_cast at C1
  rw [← C1] at hn
  simp only [Nat.one_ne_zero, le_zero_iff] at hn
  apply rfunct_mul_n_pos k z n hn

lemma Eise_on_square_is_bounded_Case2 (k : ℤ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (hn : 1 ≤ n) (hk : 0 ≤ k)
  (C2 :Complex.abs (x.2 : ℂ) = n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  lift k to ℕ using hk
  rw [inv_le_inv]
  have h0 : (x.2 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C2
    simp at C2
    norm_cast at *
    rw [← C2] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  have h1 : (↑x.fst * ↑z + ↑x.snd) ^ (k : ℤ) =
    (x.snd  : ℂ)^ (k) * ((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ (k) := by
    field_simp
    ring_nf
  rw [h1]
  simp_rw [map_mul Complex.abs]
  have h3 : Complex.abs (n^k ) = Complex.abs ((x.2)^k ) := by
    have : Complex.abs (x.snd^k) = Complex.abs (x.snd)^k := by
      simp  [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C2]
    norm_cast
    simp [Nat.cast_pow, map_pow, abs_natCast]
  simp at *
  norm_cast at *
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left
  have := auxlem3 z x k
  simp at *
  norm_cast at *
  norm_cast
  simp  [ge_iff_le, map_nonneg, zpow_nonneg]
  apply Complex.abs.pos (pow_linear_ne_zero'' _ _ _ _ _)
  have h0 : (x.2 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C2
    simp at C2
    norm_cast at *
    rw [← C2] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  norm_cast at *
  apply rfunct_mul_n_pos k z n hn


theorem Eise_on_square_is_bounded (k : ℤ) (hk : 0 ≤ k) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (h : x ∈ square n)
  (hn : 1 ≤ n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
    (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ :=
  by
  by_cases C1 : Complex.abs (x.1 : ℂ) = n
  apply Eise_on_square_is_bounded_Case1 k z n x hn hk C1
  have C2 := Complex_abs_square_left_ne n x h C1
  apply Eise_on_square_is_bounded_Case2 k z n x hn hk C2


theorem Eise_on_square_is_bounded' (k : ℤ ) (hk : 0 ≤ k) (z : ℍ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : ℤ × ℤ,
      x ∈ square n →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  intro x hx
  apply Eise_on_square_is_bounded k hk z n x hx hn

theorem Eise_on_zero_square (k : ℤ) (hk : 0 ≤ k) (z : ℍ) (h : 1 ≤ k) :
    ∀ x : ℤ × ℤ,
      x ∈ square 0 →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * 0 ^ k))⁻¹ :=
  by
  lift k to ℕ using hk
  intro x hx
  rw [square_zero] at hx
  simp only [Finset.mem_singleton] at hx
  simp_rw [hx]
  simp only [add_zero, Int.cast_zero, MulZeroClass.zero_mul, map_mul Complex.abs]
  have h1 : (0 : ℝ) ^ (k : ℕ) = 0 := by
    simp [cpow_nat_cast, ne_eq, zero_pow_eq_zero]
    linarith
  norm_cast
  simp
  norm_cast at *
  rw [h1]
  simp [map_zero, inv_zero, cpow_nat_cast, map_pow, abs_ofReal, mul_zero, le_refl]


theorem Eise_on_square_is_bounded'' (k : ℤ) (hk : 0 ≤ k) (z : ℍ) (n : ℕ) (hn : 1 ≤ k) :
    ∀ x : ℤ × ℤ,
      x ∈ square n →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  by_cases h0 : n = 0
  · rw [h0]; have := Eise_on_zero_square k hk z hn; simp at *; apply this
  have Hn : 1 ≤ n := by
    have := Nat.pos_of_ne_zero h0
    linarith
  intro x hx
  apply Eise_on_square_is_bounded k hk z n x hx Hn


theorem AbsEise_bounded_on_square (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
    ∀ n : ℕ, ∑ y : ℤ × ℤ in square n, (AbsEise k z) y ≤ 8 / rfunct z ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ :=
  by
  intro n
  simp_rw [AbsEise]
  simp [one_div, Complex.abs_pow, abs_inv, zpow_ofNat]
  have hk0 : 0 ≤ k := by linarith
  have k0 : 1 ≤ k := by linarith
  have BO := Eise_on_square_is_bounded'' (k ) hk0 (z : ℍ) (n : ℕ) k0
  by_cases n0 : n = 0
  · rw [n0]
    norm_cast
    rw [square_zero]
    simp  [add_zero, Int.cast_zero, Nat.cast_zero, MulZeroClass.zero_mul, Finset.sum_singleton]
    rw [zero_zpow]
    rw [zero_zpow]
    simp
    linarith
    linarith
  have := Finset.sum_le_sum BO
  simp only [Finset.sum_const, map_mul Complex.abs, nsmul_eq_mul] at this
  rw [square_size' n0] at this
  norm_cast at this
  have ne :
    (8 * n * (Complex.abs (rfunct z ^ k) * (n ^ k : ℝ))⁻¹ : ℝ) =
      8 / rfunct z ^ k * ((n : ℝ)^ ((k : ℤ) - 1))⁻¹ :=
    by
    norm_cast
    simp
    field_simp
    ring_nf
    simp
    rw [mul_comm]
    congr
    rw [abs_eq_self]
    apply zpow_nonneg
    apply (EisensteinSeries.rfunct_pos z).le
    have := natpowsinv n k ?_
    rw [mul_comm]

    rw [←this]
    simp

    norm_cast at *
    congr
    rw [add_comm]
    congr
    norm_cast at *
  simp at ne
  rw [←ne]
  simp at this
  convert this
  lift k to ℕ using hk0
  simp


/-
theorem AbsEise_sum_on_square_bounded (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    ∀ n : ℕ,
      (fun x : ℕ => ∑ y : ℤ × ℤ in square x, (AbsEise k z) y) n ≤
        8 / rfunct z ^ k * (rie (k - 1)) n :=
  by
  have BIGCLAIM := AbsEise_bounded_on_square k z h
  simp only at BIGCLAIM
  simp_rw [rie]
  simp only [one_div]
  intro n
  have tr : ((↑n ^ ((k : ℤ) - 1))⁻¹ : ℝ) = ((↑n ^ ((k : ℝ) - 1))⁻¹ : ℝ) :=
    by
    simp [inv_inj]
  rw [← tr]
  apply BIGCLAIM n
-/

lemma summable_rfunct_twist  (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
  Summable fun n : ℕ => 8 / rfunct z ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k -1  : ℤ) := by linarith
    norm_cast at *
  have riesum := Real.summable_nat_rpow_inv.2 hk
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    linarith
    norm_cast
    apply zpow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := rfunct_pos z
    rw [HR] at this
    simp only [lt_self_iff_false] at this
  rw [← (summable_mul_left_iff nze).symm]
  simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at riesum
  convert riesum
  norm_cast

theorem real_eise_is_summable (k : ℤ) (z : ℍ) (h : 3 ≤ k) : Summable (AbsEise k z) :=by
  let In := fun (n : ℕ) => square n
  have HI := squares_cover_all
  let g := fun y : ℤ × ℤ => (AbsEise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by
    intro y
    simp_rw [AbsEise]
    simp
    apply zpow_nonneg
    apply Complex.abs.nonneg
  have index_lem := sum_lemma g gpos In HI
  rw [index_lem]
  let e := fun x : ℕ => ∑ y : ℤ × ℤ in In x, g y
  have smallerclaim := AbsEise_bounded_on_square k z h
  have epos : ∀ x : ℕ, 0 ≤ e x := by
    intro x
    apply Finset.sum_nonneg; intro i _;
    apply Complex.abs.nonneg
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k -1  : ℤ) := by linarith
    norm_cast at *
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    linarith
    norm_cast
    apply zpow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := rfunct_pos z
    rw [HR] at this
    simp only [lt_self_iff_false] at this
  have riesum' : Summable fun n : ℕ => 8 / rfunct z ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ :=
    by
    rw [← (summable_mul_left_iff nze).symm]
    norm_cast
    have riesum := Real.summable_nat_rpow_inv.2 hk
    convert riesum
    norm_cast
  have := Summable.of_nonneg_of_le epos smallerclaim
  apply this
  apply riesum'

theorem Eisenstein_tsum_summable (k : ℤ) (z : ℍ) (h : 3 ≤ k) : Summable (eise k z) :=
  by
  rw [summable_norm_iff.symm]
  have := real_eise_is_summable k z h
  exact this
