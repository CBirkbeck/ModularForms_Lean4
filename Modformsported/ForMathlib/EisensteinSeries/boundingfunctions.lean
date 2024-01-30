import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Modformsported.ForMathlib.EisensteinSeries.bounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Modformsported.ForMathlib.EisensteinSeries.lattice_functions
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Series

noncomputable section

open Complex Filter UpperHalfPlane Set

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane Complex

namespace EisensteinSeries


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
def r (z : ℍ) : ℝ := min (z.1.2) (Real.sqrt (lowerBound1 z))

theorem r_pos (z : ℍ) : 0 < r z := by
  simp only [r, lt_min_iff, z.property, Real.sqrt_pos, lowerBound1_pos, and_self]

theorem r_ne_zero (z : ℍ) :  r z ≠ 0 := ne_of_gt (r_pos z)

lemma r_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ) (hn : 1 ≤ n) :
  0 < (Complex.abs ((r z : ℂ) ^ (k : ℤ) * (n : ℂ)^ (k : ℤ))) := by
  apply Complex.abs.pos
  apply mul_ne_zero
  norm_cast
  apply pow_ne_zero k (ne_of_gt (r_pos z))
  apply pow_ne_zero
  norm_cast at *
  linarith

lemma pow_two_of_nonzero_ge_one (a : ℤ) (ha : a  ≠ 0) : 0 ≤ a^2 - 1  := by
  simp only [sub_nonneg, one_le_sq_iff_one_le_abs, ge_iff_le]
  exact Int.one_le_abs ha

theorem aux4 (a b : ℝ) (h : 0 < b) :
    (b ^ 2) / (a ^ 2 + b ^ 2) = 1 / ((a / b) ^ 2 + 1) :=
  by
  field_simp

theorem auxlb (z : ℍ) (δ : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (z.1.2 ^ 2 ) / (z.1.1 ^ 2 + z.1.2 ^ 2) ≤  (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 := by
  have H1 : (δ * z.1.1 + n) ^ 2 + (δ * z.1.2) ^ 2 =
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1 + n^2 := by
    ring
  have H4 :
    (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + n * 2 * δ * z.1.1   + n^2) * (z.1.1 ^ 2 + z.1.2 ^ 2) -
    (z.1.2 ^ 2) = (δ * (z.1.1 ^ 2 + z.1.2 ^ 2)+ n * z.1.1)^2 + (n^2 - 1)* (z.1.2)^2 := by
     ring
  rw [H1, div_le_iff, ← sub_nonneg, H4]
  · apply add_nonneg
    apply pow_two_nonneg
    apply mul_nonneg
    norm_cast
    apply pow_two_of_nonzero_ge_one n hn
    apply pow_two_nonneg
  · apply_rules [add_pos_of_nonneg_of_pos, pow_two_nonneg, upper_half_im_pow_pos z 2]

theorem auxbound1 (z : ℍ) (δ : ℝ) : r z ≤ Complex.abs ((z : ℂ) + δ)  := by
    rw [r, Complex.abs]
    have H1 : (z : ℂ).im ≤
      Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) := by
      rw [Real.le_sqrt' ]
      norm_cast
      nlinarith
      apply z.2
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, AbsoluteValue.coe_mk, MulHom.coe_mk,
      min_le_iff] at *
    left
    norm_cast
    rw [normSq_apply]
    simp only [add_re, UpperHalfPlane.coe_re, ofReal_re, add_im, UpperHalfPlane.coe_im, ofReal_im,
      add_zero]
    norm_cast at *

theorem auxbound2 (z : ℍ) (δ : ℝ) (n : ℤ) (h : n ≠ 0) : r z ≤ Complex.abs (δ * (z : ℂ) + n) := by
  rw [r, Complex.abs]
  have H1 :
    Real.sqrt (lowerBound1 z) ≤
      Real.sqrt
        ((δ * (z : ℂ).re + n) * (δ * (z : ℂ).re + n) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
    by
    rw [lowerBound1, Real.sqrt_le_sqrt_iff, ← pow_two, ← pow_two]
    apply auxlb z δ n h
    nlinarith
  simp only [ne_eq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, AbsoluteValue.coe_mk,
    MulHom.coe_mk, min_le_iff, normSq_apply] at *
  right
  simp only [add_re, mul_re, ofReal_re, UpperHalfPlane.coe_re, ofReal_im, UpperHalfPlane.coe_im,
    zero_mul, sub_zero, int_cast_re, add_im, mul_im, add_zero, int_cast_im] at *
  norm_cast

theorem bound1 (z : ℍ) (x : Fin 2 → ℤ) (k : ℤ) (hk : 0 ≤ k) :
    (r z ) ^ k ≤ Complex.abs (((z : ℂ) + (x 1 : ℂ) / (x 0 : ℂ)) ^ k) := by
  have := auxbound1 z (x 1 / x 0 : ℝ)
  lift k to ℕ using hk
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast] at *
  exact this

theorem bound2 (z : ℍ) (x : Fin 2 → ℤ) (k : ℤ) (hk : 0 ≤ k) :
    (r z ) ^ k ≤ Complex.abs (((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ k) := by
  have := auxbound2 z (x 0 / x 1 : ℝ) 1 one_ne_zero
  lift k to ℕ using hk
  simp only [zpow_coe_nat, map_pow, ge_iff_le]
  apply pow_le_pow_left (r_pos _).le
  simp only [ofReal_div, ofReal_int_cast, Int.cast_one] at *
  exact this

def upperHalfPlaneSlice (A B : ℝ) :=
  {z : ℍ | Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B}

theorem slice_mem (A B : ℝ) (z : ℍ) :
    z ∈ upperHalfPlaneSlice A B ↔ Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B := Iff.rfl

lemma compact_in_some_slice (K : Set ℍ) (hK : IsCompact K) : ∃  A B : ℝ, 0 < B ∧
    K ⊆ upperHalfPlaneSlice A B  := by
  by_cases hne : Set.Nonempty K
  · have hcts : ContinuousOn (fun t =>  t.im) K := by
       apply Continuous.continuousOn UpperHalfPlane.continuous_im
    obtain ⟨b, _, HB⟩ :=  IsCompact.exists_isMinOn hK hne hcts
    let t := (⟨Complex.I, by simp⟩ : ℍ)
    have  ht : UpperHalfPlane.im t = I.im := by rfl
    obtain ⟨r, _, hr2⟩ := Bornology.IsBounded.subset_closedBall_lt hK.isBounded 0 t
    refine' ⟨Real.sinh (r) + Complex.abs ((UpperHalfPlane.center t r)), b.im, _⟩
    constructor
    exact b.2
    intro z hz
    simp only [I_im, slice_mem, abs_ofReal, ge_iff_le] at *
    constructor
    have hr3 := hr2 hz
    simp  at hr3
    apply le_trans (abs_re_le_abs z)
    have := Complex.abs.sub_le (z : ℂ) (UpperHalfPlane.center t r) 0
    simp only [sub_zero, ge_iff_le] at this
    rw [dist_le_iff_dist_coe_center_le] at hr3
    apply le_trans this
    have htim : UpperHalfPlane.im t = 1 := by
      simp only [ht]
    rw [htim] at hr3
    simp only [one_mul, add_le_add_iff_right, ge_iff_le] at *
    exact hr3
    have hbz := HB  hz
    simp only [mem_setOf_eq, ge_iff_le] at *
    convert hbz
    rw [UpperHalfPlane.im]
    apply abs_eq_self.mpr z.2.le
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [empty_subset, and_true, exists_const]
    use 1
    linarith

@[simp]
lemma uhc (z : ℍ) : (z : ℂ) = z.1 := rfl

theorem r_lower_bound_on_slice (A B : ℝ) (h : 0 < B) (z : upperHalfPlaneSlice A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z.1 := by
  have zpos := UpperHalfPlane.im_pos z.1
  have hz := z.2
  rw [slice_mem] at hz
  simp only [abs_ofReal, ge_iff_le] at hz
  rw [r, r]
  apply min_le_min
  · dsimp only
    convert hz.2
    have := abs_eq_self.mpr zpos.le
    convert this.symm
  rw [Real.sqrt_le_sqrt_iff]
  have := aux4 (z : ℂ).re (z : ℂ).im zpos
  simp only [uhc, div_pow, one_div] at this
  simp_rw [lowerBound1]
  rw [this, aux4 A B h, one_div, inv_le_inv, add_le_add_iff_right, div_pow]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · apply (lowerBound1_pos z).le


variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

def unionEquiv (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ ι i) :
    (⋃ s : ℕ, ((ι s) : Set (ℤ × ℤ))) ≃ (ℤ × ℤ) where
  toFun x := x.1
  invFun x := by
    use x
    simp
    obtain ⟨i, hi1,_⟩:= HI ![x.1, x.2]
    refine ⟨i,hi1⟩
  left_inv := by  intro x; cases x; rfl
  right_inv := by intro x; rfl

theorem summable_disjoint_union_of_nonneg {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ x, Summable fun y : i x => f ⟨y,  Set.mem_iUnion_of_mem (x) y.2 ⟩) ∧
        Summable fun x => ∑' y : i x, f ⟨y, Set.mem_iUnion_of_mem (x) y.2 ⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : Summable f ↔ Summable (f ∘ h0) := by
   rw [Equiv.summable_iff]
  have h22 : ∀ y : Σ s : α, i s, 0 ≤ (f ∘ h0) y :=
    by
    intro y
    simp
    apply hf
  have h1 := summable_sigma_of_nonneg h22
  rw [←h01] at h1;
  convert h1

theorem disjoint_aux (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ In i) :
    ∀ i j : ℕ, i ≠ j → Disjoint (In i) (In j) :=
  by
  intro i j h
  intro x h1 h2 a h3
  have H0 := HI ![a.1, a.2]
  have := ExistsUnique.unique H0 (h1 h3) (h2 h3)
  simp at *
  exact h this

theorem summable_lemma (f : (Fin 2 → ℤ) → ℝ) (h : ∀ y : (Fin 2 → ℤ), 0 ≤ f y)
  (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : (Fin 2 → ℤ), ∃! i : ℕ, ⟨y 0, y 1⟩ ∈ ι i) :
    Summable f ↔ Summable fun n : ℕ => ∑ x in ι n, f ![x.1, x.2] := by
  let h2 := Equiv.trans (unionEquiv ι HI) (piFinTwoEquiv fun _ => ℤ).symm
  have h22 : ∀ y : ⋃ s : ℕ, (ι s), 0 ≤ (f ∘ h2) y := by
    intro y
    apply h
  have h3 := summable_disjoint_union_of_nonneg ?_ h22
  have h4 : Summable f ↔ Summable (f ∘ h2) := by rw [Equiv.summable_iff]
  rw [h4, h3]
  constructor
  intro H
  convert H.2
  rw [←Finset.tsum_subtype]
  rfl
  intro H
  constructor
  intro x
  simp only [Finset.coe_sort_coe, Equiv.coe_trans, Function.comp_apply]
  rw [unionEquiv]
  simp only [Equiv.coe_fn_mk]
  convert (Finset.summable (ι x) (f ∘ (piFinTwoEquiv fun _ => ℤ).symm))
  convert H
  rw [←Finset.tsum_subtype]
  rfl
  simpa using (disjoint_aux ι HI)

lemma summable_r_pow  (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
  Summable fun n : ℕ => 8 / (r z) ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ := by
  have hk : 1 < (k - 1 : ℝ) := by
    have : 1 < (k - 1 : ℤ) := by linarith
    norm_cast at *
  have riesum := Real.summable_nat_rpow_inv.2 hk
  have nze : (8 / (r z) ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    linarith
    norm_cast
    apply zpow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := r_pos z
    rw [HR] at this
    simp only [lt_self_iff_false] at this
  rw [← (summable_mul_left_iff nze).symm]
  simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at riesum
  convert riesum
  norm_cast

lemma summable_upper_bound (k : ℤ) (h : 3 ≤ k) (z : ℍ) :
 Summable fun (x : Fin 2 → ℤ) => (1/(r z)^k) * ((max (x 0).natAbs (x 1).natAbs : ℝ)^k)⁻¹ := by
  rw [summable_lemma _ _ (fun (n : ℕ) => square n)]
  have : ∀ n : ℕ, ∑ v in square n, (1/((r z)^k))*((max v.1.natAbs v.2.natAbs: ℝ)^k)⁻¹ =
     ∑ v in square n, (1/(r (z)^k))*((n : ℝ)^k)⁻¹ := by
     intro n
     apply Finset.sum_congr
     rfl
     intro x hx
     simp at hx
     congr
     norm_cast at *
  have hs : Summable (fun n : ℕ => ∑ v in square n, (1/(r z)^k) * ((n : ℝ)^k)⁻¹)  := by
    simp
    apply Summable.congr (summable_r_pow k z h)
    intro b
    by_cases b0 : b = 0
    rw [b0]
    have hk : (0: ℝ)^((k : ℤ)-1) = 0:= by
      rw [zero_zpow]
      linarith
    simp at *
    rw [hk]
    simp
    right
    have hk0 : 0 ≤ k := by linarith
    lift k to ℕ using hk0
    simp  [zpow_coe_nat, ne_eq, zero_pow_eq_zero, gt_iff_lt]
    linarith
    rw [square_size' b0]
    field_simp
    ring_nf
    simp_rw [mul_assoc]
    have hbb : (b : ℝ)^(-1 + (k : ℝ)) = (b : ℝ)⁻¹ * b^(k : ℝ) := by
      rw [Real.rpow_add]
      congr
      exact Real.rpow_neg_one ↑b
      simpa [pos_iff_ne_zero] using b0
    norm_cast at *
    rw [hbb]
    ring_nf
    simp
  apply Summable.congr hs
  intro b
  apply (this b).symm
  apply squares_cover_all'
  intro y
  apply mul_nonneg
  simp
  apply zpow_nonneg
  apply (r_pos z).le
  simp  [ge_iff_le, Nat.cast_le, Real.rpow_nat_cast, inv_nonneg, le_max_iff, Nat.cast_nonneg,
    or_self, zpow_nonneg]


lemma Eise_on_square_is_bounded_Case1 (k : ℤ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ) (hn : 1 ≤ n) (hk : 0 ≤ k)
  (C1 :Complex.abs (x 0 : ℂ) = n) : (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs ((r z) ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  lift k to ℕ using hk
  rw [inv_le_inv]
  have h0 : (x 0 : ℂ) ≠ 0 := by
    intro hx
    rw [hx] at C1
    simp only [map_zero, Int.cast_eq_zero] at *
    norm_cast at *
    simp_rw [← C1] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    ((x 0 : ℂ) ^ (k : ℤ)) * ((z : ℂ) + (x 1 : ℂ) / x 0) ^ (k : ℤ) :=
    by
    field_simp
    ring
  rw [h1]
  simp_rw [map_mul Complex.abs]
  norm_cast at *
  have h3 : Complex.abs (n^k : ℕ) = Complex.abs ((x 0)^k : ℤ) := by
    have : Complex.abs ((x 0)^k : ℤ) = Complex.abs (x 0)^k := by
      simp only [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C1]
    norm_cast
    simp only [Nat.cast_pow, map_pow, abs_natCast]
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Complex.abs.nonneg _)
  have := bound1 z x k (Nat.cast_nonneg k)
  simp only [zpow_coe_nat, uhc, map_pow] at this
  norm_cast at *
  convert this
  apply abs_eq_self.mpr ( pow_nonneg (r_pos z).le k)
  rw [Complex.abs_pow]
  rfl
  apply Complex.abs.pos (pow_linear_ne_zero' _ _ _ _ _)
  intro hx
  rw [hx] at C1
  simp [Int.cast_zero] at C1
  norm_cast at C1
  rw [← C1] at hn
  simp only [Nat.one_ne_zero, le_zero_iff] at hn
  apply r_mul_n_pos k z n hn

lemma Eise_on_square_is_bounded_Case2 (k : ℤ) (z : ℍ) (n : ℕ) (x : Fin 2 → ℤ) (hn : 1 ≤ n)
  (hk : 0 ≤ k) (C2 : Complex.abs (x 1 : ℂ) = n) :
    (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ (k : ℤ)))⁻¹ ≤
      (Complex.abs ((r z) ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
  lift k to ℕ using hk
  rw [inv_le_inv]
  have h0 : (x 1 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C2
    simp at C2
    norm_cast at *
    rw [← C2] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  have h1 : ((x 0) * ↑z + (x 1)) ^ (k : ℤ) =
    (x 1 : ℂ)^ (k) * ((x 0 : ℂ) / (x 1 : ℂ) * (z : ℂ) + 1) ^ (k) := by
    field_simp
    ring_nf
  rw [h1]
  simp_rw [map_mul Complex.abs]
  have h3 : Complex.abs (n^k ) = Complex.abs ((x 1)^k ) := by
    have : Complex.abs ((x 1)^k) = Complex.abs (x 1)^k := by
      simp  [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C2]
    norm_cast
    simp [Nat.cast_pow, map_pow, abs_natCast]
  simp at *
  norm_cast at *
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left
  have := bound2 z x k
  simp at *
  norm_cast at *
  convert this
  apply abs_eq_self.mpr (  (r_pos z).le )
  norm_cast
  simp  [ge_iff_le, map_nonneg, zpow_nonneg]
  apply Complex.abs.pos (pow_linear_ne_zero'' _ _ _ _ _)
  have h0 : (x 1 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C2
    simp at C2
    norm_cast at *
    rw [← C2] at hn
    simp only [Nat.one_ne_zero, le_zero_iff] at hn
  norm_cast at *
  apply r_mul_n_pos k z n hn

theorem Eise_on_square_is_bounded2 (k : ℤ) (hk : 1 ≤ k) (z : ℍ) (n : ℕ)
  (x : Fin 2 → ℤ) (hx : ⟨x 0, x 1⟩ ∈ square n) :
  (Complex.abs (((x 0 : ℂ) * z + (x 1 : ℂ)) ^ k))⁻¹ ≤ (Complex.abs ((r z) ^ k * n ^ k))⁻¹ := by
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  by_cases hn : n = 0
  · rw [hn] at hx
    simp at hx
    rw [hx.1, hx.2]
    have h1 : (0 : ℝ) ^ (k : ℕ) = 0 := by
      simp [cpow_nat_cast, ne_eq, zero_pow_eq_zero]
      linarith
    simp [hn, h1]
  · have hnn : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
    by_cases C1 : Complex.abs (x 0 : ℂ) = n
    apply Eise_on_square_is_bounded_Case1 k z n x hnn (Int.ofNat_nonneg k) C1
    have C2 := Complex_abs_square_left_ne n ⟨x 0, x 1⟩ hx C1
    apply Eise_on_square_is_bounded_Case2 k z n x hnn (Int.ofNat_nonneg k) C2

lemma  eisensteinSeries_TendstoLocallyUniformlyOn  (k : ℤ) (hk : 3 ≤ k) (N : ℕ)
  (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
    (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) )
    ( fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) Filter.atTop ⊤ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact, eisensteinSeries_SIF]
  simp [eisensteinSeries]
  intros K hK
  obtain ⟨A,B,hB, HABK⟩:= compact_in_some_slice K hK
  let u :=  fun x : (gammaSet N a )  =>
    (1/((r  ⟨⟨A, B⟩, hB⟩)^k))* ( (max (x.1 0).natAbs (x.1 1).natAbs : ℝ)^k)⁻¹
  have hu : Summable u := by
    have := Summable.subtype (summable_upper_bound k hk  ⟨⟨A, B⟩, hB⟩) (gammaSet N a )
    apply this.congr
    intro v
    simp
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  have hkgt1 : 1 ≤ k := by linarith
  have sq := square_mem (max (((piFinTwoEquiv fun _ => ℤ).1 v).1).natAbs
  (((piFinTwoEquiv fun _ => ℤ).1 v).2).natAbs ) ⟨(v.1 0), v.1 1⟩
  simp at sq
  have hk0 : 0 ≤ k := by linarith
  have := Eise_on_square_is_bounded2 k hkgt1 x (max (v.1 0).natAbs (v.1 1).natAbs ) v
  simp  at this
  rw [eisSummand]
  simp
  apply le_trans (this sq)
  rw [mul_comm]
  apply mul_le_mul
  rw [inv_le_inv]
  lift k to ℕ using hk0
  apply pow_le_pow_left
  apply (r_pos _).le
  rw [abs_of_pos (r_pos _)]
  exact r_lower_bound_on_slice A B hB ⟨x, HABK hx⟩
  lift k to ℕ using hk0
  apply pow_pos
  simpa only [abs_pos, ne_eq] using (r_ne_zero x)
  lift k to ℕ using hk0
  apply pow_pos (r_pos _)
  rfl
  simp only [ge_iff_le, Nat.cast_le, inv_nonneg, le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]
  simp only [inv_nonneg, ge_iff_le]
  apply zpow_nonneg (r_pos _).le
  simp only [top_eq_univ, isOpen_univ]
