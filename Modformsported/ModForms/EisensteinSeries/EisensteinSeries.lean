import Modformsported.ModForms.EisensteinSeries.EisensteinSeriesIndexLemmas
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Geometry.Manifold.Mfderiv
import Mathlib.Analysis.Calculus.Deriv.Zpow
import Mathlib.Tactic.Default

#align_import mod_forms.Eisenstein_Series.Eisenstein_series

universe u v w

open Complex

open scoped BigOperators NNReal Classical Filter UpperHalfPlane

open ModularForm

open SlashInvariantForm

local notation "SL2Z" => Matrix.SpecialLinearGroup (Fin 2) ℤ

noncomputable section

local notation "ℍ'" =>
  (⟨UpperHalfPlane.upperHalfSpace, upper_half_plane_isOpen⟩ : TopologicalSpace.Opens ℂ)

/-! ### Eisenstein series -/


namespace EisensteinSeries

/-- The function on `ℤ × ℤ` whose sum defines an Eisenstein series.-/
def eise (k : ℤ) (z : ℍ) : ℤ × ℤ → ℂ := fun x => 1 / (x.1 * z + x.2) ^ k

/-
def Eisen (k : ℤ) (x : ℤ × ℤ) : C(ℍ, ℂ) :=
⟨λ z, 1/(x.1*z+x.2)^k, by {simp,  sorry}⟩
-/
instance : TopologicalSpace C(ℍ, ℂ) :=
  inferInstance

def eise' (k : ℤ) (z : ℂ) : ℤ × ℤ → ℂ := fun x => 1 / (x.1 * z + x.2) ^ k

def realEise (k : ℤ) (z : ℍ) : ℤ × ℤ → ℝ := fun x => Complex.abs (1 / (x.1 * z + x.2) ^ k)

def eiseDeriv (k : ℤ) (z : ℂ) : ℤ × ℤ → ℂ := fun x => -k * x.1 / (x.1 * z + x.2) ^ (k + 1)

/-- The Eisenstein series of weight `k : ℤ` -/
def eisensteinSeriesOfWeight_ (k : ℤ) : ℍ → ℂ := fun z => ∑' x : ℤ × ℤ, eise k z x

def realEisensteinSeriesOfWeight_ (k : ℤ) : ℍ → ℝ := fun z => ∑' x : ℤ × ℤ, realEise k z x

def eisensteinDerivWeight (k : ℤ) : ℍ → ℂ := fun z => ∑' x : ℤ × ℤ, eiseDeriv k z x

/-
lemma summable2 (k : ℤ) (h: 3 ≤ k) : summable (Eisen k):=
begin
  sorry,
end


def Eisenstein_series_of_weight_' (k: ℤ) : C(ℍ, ℂ):=
 ∑' (x : ℤ × ℤ), Eisen k x
-/
theorem eise_is_nonneg (k : ℤ) (z : ℍ) (y : ℤ × ℤ) : 0 ≤ abs (eise k z y) := by
  apply complex.abs.nonneg

theorem calc_lem (k : ℤ) (a b c d i1 i2 : ℂ) (z : ℍ) (h : c * z + d ≠ 0) :
    ((i1 * ((a * z + b) / (c * z + d)) + i2) ^ k)⁻¹ =
      (c * z + d) ^ k * (((i1 * a + i2 * c) * z + (i1 * b + i2 * d)) ^ k)⁻¹ :=
  by
  have h1 : i1 * ((a * z + b) / (c * z + d)) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h1]
  have h2 : i1 * (a * z + b) / (c * z + d) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h2]
  have h3 := div_add' (i1 * (a * z + b)) i2 (c * z + d) h
  rw [h3]
  simp only [div_zpow, inv_div]
  rw [div_eq_inv_mul, mul_comm]
  have h5 : (c * z + d) ^ k ≠ 0 := by apply zpow_ne_zero _ h
  apply congr_arg fun b : ℂ => (c * z + d) ^ k * b⁻¹
  ring_nf

theorem coe_chain (A : SL2Z) (i j : Fin 2) :
    (A.1 i j : ℂ) = ((A.1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ) :=
  by
  simp
  rw [← coe_coe]
  fin_cases i <;> fin_cases j
  all_goals
    simp [coe_coe]
    norm_cast

-- How the Eise function changes under the Moebius action
theorem eise_moeb (k : ℤ) (z : ℍ) (A : SL2Z) (i : ℤ × ℤ) :
    eise k ((A : Matrix.GLPos (Fin 2) ℝ) • z) i =
      (A.1 1 0 * z + A.1 1 1) ^ k * eise k z (indEquiv A i) :=
  by
  rw [Eise]
  rw [Eise]
  simp [coeFn_coe_base']
  dsimp
  rw [calc_lem]
  have h1 := coe_chain A
  simp only [Subtype.val_eq_coe] at h1 
  rw [h1]
  rw [h1]
  rw [← coe_coe]
  apply UpperHalfPlane.denom_ne_zero A

def eisensteinIsSlashInv (Γ : Subgroup SL2Z) (k : ℤ) : SlashInvariantForm Γ k
    where
  toFun := eisensteinSeriesOfWeight_ k
  slash_action_eq' := by
    intro A
    ext1
    simp_rw [slash_action_eq'_iff]
    rw [Eisenstein_series_of_weight_]
    simp only [Set.mem_setOf_eq]
    simp
    have h1 := Eise_moeb k x A
    have h2 := tsum_congr h1
    convert h2
    simp only [Subtype.val_eq_coe]
    have h3 := Equiv.tsum_eq (Ind_equiv A) (Eise k x)
    rw [tsum_mul_left]
    rw [h3]

/-
begin
rw modular_forms.wmodular_mem',
rw Eisenstein_series_of_weight_,
simp only [set.mem_set_of_eq],
intros A z,
have h1:= Eise_moeb k z A,
have h2:=tsum_congr h1,
convert h2,
simp only [subtype.val_eq_coe],
have h3:=equiv.tsum_eq (Ind_equiv A) (Eise k z),
rw tsum_mul_left,
rw h3,
simp,
end

-/
theorem Eise_on_square_is_bounded (k : ℕ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (h : x ∈ square n)
    (hn : 1 ≤ n) :
    (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤ (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  by_cases C1 : Complex.abs (x.1 : ℂ) = n
  rw [inv_le_inv]
  have h0 : (x.1 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C1 
    simp [Int.cast_zero] at C1 
    norm_cast at C1 
    rw [← C1] at hn 
    simp only [Nat.one_ne_zero, le_zero_iff] at hn 
    exact hn
  have h1 : (↑x.fst * ↑z + ↑x.snd) ^ k = ↑x.fst ^ k * ((z : ℂ) + (x.2 : ℂ) / ↑x.fst) ^ k :=
    by
    rw [← mul_pow]
    rw [div_eq_mul_inv]
    have :
      (x.fst : ℂ) * ((z : ℂ) + (x.snd : ℂ) * (x.fst : ℂ)⁻¹) = (x.fst : ℂ) * (z : ℂ) + (x.snd : ℂ) :=
      by
      have p1 :
        (x.fst : ℂ) * ((z : ℂ) + (x.snd : ℂ) * (x.fst : ℂ)⁻¹) =
          (x.fst : ℂ) * (z : ℂ) + (x.fst : ℂ) * (x.fst : ℂ)⁻¹ * (x.snd : ℂ)
      ring_nf
      rw [mul_inv_cancel] at p1 
      simp only [one_mul] at p1 
      rw [p1]
      exact h0
    rw [this]
  rw [h1]
  simp_rw [map_mul Complex.abs]
  have h3 : Complex.abs (↑x.fst ^ k) = Complex.abs ↑x.fst ^ k := by apply Complex.abs_pow
  rw [h3]
  rw [C1]
  have h4 : Complex.abs (↑n ^ k) = ↑n ^ k := by norm_cast
  rw [h4]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left
  have := auxlem2 z n x h k
  apply this; norm_cast
  simp only [zero_le']
  simp only [complex.abs.pos, Ne.def]
  have hh : (x.fst : ℂ) * (z : ℂ) + (x.snd : ℂ) ≠ 0 :=
    by
    intro H
    have H1 : x.1 = 0 ∨ (z : ℂ).im = 0 := by simpa using congr_arg Complex.im H
    cases H1;
    · rw [H1] at C1 ; simp only [Int.cast_zero, abs_zero] at C1 
      norm_cast at C1 
      rw [← C1] at hn 
      simp only [Nat.one_ne_zero, square_mem, le_zero_iff] at *
      exact hn
    have HH := z.property
    simp only [Subtype.val_eq_coe] at HH 
    rw [H1] at HH 
    simp at HH 
    exact HH
  apply complex.abs.pos
  apply pow_ne_zero
  exact hh
  rw [map_mul Complex.abs]
  apply mul_pos
  apply complex.abs.pos
  apply pow_ne_zero
  have := rfunct_pos z
  norm_cast
  intro np
  rw [np] at this 
  simp only [lt_self_iff_false] at this 
  exact this
  apply complex.abs.pos
  apply pow_ne_zero
  norm_cast
  intro Hn
  rw [Hn] at hn 
  simp only [Nat.one_ne_zero, le_zero_iff] at hn 
  exact hn
  have C2 : Complex.abs (x.2 : ℂ) = n :=
    by
    simp only [square_mem] at h 
    have := max_aux'' x.1.natAbs x.2.natAbs n h
    norm_cast
    cases this
    by_contra
    norm_cast at C1 
    rw [← this] at C1 
    rw [Int.abs_eq_natAbs] at C1 
    simp only [eq_self_iff_true, not_true] at C1 
    exact C1
    rw [← this]
    rw [Int.abs_eq_natAbs]
  rw [inv_le_inv]
  have h0 : (x.2 : ℂ) ≠ 0 := by
    norm_cast
    intro hx
    rw [hx] at C2 
    simp only [Int.cast_zero, abs_zero] at C2 
    norm_cast at C2 
    rw [← C2] at hn 
    simp only [Nat.one_ne_zero, le_zero_iff] at hn 
    exact hn
  have h1 : (↑x.fst * ↑z + ↑x.snd) ^ k = ↑x.snd ^ k * ((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ k :=
    by
    rw [← mul_pow]; simp only
    rw [div_eq_mul_inv]
    have :
      (x.snd : ℂ) * ((x.fst : ℂ) * (x.snd : ℂ)⁻¹ * (z : ℂ) + 1) =
        (x.snd : ℂ) * (x.snd : ℂ)⁻¹ * (x.fst : ℂ) * (z : ℂ) + (x.snd : ℂ) :=
      by ring
    rw [this]
    rw [mul_inv_cancel]
    simp only [one_mul]
    exact h0
  rw [h1]
  rw [map_mul Complex.abs]
  rw [map_mul Complex.abs]
  have h3 : Complex.abs (↑x.2 ^ k) = Complex.abs ↑x.2 ^ k := by apply Complex.abs_pow
  rw [h3]
  rw [C2]
  have h4 : Complex.abs (↑n ^ k) = ↑n ^ k := by norm_cast
  rw [h4]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left
  have := auxlem3 z n x h k
  apply this
  norm_cast
  simp only [zero_le']
  have hh : (x.fst : ℂ) * (z : ℂ) + (x.snd : ℂ) ≠ 0 :=
    by
    intro H
    have H1 : x.1 = 0 ∨ (z : ℂ).im = 0 := by simpa using congr_arg Complex.im H
    cases H1
    · rw [H1] at H 
      simp only [Int.cast_eq_zero, Int.cast_zero, MulZeroClass.zero_mul, zero_add] at H 
      rw [H] at C2 
      simp only [Int.cast_zero, abs_zero] at C2 
      norm_cast at C2 
      rw [← C2] at hn 
      simp only [Nat.one_ne_zero, square_mem, le_zero_iff] at *
      exact hn
    have HH := z.property; simp only [Subtype.val_eq_coe] at HH 
    rw [H1] at HH ; simp only [lt_self_iff_false] at HH 
    exact HH
  apply complex.abs.pos
  apply pow_ne_zero
  exact hh
  rw [map_mul Complex.abs]
  apply mul_pos
  apply complex.abs.pos
  apply pow_ne_zero
  have := rfunct_pos z
  norm_cast
  intro np
  rw [np] at this 
  simp only [lt_self_iff_false] at this 
  exact this
  apply complex.abs.pos
  apply pow_ne_zero
  norm_cast
  intro Hn
  rw [Hn] at hn 
  simp only [Nat.one_ne_zero, le_zero_iff] at hn 
  exact hn

theorem Eise_on_square_is_bounded' (k : ℕ) (z : ℍ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : ℤ × ℤ,
      x ∈ square n →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  intro x hx
  apply Eise_on_square_is_bounded k z n x hx hn

theorem Eise_on_zero_square (k : ℕ) (z : ℍ) (h : 1 ≤ k) :
    ∀ x : ℤ × ℤ,
      x ∈ square 0 →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * 0 ^ k))⁻¹ :=
  by
  intro x hx
  rw [Square_zero] at hx 
  simp only [Finset.mem_singleton] at hx 
  simp_rw [hx]
  simp only [add_zero, Int.cast_zero, MulZeroClass.zero_mul, map_mul Complex.abs]
  have h1 : (0 : ℂ) ^ k = 0 := by rw [zero_pow_eq_zero]; linarith
  rw [h1]
  simp

theorem Eise_on_square_is_bounded'' (k : ℕ) (z : ℍ) (n : ℕ) (hn : 1 ≤ k) :
    ∀ x : ℤ × ℤ,
      x ∈ square n →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  by_cases h0 : n = 0
  · rw [h0]; have := Eise_on_zero_Square k z hn; simp at *; apply this
  have Hn : 1 ≤ n := by
    have := Nat.pos_of_ne_zero h0
    linarith
  intro x hx
  apply Eise_on_square_is_bounded k z n x hx Hn

theorem natpowsinv (x : ℝ) (n : ℤ) (h2 : x ≠ 0) : (x ^ (n - 1))⁻¹ = (x ^ n)⁻¹ * x :=
  by
  have := zpow_sub_one₀ h2 n
  rw [this]
  have h3 := mul_zpow (x ^ n) x⁻¹ (-1)
  simp at *
  exact h3

--Sum over squares is bounded
theorem BigClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    ∀ n : ℕ, ∑ y : ℤ × ℤ in square n, (realEise k z) y ≤ 8 / rfunct z ^ k * (n ^ ((k : ℤ) - 1))⁻¹ :=
  by
  intro n
  rw [real_Eise]
  simp [one_div, Complex.abs_pow, abs_inv, zpow_ofNat]
  have k0 : 1 ≤ k := by linarith
  have BO := Eise_on_square_is_bounded'' (k : ℕ) (z : ℍ) (n : ℕ) k0
  by_cases n0 : n = 0
  · rw [n0]
    rw [Square_zero]
    simp only [add_zero, Int.cast_zero, Nat.cast_zero, MulZeroClass.zero_mul, Finset.sum_singleton]
    have H0 : (0 : ℂ) ^ k = 0 := by rw [zero_pow_eq_zero]; linarith
    simp [abs_zero, inv_zero]
    have H00 : (0 : ℝ) ^ ((k : ℤ) - 1) = 0 := by rw [zero_zpow]; linarith
    rw [H00]
    simp [inv_zero, MulZeroClass.mul_zero]; norm_cast at *; rw [H0]
  have := Finset.sum_le_sum BO
  simp only [Finset.sum_const, map_mul Complex.abs, nsmul_eq_mul] at this 
  rw [Square_size n] at this 
  norm_cast at this 
  have ne :
    (8 * n * (Complex.abs (rfunct z ^ k) * (n ^ k : ℝ))⁻¹ : ℝ) =
      8 / rfunct z ^ k * (n ^ ((k : ℤ) - 1))⁻¹ :=
    by
    rw [Complex.abs_pow]
    rw [Complex.abs_of_nonneg]
    rw [← mul_pow]
    rw [div_eq_inv_mul]
    have : 8 * ↑n * ((rfunct z * ↑n) ^ k)⁻¹ = 8 * (rfunct z ^ k)⁻¹ * (↑n ^ ((k : ℤ) - 1))⁻¹ :=
      by
      have dis : ((rfunct z * ↑n) ^ k)⁻¹ = (rfunct z ^ k)⁻¹ * (↑n ^ k)⁻¹ :=
        by
        rw [mul_pow]
        simp_rw [← zpow_neg_one]
        simp_rw [← mul_zpow]
      simp [dis]
      rw [natpowsinv]
      ring
      norm_cast
      intro hN
      rw [hN] at n0 
      simp only [eq_self_iff_true, not_true] at n0 
      exact n0
    rw [this]
    ring
    have rpos := rfunct_pos z
    apply le_of_lt rpos
  norm_cast at ne 
  rw [Ne] at this 
  norm_cast
  simp at *
  apply this
  have hhh := Nat.pos_of_ne_zero n0
  linarith

theorem SmallClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    ∀ n : ℕ,
      (fun x : ℕ => ∑ y : ℤ × ℤ in square x, (realEise k z) y) n ≤
        8 / rfunct z ^ k * (rie (k - 1)) n :=
  by
  have BIGCLAIM := BigClaim k z h
  simp only at BIGCLAIM 
  rw [rie]
  simp only [one_div]
  intro n
  have tr : ((↑n ^ ((k : ℤ) - 1))⁻¹ : ℝ) = ((↑n ^ ((k : ℝ) - 1))⁻¹ : ℝ) :=
    by
    simp [inv_inj]
    have := realpow n k
    rw [← this]
    simp [Int.cast_ofNat, Int.cast_one, Int.cast_sub]
  rw [← tr]
  apply BIGCLAIM n

theorem real_eise_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k) : Summable (realEise k z) :=
  by
  let In := Square
  have HI := Squares_cover_all
  let g := fun y : ℤ × ℤ => (real_Eise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by simp_rw [g]; intro y; rw [real_Eise]; simp
  have index_lem := sum_lemma g gpos In HI
  rw [index_lem]
  let e := fun x : ℕ => ∑ y : ℤ × ℤ in In x, g y
  have BIGCLAIM : ∀ n : ℕ, ∑ y : ℤ × ℤ in In n, g y ≤ 8 / rfunct z ^ k * (n ^ ((k : ℤ) - 1))⁻¹ :=
    by
    simp_rw [g]
    apply BigClaim k z h
  have smallerclaim : ∀ n : ℕ, e n ≤ 8 / rfunct z ^ k * (rie (k - 1)) n :=
    by
    simp_rw [e]
    apply SmallClaim k z h
  have epos : ∀ x : ℕ, 0 ≤ e x := by
    simp_rw [e]; simp_rw [g]; intro x
    apply Finset.sum_nonneg; intro i hi; apply complex.abs.nonneg
  have hk : 1 < (k - 1 : ℤ) := by linarith
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    apply pow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := rfunct_pos z
    rw [HR] at this 
    simp only [lt_self_iff_false] at this 
    exact this
  have riesum := int_RZ_is_summmable (k - 1) hk
  have riesum' : Summable fun n : ℕ => 8 / rfunct z ^ k * rie (↑k - 1) n :=
    by
    rw [← (summable_mul_left_iff nze).symm]
    simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at riesum 
    apply riesum
  have := summable_of_nonneg_of_le epos smallerclaim
  apply this
  apply riesum'

theorem Real_Eisenstein_bound (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    realEisensteinSeriesOfWeight_ k z ≤ 8 / rfunct z ^ k * rZ (k - 1) :=
  by
  rw [real_Eisenstein_series_of_weight_, rZ, ← tsum_mul_left]
  let In := Square
  have HI := Squares_cover_all
  let g := fun y : ℤ × ℤ => (real_Eise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by simp_rw [g]; intro y; rw [real_Eise]; simp
  have hgsumm : Summable g := by simp_rw [g]; apply real_eise_is_summable k z h
  have index_lem := tsum_lemma g In HI hgsumm
  simp_rw [g] at index_lem 
  simp
  rw [index_lem]
  have ind_lem2 := sum_lemma g gpos In HI
  have smallclaim := SmallClaim k z h
  have hk : 1 < (k - 1 : ℤ) := by linarith
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero; simp; apply pow_ne_zero
    simp; by_contra HR
    have := rfunct_pos z
    rw [HR] at this 
    simp at this 
    exact this
  have riesum := int_RZ_is_summmable (k - 1) hk
  have riesum' : Summable fun n : ℕ => 8 / rfunct z ^ k * rie (↑k - 1) n :=
    by
    rw [← (summable_mul_left_iff nze).symm]
    simp at riesum 
    apply riesum
  apply tsum_le_tsum
  apply smallclaim
  simp_rw [g] at ind_lem2 
  rw [← ind_lem2]
  simp_rw [g] at hgsumm 
  apply hgsumm
  apply riesum'

theorem Eisenstein_series_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k) : Summable (eise k z) :=
  by
  let f := Eise k z
  have sum_Eq : (Summable fun x => abs (f x)) → Summable f := by
    apply summable_if_complex_abs_summable
  apply sum_Eq
  simp_rw [f]
  have := real_eise_is_summable k z h
  rw [real_Eise] at this 
  exact this

/-- The sum of Eise over the `Square`'s-/
def eisenSquare (k : ℤ) (n : ℕ) : ℍ → ℂ := fun z => ∑ x in square n, eise k z x

theorem Eisenstein_series_is_sum_eisen_squares (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    eisensteinSeriesOfWeight_ k z = ∑' n : ℕ, eisenSquare k n z :=
  by
  rw [Eisenstein_series_of_weight_]; simp_rw [eisen_square]
  have HI := Squares_cover_all
  let g := fun y : ℤ × ℤ => (Eise k z) y
  have hgsumm : Summable g := by simp_rw [g]; apply Eisenstein_series_is_summable k z h
  have index_lem := tsum_lemma' g Square HI hgsumm; simp_rw [g] at index_lem ; exact index_lem

def eisenPartialSums (k : ℤ) (n : ℕ) : ℍ → ℂ := fun z => ∑ x in Finset.range n, eisenSquare k x z

def upperHalfSpaceSlice (A B : ℝ) :=
  {z : ℍ' | Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B}

instance upperHalfSpaceSliceToUhs (A B : ℝ) : Coe (upperHalfSpaceSlice A B) ℍ :=
  ⟨fun z => z.1⟩

@[simp]
theorem slice_mem (A B : ℝ) (z : ℍ) :
    z ∈ upperHalfSpaceSlice A B ↔ Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B :=
  Iff.rfl

theorem slice_in_upper_half (A B : ℝ) (x : upperHalfSpaceSlice A B) : x.1.1 ∈ ℍ'.1 :=
  by
  have hx : 0 < x.1.1.im := by apply UpperHalfPlane.im_pos
  simp at hx 
  simp
  apply hx

theorem ball_in_upper_half (z : ℍ') (A B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (hBε : ε < B)
    (h : Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B) : Metric.closedBall z.1 ε ⊆ ℍ'.1 :=
  by
  intro x hx
  simp at *
  have hg : 0 < x.2 := by
    rw [Metric.closedBall] at h 
    have hz : z ∈ upper_half_space_slice A B := by apply h; simp [hε.le]
    simp at hz 
    have hz2 := z.2
    have hzB : B ≤ Complex.abs z.1.2 := by simp [hz.2]
    rw [dist_eq_norm] at hx 
    simp at hx 
    have h3 := le_trans (abs_im_le_abs (x - z.1)) hx
    have h4 := _root_.abs_sub_le z.1.2 x.2 0
    rw [sub_im] at h3 
    rw [_root_.abs_sub_comm] at h3 
    have h33 : -ε ≤ -|z.1.im - x.im| := by simp; apply h3
    simp at h4 
    have h5 : |z.1.im| - |z.1.im - x.im| ≤ |x.im| := by simp; linarith
    simp at hzB 
    have h6 : B - ε ≤ |z.1.im| - |z.1.im - x.im| := by simp at *; linarith
    by_contra hc
    simp at hc 
    have hcc : 0 ≤ -x.im := by linarith
    have hzc : |z.1.im - x.im| = z.1.im - x.im :=
      by
      apply _root_.abs_of_nonneg; apply add_nonneg
      have := UpperHalfPlane.im_pos z
      apply this.le; apply hcc
    have hzp : |z.1.im| = z.1.im := by apply _root_.abs_of_nonneg (UpperHalfPlane.im_pos z).le
    simp_rw [hzc, hzp] at h6 
    simp only [sub_sub_cancel] at h6 
    linarith
  apply hg

theorem closedBall_in_slice (z : ℍ') :
    ∃ A B ε : ℝ, 0 < ε ∧ 0 < B ∧ Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧ 0 ≤ A ∧ ε < B :=
  by
  let e := 3⁻¹ * Complex.abs z.1.2
  let a := Complex.abs z.1.2 + Complex.abs z
  let b := Complex.abs z.1.2 - e
  use a
  use b
  use e
  constructor
  simp_rw [e]
  simp
  apply UpperHalfPlane.im_ne_zero z
  constructor
  simp_rw [b]
  simp_rw [e]
  ring_nf
  simp only [abs_of_real, UpperHalfPlane.coe_im, Subtype.val_eq_coe]
  apply mul_pos
  nlinarith
  simp
  apply UpperHalfPlane.im_ne_zero z
  constructor
  intro x
  simp only [abs_of_real, tsub_le_iff_right, ge_iff_le, Metric.mem_closedBall, slice_mem,
    UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re]
  intro hxz
  have d1 : dist x z = dist (x : ℂ) (z : ℂ) := Subtype.dist_eq x z
  rw [d1] at hxz 
  rw [dist_eq_norm] at hxz 
  simp only [norm_eq_abs] at hxz 
  have := complex.abs.sub_le (x : ℂ) (z : ℂ) 0
  simp only [sub_zero, Subtype.val_eq_coe] at this 
  constructor
  simp_rw [a]
  have hre := le_trans (abs_re_le_abs x.1) this
  rw [UpperHalfPlane.re]
  simp only [abs_of_real, UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re] at *
  apply le_trans hre
  simp only [add_le_add_iff_right]
  apply le_trans hxz
  simp_rw [e]
  rw [UpperHalfPlane.im]
  simp only [abs_of_real, UpperHalfPlane.coe_im, Subtype.val_eq_coe]
  have hxim : 0 ≤ |UpperHalfPlane.im z| := by apply _root_.abs_nonneg
  ring_nf
  linarith
  have ineq1 := _root_.abs_sub_le z.1.2 x.1.2 0
  simp only [sub_zero, UpperHalfPlane.coe_im, Subtype.val_eq_coe] at ineq1 
  apply le_trans ineq1
  rw [add_comm]
  simp only [add_le_add_iff_left]
  have ki := le_trans (abs_im_le_abs (x.1 - z.1)) hxz
  rw [sub_im] at ki 
  rw [_root_.abs_sub_comm] at ki 
  convert ki
  simp_rw [a]
  constructor
  apply add_nonneg
  apply complex.abs.nonneg
  apply complex.abs.nonneg
  simp_rw [b]
  simp_rw [e]
  ring_nf
  rw [← sub_pos]
  have hr : 0 < Complex.abs z.1.im := by simp; apply UpperHalfPlane.im_ne_zero z
  linarith

/-- Canonical point in the `A B` slice-/
def lbpoint (A B : ℝ) (h : 0 < B) : ℍ :=
  ⟨⟨A, B⟩, by simp; exact h⟩

theorem aux55 (a b : ℝ) (h : a ≠ 0) : a / (a + b) = 1 / (b / a + 1) :=
  by
  have : b / a + 1 = (b + a) / a := by ring_nf; simp [h]
  rw [this]
  simp
  rw [add_comm]

theorem aux4 (a b : ℝ) (h : 0 < b) :
    (b ^ 4 + (a * b) ^ 2) / (a ^ 2 + b ^ 2) ^ 2 = 1 / ((a / b) ^ 2 + 1) :=
  by
  have h1 : (a ^ 2 + b ^ 2) ^ 2 = (a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2) := by ring
  rw [h1]
  have h2 : b ^ 4 + (a * b) ^ 2 = b ^ 2 * (a ^ 2 + b ^ 2) := by ring
  rw [h2]
  rw [mul_div_assoc]
  simp only [one_div, div_pow, div_self_mul_self']
  field_simp
  have hb : b ^ 2 ≠ 0 := by simp [h]; intro h3; linarith
  have := aux55 (b ^ 2) (a ^ 2) hb
  rw [add_comm]
  exact this

theorem aux5 (a b : ℝ) : 0 < a ^ 2 / b ^ 2 + 1 :=
  by
  have h1 : 0 ≤ a ^ 2 / b ^ 2 := by apply div_nonneg; nlinarith; nlinarith
  linarith

theorem aux6 (a b : ℝ) (h : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b → a ^ 2 ≤ b ^ 2 :=
  by
  intro hab
  nlinarith

theorem hcoe : UpperHalfPlane.upperHalfSpace = coe '' (Set.univ : Set UpperHalfPlane) := by simp;
  rfl

theorem rfunct_lower_bound_on_slice (A B : ℝ) (h : 0 < B) (z : upperHalfSpaceSlice A B) :
    rfunct (lbpoint A B h) ≤ rfunct z.1 := by
  simp at *
  simp_rw [rfunct]
  simp_rw [lbpoint]
  simp only [min_le_iff, le_min_iff, Subtype.val_eq_coe]
  cases z
  have zpos := UpperHalfPlane.im_pos z_val
  cases z_property
  cases z_val
  dsimp at *
  simp at *
  fconstructor
  simp_rw [lb]
  rw [Real.sqrt_le_sqrt_iff]
  have h1 : B ^ 2 ≤ Complex.abs z_val_val.im ^ 2 := by norm_cast; nlinarith
  norm_cast at h1 
  rw [_root_.sq_abs] at h1 
  simp [h1]
  nlinarith
  simp_rw [lb]
  rw [Real.sqrt_le_sqrt_iff]
  rw [Real.sqrt_le_sqrt_iff]
  rw [aux4]
  rw [aux4]
  simp
  rw [inv_le_inv]
  simp
  simp_rw [hcoe] at z_val_property 
  simp at z_val_property 
  have i1 : ((z_val_val.im ^ 2)⁻¹ : ℝ) ≤ ((B ^ 2)⁻¹ : ℝ) :=
    by
    rw [inv_le_inv]
    have h' : 0 ≤ B := by linarith
    have z_prop' : 0 ≤ z_val_val.im := by apply zpos.le
    apply aux6 _ _ h' z_prop'
    have : z_val_val.im = Complex.abs z_val_val.im := by norm_cast; have := abs_of_pos zpos;
      exact this.symm
    norm_cast at this 
    rw [this]
    exact z_property_right
    apply pow_two_pos_of_ne_zero
    have z_prop2 : 0 < z_val_val.im := by apply zpos
    linarith
    apply pow_two_pos_of_ne_zero; linarith
  have i2 : (z_val_val.re ^ 2 : ℝ) ≤ (A ^ 2 : ℝ) :=
    by
    have : Complex.abs z_val_val.re ^ 2 = z_val_val.re ^ 2 :=
      by
      norm_cast
      simp
    norm_cast at this 
    rw [← this]
    have v2 : 0 ≤ Complex.abs z_val_val.re := by apply complex.abs.nonneg
    norm_cast at v2 
    have v1 : 0 ≤ A := by apply le_trans v2 z_property_left
    apply aux6 _ _ v2 v1
    exact z_property_left
  ring_nf
  have i3 := mul_le_mul i1 i2
  have i4 : 0 ≤ z_val_val.re ^ 2 := by nlinarith
  have i5 : 0 ≤ (B ^ 2)⁻¹ := by simp; nlinarith
  have i6 := i3 i4 i5
  simp_rw [i6]
  simp
  apply aux5
  apply aux5
  exact h
  exact z_val_property
  apply div_nonneg
  apply Right.add_nonneg
  have he : Even (4 : ℤ) := by simp
  have := Even.zpow_nonneg he z_val_val.im
  apply this
  simp
  nlinarith
  nlinarith
  apply div_nonneg
  apply Right.add_nonneg
  have he : Even (4 : ℤ) := by simp
  have := Even.zpow_nonneg he z_val_val.im
  apply this
  simp only
  nlinarith
  nlinarith

theorem rfunctbound (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) (z : upperHalfSpaceSlice A B) :
    8 / rfunct z ^ k * rZ (k - 1) ≤ 8 / rfunct (lbpoint A B hb) ^ k * rZ (k - 1) :=
  by
  have h1 := rfunct_lower_bound_on_slice A B hb z
  simp only [Subtype.val_eq_coe] at h1 
  have v1 : 0 ≤ rfunct z := by have := rfunct_pos z; linarith
  have v2 : 0 ≤ rfunct (lbpoint A B hb) := by have := rfunct_pos (lbpoint A B hb); linarith
  have h2 := pow_le_pow_of_le_left v2 h1 k
  ring_nf
  rw [← inv_le_inv] at h2 
  have h3 : 0 ≤ rZ (k - 1) := by
    have hk : 1 < (k - 1 : ℤ) := by linarith
    have hkk : 1 < ((k - 1 : ℤ) : ℝ) := by norm_cast; exact hk
    simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at hkk 
    have := rZ_pos (k - 1) hkk; linarith
  nlinarith
  apply pow_pos
  apply rfunct_pos
  apply pow_pos
  apply rfunct_pos

theorem rfunctbound' (k : ℕ) (A B : ℝ) (hb : 0 < B) (z : upperHalfSpaceSlice A B) (n : ℕ) :
    8 / rfunct z ^ k * rie (k - 1) n ≤ 8 / rfunct (lbpoint A B hb) ^ k * rie (k - 1) n :=
  by
  have h1 := rfunct_lower_bound_on_slice A B hb z
  simp only [Subtype.val_eq_coe] at h1 
  have v1 : 0 ≤ rfunct z := by have := rfunct_pos z; linarith
  have v2 : 0 ≤ rfunct (lbpoint A B hb) := by have := rfunct_pos (lbpoint A B hb); linarith
  have h2 := pow_le_pow_of_le_left v2 h1 k
  ring_nf
  rw [← inv_le_inv] at h2 
  have h3 : 0 ≤ rie (k - 1) n := by
    rw [rie]
    simp only [one_div, inv_nonneg]
    apply Real.rpow_nonneg_of_nonneg
    simp only [Nat.cast_nonneg]
  nlinarith
  apply pow_pos
  apply rfunct_pos
  apply pow_pos
  apply rfunct_pos

theorem Real_Eisenstein_bound_unifomly_on_stip (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
    (z : upperHalfSpaceSlice A B) :
    realEisensteinSeriesOfWeight_ k z.1 ≤ 8 / rfunct (lbpoint A B hb) ^ k * rZ (k - 1) :=
  by
  have : 8 / rfunct z ^ k * rZ (k - 1) ≤ 8 / rfunct (lbpoint A B hb) ^ k * rZ (k - 1) := by
    apply rfunctbound; exact h
  apply le_trans (Real_Eisenstein_bound k z h) this

def eisenSquareSlice (k : ℤ) (A B : ℝ) (n : ℕ) : upperHalfSpaceSlice A B → ℂ := fun x =>
  eisenSquare k n x

def eisenParSumSlice (k : ℤ) (A B : ℝ) (n : ℕ) : upperHalfSpaceSlice A B → ℂ := fun z =>
  ∑ x in Finset.range n, eisenSquareSlice k A B x z

instance : Coe ℍ ℍ' :=
  ⟨fun z => ⟨z.1, by simp; cases z; assumption⟩⟩

instance sliceCoe (A B : ℝ) (hb : 0 < B) : Coe (upperHalfSpaceSlice A B) ℍ' :=
  ⟨fun x : upperHalfSpaceSlice A B => (x : ℍ')⟩

def eisensteinSeriesRestrict (k : ℤ) (A B : ℝ) : upperHalfSpaceSlice A B → ℂ := fun x =>
  eisensteinSeriesOfWeight_ k x

instance nonemp (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) : Nonempty (upperHalfSpaceSlice A B) :=
  by
  let z := (⟨A, B⟩ : ℂ)
  rw [← exists_true_iff_nonempty]
  simp
  use z
  have zim : z.im = B := by rfl
  use hb
  simp_rw [z]
  simp_rw [UpperHalfPlane.re, UpperHalfPlane.im]
  simp
  constructor
  have := abs_eq_self.2 ha
  rw [this]
  apply le_abs_self

theorem Eisenstein_series_is_sum_eisen_squares_slice (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
    (z : upperHalfSpaceSlice A B) :
    eisensteinSeriesRestrict k A B z = ∑' n : ℕ, eisenSquareSlice k A B n z :=
  by
  rw [Eisenstein_series_restrict]; simp_rw [Eisen_square_slice]
  have HI := Squares_cover_all
  let g := fun y : ℤ × ℤ => (Eise k z) y
  have hgsumm : Summable g := by simp_rw [g]; apply Eisenstein_series_is_summable k z h
  have index_lem := tsum_lemma' g Square HI hgsumm
  simp_rw [g] at index_lem 
  exact index_lem

theorem Eisen_partial_tends_to_uniformly (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) :
    TendstoUniformly (eisenParSumSlice k A B) (eisensteinSeriesRestrict k A B) Filter.atTop :=
  by
  let M : ℕ → ℝ := fun x => 8 / rfunct (lbpoint A B hb) ^ k * rie (k - 1) x
  have := M_test_uniform _ (Eisen_square_slice k A B) M
  simp_rw [← Eisenstein_series_is_sum_eisen_squares_slice k h A B hb _] at this 
  apply this
  simp_rw [Eisen_square_slice]
  simp_rw [eisen_square]
  simp_rw [M]
  simp_rw [Eise]
  intro n a
  have SC := SmallClaim k a h n
  rw [real_Eise] at SC 
  simp at SC 
  simp
  have ineq1 :
    Complex.abs (∑ x : ℤ × ℤ in Square n, ((↑x.fst * ↑↑a + ↑x.snd) ^ k)⁻¹) ≤
      ∑ x : ℤ × ℤ in Square n, (Complex.abs ((↑x.fst * ↑↑a + ↑x.snd) ^ k))⁻¹ :=
    by
    simp
    have := complex_abs_sum_le (Square n) fun x : ℤ × ℤ => (((x.1 : ℂ) * (a : ℂ) + (x.2 : ℂ)) ^ k)⁻¹
    simp at this 
    exact this
  simp at *
  have SC2 := le_trans ineq1 SC
  have rb := rfunctbound' k A B hb a n
  apply le_trans SC2 rb
  infer_instance
  infer_instance
  simp_rw [M]
  have hk : 1 < (k - 1 : ℤ) := by linarith
  have nze : (8 / rfunct (lbpoint A B hb) ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero; simp; apply pow_ne_zero
    simp; by_contra HR
    have := rfunct_pos (lbpoint A B hb)
    rw [HR] at this 
    simp at this 
    exact this
  have riesum := int_RZ_is_summmable (k - 1) hk
  rw [← (summable_mul_left_iff nze).symm]
  simp at riesum 
  apply riesum
  apply EisensteinSeries.nonemp A B ha hb

def powfun (k : ℤ) : ℂ → ℂ := fun x => x ^ k

def trans (a b : ℤ) : ℂ → ℂ := fun x => a * x + b

def ein (a b k : ℤ) : ℂ → ℂ := fun x => (a * x + b) ^ k

theorem com (a b k : ℤ) : ein a b k = powfun k ∘ trans a b := by rfl

theorem d1 (k : ℤ) (x : ℂ) : deriv (fun x => x ^ k) x = k * x ^ (k - 1) := by simp

theorem d2 (a b k : ℤ) (x : ℂ) (h : (a : ℂ) * x + b ≠ 0) :
    deriv (ein a b k) x = k * a * (a * x + b) ^ (k - 1) :=
  by
  rw [com]
  rw [deriv.comp]
  rw [powfun]
  rw [trans]
  simp
  ring
  rw [powfun]
  rw [trans]; simp; simp_rw [differentiableAt_zpow]
  simp [h]
  rw [trans]
  simp only [differentiableAt_const, differentiableAt_add_const_iff, differentiableAt_id',
    DifferentiableAt.mul]

theorem aux8 (a b k : ℤ) (x : ℂ) : (((a : ℂ) * x + b) ^ k)⁻¹ = ((a : ℂ) * x + b) ^ (-k) := by
  refine' (zpow_neg _ k).symm

theorem dd2 (a b k : ℤ) (x : ℂ) (h : (a : ℂ) * x + b ≠ 0) :
    HasDerivAt (ein a b k) (k * (a * x + b) ^ (k - 1) * a : ℂ) x :=
  by
  rw [com]
  apply HasDerivAt.comp
  rw [powfun]
  rw [trans]
  simp
  apply hasDerivAt_zpow
  simp [h]
  rw [trans]
  apply HasDerivAt.add_const
  have := HasDerivAt.const_mul (a : ℂ) (hasDerivAt_id x)
  simp at *
  exact this

theorem H_member (z : ℂ) : z ∈ UpperHalfPlane.upperHalfSpace ↔ 0 < z.im :=
  Iff.rfl

theorem Eise'_has_deriv_within_at (k : ℤ) (y : ℤ × ℤ) (hkn : k ≠ 0) :
    IsHolomorphicOn fun z : ℍ' => eise k z y :=
  by
  rw [IsHolomorphicOn]
  intro z
  by_cases hy : (y.1 : ℂ) * z.1 + y.2 ≠ 0
  simp_rw [Eise]; ring_nf
  have := aux8 y.1 y.2 k z.1
  simp only [Subtype.val_eq_coe] at this 
  have nz : (y.1 : ℂ) * z.1 + y.2 ≠ 0 := by apply hy
  have hdd := dd2 y.1 y.2 (-k) z nz
  rw [ein] at hdd 
  have H' := HasDerivAt.hasDerivWithinAt hdd
  have H :
    HasDerivWithinAt (fun x : ℂ => (↑y.fst * x + ↑y.snd) ^ (-k))
      (↑(-k) * (↑y.fst * ↑z + ↑y.snd) ^ (-k - 1) * ↑y.fst) UpperHalfPlane.upperHalfSpace ↑z :=
    by apply H'
  simp at H 
  let fx := (-k * ((y.1 : ℂ) * z.1 + y.2) ^ (-k - 1) * y.1 : ℂ)
  refine' ⟨fx, _⟩
  rw [hasDerivWithinAt_iff_tendsto] at *
  simp [zpow_neg, Algebra.id.smul_eq_mul, eq_self_iff_true, Ne.def, Int.cast_neg,
    Subtype.val_eq_coe, norm_eq_abs, sub_neg_eq_add] at *
  rw [Metric.tendsto_nhdsWithin_nhds] at *
  intro ε hε
  have HH := H ε hε
  obtain ⟨d1, hd1, hh⟩ := HH
  refine' ⟨d1, hd1, _⟩
  intro x hx hd
  dsimp at *
  simp_rw [extendByZero]
  simp only [dite_eq_ite, if_true, Subtype.coe_prop, Subtype.coe_eta, Subtype.coe_mk]
  rw [← dite_eq_ite]; rw [dif_pos hx]
  have H3 := hh hx hd
  simp_rw [fx]
  convert H3
  ring_nf
  simp only [Classical.not_not, Subtype.val_eq_coe] at hy 
  have hz : y.1 = 0 ∧ y.2 = 0 := by
    by_contra
    simp only [not_and] at h 
    cases z
    cases y
    dsimp at *
    injections
    dsimp at *
    simp only [int_cast_re, Int.cast_eq_zero, add_zero, int_cast_im, MulZeroClass.zero_mul,
      sub_zero, mul_eq_zero] at *
    cases h_2
    rw [h_2] at h_1 
    simp only [Int.cast_eq_zero, Int.cast_zero, MulZeroClass.zero_mul, zero_add] at *
    have := h h_2
    rw [h_1] at this 
    simp only [eq_self_iff_true, not_true] at this 
    exact this
    simp only [H_member] at z_property 
    rw [h_2] at z_property 
    simp only [lt_self_iff_false] at z_property 
    exact z_property
  simp_rw [Eise]; rw [hz.1, hz.2]
  simp only [one_div, add_zero, Int.cast_zero, MulZeroClass.zero_mul]
  have zhol := zero_hol ℍ'
  rw [IsHolomorphicOn] at zhol 
  have zhol' := zhol z
  simp only at zhol' 
  have zk : ((0 : ℂ) ^ k)⁻¹ = 0 := by
    simp only [inv_eq_zero]
    apply zero_zpow
    apply hkn
  rw [zk]
  exact zhol'

theorem Eise'_has_diff_within_at (k : ℤ) (y : ℤ × ℤ) (hkn : k ≠ 0) :
    DifferentiableOn ℂ (extendByZero fun z : ℍ' => eise k z y) ℍ' :=
  by
  have := isHolomorphicOn_iff_differentiableOn ℍ' fun z : ℍ' => Eise k z y
  simp
  rw [this]
  apply Eise'_has_deriv_within_at
  apply hkn

theorem Eis_diff_on_ball {R : ℝ} {z w : ℂ} (hw : w ∈ Metric.ball z R) (k : ℤ) (y : ℤ × ℤ)
    (hkn : k ≠ 0) (h : Metric.closedBall z R ⊆ ℍ') :
    DifferentiableOn ℂ (extendByZero fun z : ℍ' => eise k z y) (Metric.closedBall z R) :=
  by
  apply DifferentiableOn.mono (Eise'_has_diff_within_at k y hkn)
  simp only [Metric.mem_ball, Ne.def, Subtype.coe_mk] at *
  apply h

end EisensteinSeries

