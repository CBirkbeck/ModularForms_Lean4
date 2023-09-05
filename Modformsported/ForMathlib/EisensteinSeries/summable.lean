import Modformsported.ForMathlib.ModForms2
import Modformsported.ForMathlib.EisensteinSeries.basic
import Modformsported.ForMathlib.EisensteinSeries.lattice_functions
import Modformsported.ForMathlib.EisensteinSeries.bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow 
import Modformsported.ModForms.Riemzeta
import Modformsported.ModForms.WeierstrassMTest 

open Complex

open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold

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

theorem pow_linear_ne_zero'' (c d : ℤ) (z : ℍ) (h : d ≠ 0) (k : ℕ) : ((c : ℂ) * z + d)^k  ≠ 0 := by
  norm_cast
  apply pow_ne_zero _ (linear_ne_zero'' c d z h) 

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

section auxilary_summable

variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

def fn (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) (x : ℤ × ℤ) :
    x ∈ ⋃ s : ℕ, (In s) := by
  have h1 := HI x
  rw [Set.mem_iUnion]
  simp 
  obtain ⟨i, hi1,_⟩:= h1
  refine ⟨i,hi1⟩

def fnn (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) (x : ℤ × ℤ) :
    ⋃ s : ℕ, ((In s) : Set (ℤ × ℤ)) :=
  ⟨x, fn In HI x⟩ 

def unionEquiv (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) :
    (⋃ s : ℕ, ((In s) : Set (ℤ × ℤ))) ≃ ℤ × ℤ where
  toFun x := x.1
  invFun x := fnn In HI x
  left_inv := by simp; intro x; cases x; rfl
  right_inv := by simp; intro x; rfl


theorem unionmem (i : α → Set β) (x : α) (y : i x) :  (y : β) ∈ ⋃ x, i x :=
  by
  apply Set.mem_iUnion_of_mem 
  apply y.2

theorem summable_disjoint_union_of_nonneg {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ x, Summable fun y : i x => f ⟨y,  unionmem i x y ⟩) ∧
        Summable fun x => ∑' y : i x, f ⟨y, unionmem i x y⟩ :=
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

theorem tsum_disjoint_union_of_nonneg' {γ : Type} [AddCommGroup γ]  [ UniformSpace γ]
    [UniformAddGroup γ] [CompleteSpace γ] [T0Space γ] [T2Space γ]
    {i : α → Set β} {f : (⋃ x, i x) → γ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (h1 : Summable f) :
    ∑' x, f x = ∑' x, ∑' y : i x, f ⟨y, unionmem i x y⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h11 : ∑' x, f x = ∑' y, f (h0 y) := by have := Equiv.tsum_eq h0 f; rw [← this]
  rw [h11]
  rw [tsum_sigma]
  simp_rw [Set.sigmaToiUnion]
  rfl
  have h01 : Summable f ↔ Summable (f ∘ h0) := by rw [Equiv.summable_iff]
  convert (h01.1 h1)

theorem sum_lemma (f : ℤ × ℤ → ℝ) (h : ∀ y : ℤ × ℤ, 0 ≤ f y) (In : ℕ → Finset (ℤ × ℤ))
    (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) : Summable f ↔ Summable fun n : ℕ => ∑ x in In n, f x :=
  by
  let h2 := unionEquiv In HI
  have h22 : ∀ y : ⋃ s : ℕ, (In s), 0 ≤ (f ∘ h2) y :=
    by
    intro y
    apply h  
  have hdis' := disjoint_aux In HI
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint ((In a)) ((In b)) :=
    by
    intro a b hab;
    apply hdis'; exact hab
  have h3 := summable_disjoint_union_of_nonneg ?_ h22
  have h4 : Summable f ↔ Summable (f ∘ h2) := by rw [Equiv.summable_iff]
  rw [h4]
  rw [h3]
  constructor
  intro H
  convert H.2
  rw [←Finset.tsum_subtype]
  rfl
  intro H
  constructor
  intro x
  simp
  rw [unionEquiv]
  simp
  apply Finset.summable
  convert H
  rw [←Finset.tsum_subtype]
  rfl
  norm_cast

theorem tsum_lemma {γ : Type} [AddCommGroup γ]  [ UniformSpace γ]
    [UniformAddGroup γ] [CompleteSpace γ] [T0Space γ] [T2Space γ] 
    (f : ℤ × ℤ → γ) (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i)
    (hs : Summable f) : ∑' x, f x = ∑' n : ℕ, ∑ x in In n, f x :=
  by
  let h2 := unionEquiv In HI
  have hdis' := disjoint_aux In HI
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint ( (In a)) ((In b)) :=
    by
    intro a b hab; 
    apply hdis'; exact hab
  
  have HS : Summable (f ∘ h2) := by rw [Equiv.summable_iff h2]; exact hs
  have HH := tsum_disjoint_union_of_nonneg' ?_ HS
  simp at HH 
  have := Equiv.tsum_eq h2 f
  rw [← this]
  rw [HH]
  rw [unionEquiv]
  simp
  norm_cast  

section Abs_Eisentein_summable


lemma Eise_on_square_is_bounded_Case1 (k : ℕ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (hn : 1 ≤ n) 
  (C1 :Complex.abs (x.1 : ℂ) = n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤ 
      (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
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
    simp only [Nat.cast_pow, map_pow, abs_cast_nat]
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

lemma Eise_on_square_is_bounded_Case2 (k : ℕ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (hn : 1 ≤ n) 
  (C2 :Complex.abs (x.2 : ℂ) = n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤ 
      (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ := by
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
    (x.snd  : ℂ)^ (k : ℤ) * ((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ (k : ℤ) := by
    field_simp
    ring
  rw [h1]
  simp_rw [map_mul Complex.abs]
  have h3 : Complex.abs (n^k : ℕ) = Complex.abs (x.snd^k : ℤ) := by 
    have : Complex.abs (x.snd^k : ℤ) = Complex.abs (x.snd)^k := by 
      simp only [Int.cast_pow, map_pow, Real.rpow_nat_cast]
    rw [this, C2]
    norm_cast
    simp only [Nat.cast_pow, map_pow, abs_cast_nat]
  simp at *
  norm_cast at *
  rw [h3, mul_comm]
  apply mul_le_mul_of_nonneg_left
  have := auxlem3 z x k
  simp at *
  norm_cast at *
  simp only [ge_iff_le, map_nonneg, pow_nonneg]
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


theorem Eise_on_square_is_bounded (k : ℕ) (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (h : x ∈ square n) 
  (hn : 1 ≤ n) : (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ (k : ℤ)))⁻¹ ≤ 
    (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ)))⁻¹ :=
  by
  by_cases C1 : Complex.abs (x.1 : ℂ) = n
  apply Eise_on_square_is_bounded_Case1 k z n x hn C1
  have C2 := Complex_abs_square_left_ne n x h C1
  apply Eise_on_square_is_bounded_Case2 k z n x hn C2
 

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
  rw [square_zero] at hx 
  simp only [Finset.mem_singleton] at hx 
  simp_rw [hx]
  simp only [add_zero, Int.cast_zero, MulZeroClass.zero_mul, map_mul Complex.abs]
  have h1 : (0 : ℂ) ^ k = 0 := by 
    simp only [cpow_nat_cast, ne_eq, zero_pow_eq_zero]
    linarith
  rw [h1]
  simp only [map_zero, inv_zero, cpow_nat_cast, map_pow, abs_ofReal, mul_zero, le_refl]

theorem Eise_on_square_is_bounded'' (k : ℕ) (z : ℍ) (n : ℕ) (hn : 1 ≤ k) :
    ∀ x : ℤ × ℤ,
      x ∈ square n →
        (Complex.abs (((x.1 : ℂ) * z + (x.2 : ℂ)) ^ k))⁻¹ ≤
          (Complex.abs (rfunct z ^ k * n ^ k))⁻¹ :=
  by
  by_cases h0 : n = 0
  · rw [h0]; have := Eise_on_zero_square k z hn; simp at *; apply this
  have Hn : 1 ≤ n := by
    have := Nat.pos_of_ne_zero h0
    linarith
  intro x hx
  apply Eise_on_square_is_bounded k z n x hx Hn

theorem AbsEise_bounded_on_square (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
    ∀ n : ℕ, ∑ y : ℤ × ℤ in square n, (AbsEise k z) y ≤ 8 / rfunct z ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ :=
  by
  intro n
  simp_rw [AbsEise]
  simp [one_div, Complex.abs_pow, abs_inv, zpow_ofNat]
  have k0 : 1 ≤ k := by linarith
  have BO := Eise_on_square_is_bounded'' (k : ℕ) (z : ℍ) (n : ℕ) k0
  by_cases n0 : n = 0
  · rw [n0]
    norm_cast
    rw [square_zero]
    simp only [add_zero, Int.cast_zero, Nat.cast_zero, MulZeroClass.zero_mul, Finset.sum_singleton]
    have H0 : (0 : ℂ) ^ k = 0 := by simp; linarith
    simp [abs_zero, inv_zero]
    have H00 : (0 : ℝ) ^ (k - 1) = 0 := by norm_cast; simp; linarith
    norm_cast at *
    rw [H00]
    simp [inv_zero, MulZeroClass.mul_zero]; norm_cast at *; rw [H0]
  have := Finset.sum_le_sum BO
  simp only [Finset.sum_const, map_mul Complex.abs, nsmul_eq_mul] at this 
  rw [square_size' n] at this 
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
    congr
    norm_cast
    have := natpowsinv n k ?_
    norm_cast at *
    rw [this]
    apply mul_comm
    norm_cast at *
    rw [abs_eq_self]
    apply (EisensteinSeries.rfunct_pos z).le
  norm_cast at *
  rw [←ne] 
  norm_cast
  simp at *
  apply this
  have hhh := Nat.pos_of_ne_zero n0
  linarith

theorem SmallClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k) :
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

theorem real_eise_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k) : Summable (AbsEise k z) :=by
  let In := fun (n : ℕ) => square n
  have HI := squares_cover_all 
  let g := fun y : ℤ × ℤ => (AbsEise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by  intro y; simp_rw [AbsEise]; simp
  have index_lem := sum_lemma g gpos In HI
  rw [index_lem]
  let e := fun x : ℕ => ∑ y : ℤ × ℤ in In x, g y
  have smallerclaim := SmallClaim k z h
  have epos : ∀ x : ℕ, 0 ≤ e x := by
    intro x
    apply Finset.sum_nonneg; intro i _; 
    apply Complex.abs.nonneg
  have hk : 1 < (k - 1 : ℤ) := by linarith
  have nze : (8 / rfunct z ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp only [Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero]
    linarith
    norm_cast
    apply pow_ne_zero
    simp only [Ne.def]
    by_contra HR
    have := rfunct_pos z
    rw [HR] at this 
    simp only [lt_self_iff_false] at this 
  have riesum := int_RZ_is_summmable (k - 1) hk
  have riesum' : Summable fun n : ℕ => 8 / rfunct z ^ k * rie (↑k - 1) n :=
    by
    rw [← (summable_mul_left_iff nze).symm]
    simp only [Int.cast_ofNat, Int.cast_one, Int.cast_sub] at riesum 
    apply riesum
  have := summable_of_nonneg_of_le epos smallerclaim
  apply this
  apply riesum'

theorem Eisenstein_tsum_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k) : Summable (eise k z) :=
  by
  let f := eise k z
  have sum_Eq : (Summable fun x => abs (f x)) → Summable f := by
    apply summable_if_complex_abs_summable
  apply sum_Eq
  have := real_eise_is_summable k z h
  simp_rw [AbsEise] at this 
  exact this