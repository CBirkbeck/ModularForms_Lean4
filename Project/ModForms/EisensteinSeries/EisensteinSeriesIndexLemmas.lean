import Mathlib.Tactic.PiInstances
import Project.ModForms.ModularGroup.ModGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Project.ForMathlib.ModForms2
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.Instances.Ennreal
import Mathlib.Topology.Instances.Nnreal
import Project.ModForms.Riemzeta
import Project.ModForms.HolomorphicFunctions
import Mathlib.Order.Filter.Archimedean
import Project.ModForms.WeierstrassMTest
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.Modular

#align_import mod_forms.Eisenstein_Series.Eisenstein_series_index_lemmas

universe u v w

open Complex

open ModularGroup

open IntegralMatricesWithDeterminante

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

local notation "SL2Z" => Matrix.SpecialLinearGroup (Fin 2) ℤ

local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

noncomputable section

namespace EisensteinSeries

theorem ridic (a b c d : ℤ) : a * d - b * c = 1 → a * d - c * b = 1 := by intro h; linarith

theorem ridic2 (a b c d z : ℤ) (h : a * d - b * c = 1) : z * d * a - z * c * b = z := by ring_nf;
  rw [h]; rw [one_mul]

-- This is the permutation of the summation index coming from the moebius action
def indPerm (A : SL2Z) : ℤ × ℤ → ℤ × ℤ := fun z =>
  (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1)

theorem det_sl_one (M : SL2Z) : M.1 0 0 * M.1 1 1 + -(M.1 0 1 * M.1 1 0) = 1 := by apply det_m

def indEquiv (A : SL2Z) : ℤ × ℤ ≃ ℤ × ℤ
    where
  toFun := indPerm A
  invFun := indPerm A⁻¹
  left_inv z := by
    simp_rw [Ind_perm]
    ring_nf
    have hdet := det_sl_one A
    simp only [Subtype.val_eq_coe, SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *
    nth_rw 2 [mul_comm]
    nth_rw 3 [mul_comm]
    ext
    simp only
    simp_rw [hdet]
    ring
    simp only
    nth_rw 3 [add_comm]
    simp_rw [hdet]
    ring
  right_inv z := by
    simp_rw [Ind_perm]
    ring_nf
    have hdet := det_sl_one A
    simp only [Subtype.val_eq_coe, SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *
    ext
    simp only [mul_neg]
    nth_rw 3 [mul_comm]
    simp_rw [hdet]
    ring
    simp only [mul_neg]
    nth_rw 3 [add_comm]
    nth_rw 5 [mul_comm]
    simp_rw [hdet]
    ring

@[simp]
theorem ind_simp (A : SL2Z) (z : ℤ × ℤ) :
    indEquiv A z = (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1) := by rfl

theorem max_aux' (a b : ℕ) : max a b = a ∨ max a b = b := by apply max_choice

theorem max_aux (a b : ℕ) : a = max a b ∨ b = max a b := by have := max_aux' a b; cases this;
  simp [this]; simp [this]

theorem max_aux'' (a b n : ℕ) (h : max a b = n) : a = n ∨ b = n :=
  by
  rw [← h]
  apply max_aux

theorem max_aux3 (a b n : ℕ) (h : max a b = n) : a ≤ n ∧ b ≤ n := by rw [← h]; constructor;
  exact le_max_left a b; exact le_max_right a b

/-- For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that the maximum of the
absolute values of the pair is `m` -/
def square (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico (-m : ℤ) (m + 1)).product (Finset.Ico (-m : ℤ) (m + 1))).filterₓ fun x =>
    max x.1.natAbs x.2.natAbs = m

/-- For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that..-/
def square2 (m : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Ico (-m : ℤ) (m + 1)).product {m} ∪ (Finset.Ico (-m : ℤ) (m + 1)).product {-(m : ℤ)} ∪
      ({m} : Finset ℤ).product (Finset.Ico (-m + 1) m) ∪
    ({-m} : Finset ℤ).product (Finset.Ico (-m + 1) m)

theorem square2_card (n : ℕ) (h : 1 ≤ n) : (Finset.card (square2 n) : ℤ) = 8 * n :=
  by
  rw [Square2, Finset.card_union_eq, Finset.card_union_eq, Finset.card_union_eq,
    Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product]
  · simp only [Finset.card_singleton, mul_one, one_mul]
    have hn : -(n : ℤ) ≤ n + 1 := by linarith
    have hn2 : -(n : ℤ) + 1 ≤ n := by linarith
    have r1 := Int.card_Ico_of_le (-(n : ℤ)) (n + 1) hn
    have r2 := Int.card_Ico_of_le (-(n : ℤ) + 1) n hn2
    simp only [Int.ofNat_add, Int.card_Ico, sub_neg_eq_add, neg_add_le_iff_le_add] at *
    rw [r1, r2]
    ring_nf
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Ne.def, Finset.mem_singleton, Finset.mem_product, Finset.mem_Ico] at *
    by_contra H
    have haa := ha.2
    have hbb := hb.2
    rw [H] at haa 
    rw [hbb] at haa 
    have hv := eq_zero_of_neg_eq haa
    simp only [Int.coe_nat_eq_zero] at hv 
    rw [hv] at h 
    simp only [Nat.one_ne_zero, le_zero_iff] at h 
    exact h
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Ne.def, Finset.mem_union, Finset.mem_singleton, neg_add_le_iff_le_add,
      Finset.mem_product, Finset.mem_Ico] at *
    cases ha
    have hbb := hb.2
    have haa := ha.2
    by_contra H
    rw [← H] at hbb 
    rw [haa] at hbb 
    simp only [lt_self_iff_false, and_false_iff] at hbb 
    exact hbb
    have hbb := hb.2
    have haa := ha.2
    by_contra H
    rw [← H] at hbb 
    rw [haa] at hbb 
    simp at hbb 
    have hk := hbb.1
    linarith
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Ne.def, Finset.mem_union, Finset.union_assoc, Finset.mem_singleton,
      neg_add_le_iff_le_add, Finset.mem_product, Finset.mem_Ico] at *
    by_contra H
    cases ha
    · have hbb := hb.2
      have haa := ha.2
      rw [← H] at hbb 
      rw [← haa] at hbb 
      simp [lt_self_iff_false, and_false_iff] at hbb 
      exact hbb
    cases ha
    · have hbb := hb.2
      have haa := ha.2
      rw [← H] at hbb 
      rw [haa] at hbb 
      simp only [Int.coe_nat_pos, neg_lt_self_iff, add_right_neg] at hbb 
      linarith
    · have hbb := hb.1
      have haa := ha.1
      rw [H] at haa 
      rw [hbb] at haa 
      have hv := eq_zero_of_neg_eq haa
      simp only [Int.coe_nat_eq_zero] at hv 
      rw [hv] at h 
      simp only [Nat.one_ne_zero, le_zero_iff] at h 
      exact h

theorem natAbs_inter (a : ℤ) (n : ℕ) (h : a.natAbs < n) : a < (n : ℤ) ∧ 0 < (n : ℤ) + a :=
  by
  have := Int.natAbs_eq a
  cases this
  rw [this]
  constructor
  norm_cast
  exact h
  norm_cast
  simp only [add_pos_iff]
  left
  have h1 : 0 ≤ a.nat_abs := zero_le (Int.natAbs a)
  linarith
  rw [this]
  constructor
  rw [neg_lt_iff_pos_add]
  norm_cast
  simp
  have h1 : 0 ≤ a.nat_abs := zero_le (Int.natAbs a)
  left
  linarith
  rw [← Int.ofNat_lt] at h 
  rw [← sub_pos] at h 
  convert h

theorem natAbs_inter2 (a : ℤ) (n : ℕ) (h : a.natAbs ≤ n) : a ≤ (n : ℤ) ∧ 0 ≤ (n : ℤ) + a :=
  by
  have := lt_or_eq_of_le h; cases this
  have H := nat_abs_inter a n this; have H1 := le_of_lt H.1; have H2 := le_of_lt H.2; simp [H1, H2];
  rw [← this]
  constructor; exact Int.le_natAbs; rw [add_comm]; rw [← neg_le_iff_add_nonneg'];
  rw [← Int.abs_eq_natAbs]
  simp_rw [neg_le_abs_self]

@[simp]
theorem square_mem (n : ℕ) (x : ℤ × ℤ) : x ∈ square n ↔ max x.1.natAbs x.2.natAbs = n :=
  by
  constructor
  intro x
  rw [Square] at x 
  simp at x 
  simp_rw [x]
  intro hx
  rw [Square]
  simp
  simp [hx]
  have h2 := max_aux3 _ _ _ hx
  have h21 := nat_abs_inter2 _ _ h2.1
  have h22 := nat_abs_inter2 _ _ h2.2
  constructor
  constructor
  rw [neg_le_iff_add_nonneg']
  exact h21.2
  have := h21.1
  linarith
  constructor
  rw [neg_le_iff_add_nonneg']
  exact h22.2
  have := h22.1; linarith

theorem square_mem' (n : ℕ) (x : ℤ × ℤ) :
    x ∈ square n ↔
      x.1.natAbs = n ∧ x.2.natAbs < n ∨
        x.2.natAbs = n ∧ x.1.natAbs < n ∨ x.1.natAbs = n ∧ x.2.natAbs = n :=
  by
  simp
  constructor
  intro c1
  have := max_aux3 _ _ _ c1
  have H := max_aux'' _ _ _ c1
  have h1 := this.1
  have h2 := this.2
  rw [le_iff_lt_or_eq] at h2 
  rw [le_iff_lt_or_eq] at h1 
  cases H
  simp_rw [H]
  simp
  exact h2
  simp_rw [H]
  simp
  exact h1
  intro c2
  cases c2
  rw [c2.1]
  simp
  have := c2.2
  linarith
  cases c2
  rw [c2.1]
  simp
  have := c2.2
  linarith
  rw [c2.1, c2.2]
  simp

theorem auxin (a : ℤ) (n : ℕ) (h : 0 < (n : ℤ) + a) : 1 ≤ (n : ℤ) + a := by assumption

theorem auxin2 (a : ℤ) (n : ℕ) (h : 0 < (n : ℤ) + a) : -(n : ℤ) ≤ a := by linarith

theorem cat (a b : ℤ) (n : ℕ) (h1 : b = (n : ℤ)) (h2 : -(n : ℤ) ≤ a ∧ a < (n : ℤ) + 1) :
    b.natAbs = n ∧ (a.natAbs < n ∨ a.natAbs = n) :=
  by
  rw [h1]
  simp
  have := Int.natAbs_eq a
  cases this
  rw [this] at h2 
  norm_cast at h2 
  have h22 := h2.2
  exact nat.lt_succ_iff_lt_or_eq.mp h22
  rw [this] at h2 
  have h22 := h2.1
  have H := lt_or_eq_of_le h22
  simp only [neg_lt_neg_iff, neg_inj] at H 
  norm_cast at H 
  have h234 : n = a.nat_abs ↔ a.nat_abs = n := comm
  rw [← h234]
  exact H

theorem cat1 (a b : ℤ) (n : ℕ) (h1 : b = -(n : ℤ)) (h2 : -(n : ℤ) ≤ a ∧ a < (n : ℤ) + 1) :
    b.natAbs = n ∧ (a.natAbs < n ∨ a.natAbs = n) :=
  by
  rw [h1]
  simp
  have := Int.natAbs_eq a
  cases this
  rw [this] at h2 
  norm_cast at h2 
  have h22 := h2.2
  exact nat.lt_succ_iff_lt_or_eq.mp h22
  rw [this] at h2 
  have h22 := h2.1
  have H := lt_or_eq_of_le h22
  simp only [neg_lt_neg_iff, neg_inj] at H 
  norm_cast at H 
  have h234 : n = a.nat_abs ↔ a.nat_abs = n := comm
  rw [← h234]
  exact H

theorem dog (a b : ℤ) (n : ℕ) (h1 : a = (n : ℤ)) (h2 : 1 ≤ (n : ℤ) + b ∧ b < (n : ℤ)) :
    a.natAbs = n ∧ b.natAbs < n := by
  rw [h1]; simp; have := Int.natAbs_eq b; cases this; rw [this] at h2 ; norm_cast at h2 ; exact h2.2
  rw [this] at h2 ; have h22 := h2.1; norm_cast at *; linarith

theorem dog1 (a b : ℤ) (n : ℕ) (h1 : a = -(n : ℤ)) (h2 : 1 ≤ (n : ℤ) + b ∧ b < (n : ℤ)) :
    a.natAbs = n ∧ b.natAbs < n := by
  rw [h1]; simp; have := Int.natAbs_eq b; cases this; rw [this] at h2 ; norm_cast at h2 ; exact h2.2
  rw [this] at h2 ; have h22 := h2.1; norm_cast at *; linarith

theorem sqr_eq_sqr2 (n : ℕ) : square n = square2 n :=
  by
  ext1
  constructor
  rw [square_mem']
  intro ha
  rw [Square2]
  simp_rw [Int.natAbs_eq_iff] at ha 
  simp only [Finset.mem_union, Finset.union_assoc, Finset.mem_product, Finset.mem_Ico,
    neg_add_le_iff_le_add, Finset.mem_singleton]
  cases ha
  cases ha.1
  have h1 := nat_abs_inter _ _ ha.2
  have h2 := auxin _ _ h1.2
  simp_rw [h, h1, h2]
  simp
  have h1 := nat_abs_inter _ _ ha.2
  have h2 := auxin _ _ h1.2
  simp_rw [h, h1, h2]
  simp
  cases ha
  cases ha.1
  have h1 := nat_abs_inter _ _ ha.2
  have h2 := auxin2 _ _ h1.2
  simp_rw [h, h2]
  simp
  have h3 := h1.1
  have Hk : a.1 < (n : ℤ) + 1 := by linarith
  simp only [Hk, true_or_iff]
  have h1 := nat_abs_inter _ _ ha.2
  have h2 := auxin2 _ _ h1.2
  simp_rw [h, h2]
  simp
  have h3 := h1.1
  have Hk : a.1 < (n : ℤ) + 1 := by linarith
  simp only [Hk, true_or_iff, or_true_iff]
  cases ha.1
  cases ha.2
  simp_rw [h, h_1]
  have n1 : -(n : ℤ) ≤ (n : ℤ) := by linarith
  simp_rw [n1]
  simp only [lt_add_iff_pos_right, true_or_iff, eq_self_iff_true, and_self_iff, zero_lt_one]
  simp_rw [h, h_1]
  have n1 : -(n : ℤ) ≤ (n : ℤ) := by linarith
  simp_rw [n1]
  simp only [lt_add_iff_pos_right, true_or_iff, eq_self_iff_true, or_true_iff, and_self_iff,
    zero_lt_one]
  cases ha.2
  simp_rw [h, h_1]
  simp only [true_and_iff, lt_self_iff_false, le_refl, and_true_iff, eq_self_iff_true, or_false_iff,
    and_false_iff] at *
  have n1 : -(n : ℤ) < (n : ℤ) + 1 := by linarith
  simp_rw [n1]
  simp only [true_or_iff]
  have hg : -(n : ℤ) < n + 1 := by linarith
  simp_rw [h, h_1, hg]
  simp
  intro ha
  rw [Square2] at ha 
  simp only [Finset.mem_union, Finset.union_assoc, Finset.mem_product, Finset.mem_Ico,
    neg_add_le_iff_le_add, Finset.mem_singleton] at ha 
  rw [square_mem']
  cases ha
  have := cat _ _ _ ha.2 ha.1
  simp_rw [this]
  simp only [true_and_iff, lt_self_iff_false, and_true_iff, false_or_iff, eq_self_iff_true,
    and_false_iff]
  exact this.2
  cases ha
  have := cat1 _ _ _ ha.2 ha.1
  simp_rw [this]
  simp
  exact this.2
  cases ha
  have := dog _ _ _ ha.1 ha.2
  simp_rw [this]
  simp only [true_or_iff, eq_self_iff_true, and_self_iff]
  have := dog1 _ _ _ ha.1 ha.2
  simp_rw [this]
  simp only [true_or_iff, eq_self_iff_true, and_self_iff]

theorem square_size (n : ℕ) (h : 1 ≤ n) : Finset.card (square n) = 8 * n :=
  by
  rw [sqr_eq_sqr2]
  have := square2_card n h
  norm_cast at this 
  apply this

theorem Squares_are_disjoint : ∀ i j : ℕ, i ≠ j → Disjoint (square i) (square j) :=
  by
  intro i j hij
  rw [Finset.disjoint_iff_ne]
  intro a ha
  simp at ha 
  intro b hb
  simp at hb 
  by_contra
  rw [h] at ha 
  rw [hb] at ha 
  induction ha
  induction h
  cases a
  induction hb
  cases b
  dsimp at *
  simp at *
  assumption

theorem Squares_cover_all : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ square i :=
  by
  intro y
  use max y.1.natAbs y.2.natAbs
  simp only [square_mem, and_self_iff, forall_eq']

theorem square_zero : square (0 : ℕ) = {(0, 0)} := by rfl

theorem square_zero_card : Finset.card (square 0) = 1 :=
  by
  rw [Square_zero]
  rfl

-- Some summable lemmas
variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

instance (a : α) : HasLiftT (i a) (Set.iUnion i) :=
  by
  fconstructor
  intro H
  cases H
  fconstructor
  apply H_val
  simp at *; fconstructor; on_goal 2 => assumption

instance : CoeTC (Finset (ℤ × ℤ)) (Set (ℤ × ℤ)) :=
  inferInstance

def coef (s : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  (s : Set (ℤ × ℤ))

def fn (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) (x : ℤ × ℤ) :
    x ∈ ⋃ s : ℕ, coef (In s) := by
  have h1 := HI x
  rw [Set.mem_iUnion]
  cases h1
  cases x
  cases h1_h
  dsimp at *
  simp at *
  fconstructor; on_goal 2 => assumption

def fnn (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) (x : ℤ × ℤ) :
    ⋃ s : ℕ, coef (In s) :=
  ⟨x, fn In HI x⟩

def unionEquiv (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) :
    (⋃ s : ℕ, coef (In s)) ≃ ℤ × ℤ where
  toFun x := x.1
  invFun x := fnn In HI x
  left_inv := by simp; intro x; cases x; rfl
  right_inv := by simp; intro x; rfl

theorem unionmem (i : α → Set β) (x : α) (y : i x) : coe y ∈ ⋃ x, i x :=
  by
  simp
  use x
  cases y
  assumption

theorem summable_disjoint_union_of_nonneg {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ x, Summable fun y : i x => f ⟨y, unionmem i x y⟩) ∧
        Summable fun x => ∑' y : i x, f ⟨y, unionmem i x y⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : Summable f ↔ Summable (f ∘ h0) := by have := Equiv.summable_iff h0; rw [this]
  have h22 : ∀ y : Σ s : α, i s, 0 ≤ (f ∘ h0) y :=
    by
    simp_rw [h0]
    rw [Set.unionEqSigmaOfDisjoint]
    simp only [Equiv.symm_symm, Function.comp_apply, Sigma.forall, Equiv.ofBijective_apply]
    simp_rw [Set.sigmaToiUnion]
    simp_rw [hf]
    simp only [forall₂_true_iff]
  have h1 := summable_sigma_of_nonneg h22
  rw [h01]; rw [h1]
  have H1 :
    ∀ x : α,
      (Summable fun y : (fun s : α => ↥(i s)) x => f (h0 ⟨x, y⟩)) ↔
        Summable fun y : ↥(i x) => f ⟨y, unionmem i x y⟩ :=
    by
    intro x
    dsimp
    simp_rw [h0]
    rw [Set.unionEqSigmaOfDisjoint]
    simp only [Equiv.symm_symm, Equiv.ofBijective_apply]
    simp_rw [Set.sigmaToiUnion]
  simp_rw [H1]
  simp only [and_congr_right_iff]
  intro hfin
  have H2 :
    ∀ x : α,
      ∑' y : (fun s : α => ↥(i s)) x, (f ∘ ⇑h0) ⟨x, y⟩ = ∑' y : ↥(i x), f ⟨↑y, unionmem i x y⟩ :=
    by
    intro x
    simp only [Function.comp_apply]
    simp_rw [h0]
    rw [Set.unionEqSigmaOfDisjoint]
    simp only [Equiv.symm_symm, Equiv.ofBijective_apply]
    simp_rw [Set.sigmaToiUnion]
  simp_rw [H2]

theorem tsum_disjoint_union_of_nonneg' {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (h1 : Summable f) :
    ∑' x, f x = ∑' x, ∑' y : i x, f ⟨y, unionmem i x y⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : ∑' x, f x = ∑' y, f (h0 y) := by have := Equiv.tsum_eq h0 f; rw [← this]
  rw [h01]
  rw [tsum_sigma]
  simp_rw [h0]
  rw [Set.unionEqSigmaOfDisjoint]
  simp
  simp_rw [Set.sigmaToiUnion]
  have h01 : Summable f ↔ Summable (f ∘ h0) := by have := Equiv.summable_iff h0; rw [this]
  rw [← h01]
  exact h1

theorem tsum_disjoint_union_of_nonneg'' {i : α → Set β} {f : (⋃ x, i x) → ℂ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (h1 : Summable f) :
    ∑' x, f x = ∑' x, ∑' y : i x, f ⟨y, unionmem i x y⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : ∑' x, f x = ∑' y, f (h0 y) := by have := Equiv.tsum_eq h0 f; rw [← this]
  rw [h01]
  rw [tsum_sigma]
  simp_rw [h0]
  rw [Set.unionEqSigmaOfDisjoint]
  simp
  simp_rw [Set.sigmaToiUnion]
  have h01 : Summable f ↔ Summable (f ∘ h0) := by have := Equiv.summable_iff h0; rw [this]
  rw [← h01]
  exact h1

theorem disjoint_aux (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) :
    ∀ i j : ℕ, i ≠ j → Disjoint (In i) (In j) :=
  by
  intro i j h
  intro x h1 h2 a h3
  cases a
  dsimp at *
  simp at *
  have HI0 := HI a_fst a_snd
  have := ExistsUnique.unique HI0 (h1 h3) (h2 h3)
  rw [this] at h 
  simp at *
  exact h

theorem sum_lemma (f : ℤ × ℤ → ℝ) (h : ∀ y : ℤ × ℤ, 0 ≤ f y) (In : ℕ → Finset (ℤ × ℤ))
    (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) : Summable f ↔ Summable fun n : ℕ => ∑ x in In n, f x :=
  by
  let h2 := union_equiv In HI
  have h22 : ∀ y : ⋃ s : ℕ, coef (In s), 0 ≤ (f ∘ h2) y :=
    by
    simp_rw [h2]; simp_rw [union_equiv]; simp
    simp_rw [coef]; simp_rw [h]; simp only [forall_const, imp_true_iff]
  have hdis' := disjoint_aux In HI
  have h5 : ∀ x : ℕ, Finset (coef (In x)) := by intro x; rw [coef]; exact Finset.univ
  have hg : ∀ x : ℕ, coef (In x) = {y : ℤ × ℤ | y ∈ In x} := by intro x; rfl
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint (coef (In a)) (coef (In b)) :=
    by
    intro a b hab; simp_rw [coef]
    rw [Finset.disjoint_coe]; apply hdis'; exact hab
  have h3 := summable_disjoint_union_of_nonneg hdis h22
  have h4 : Summable f ↔ Summable (f ∘ h2) := by have := Equiv.summable_iff h2; rw [this]
  rw [h4]
  rw [h3]
  simp only [Function.comp_apply]
  dsimp
  have h6 : ∀ x : ℕ, ∑' y : ↥(coef (In x)), f (h2 ⟨y, _⟩) = ∑ y in In x, f y := by simp only;
    intro x; apply Finset.tsum_subtype'
  simp_rw [h6]
  simp only [and_iff_right_iff_imp]
  simp_rw [h2]
  rw [union_equiv]
  simp only [Equiv.coe_fn_mk, Subtype.coe_mk]
  intro H x
  rw [hg]
  apply Finset.summable
  apply unionmem

theorem tsum_lemma (f : ℤ × ℤ → ℝ) (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i)
    (hs : Summable f) : ∑' x, f x = ∑' n : ℕ, ∑ x in In n, f x :=
  by
  let h2 := union_equiv In HI
  have hdis' := disjoint_aux In HI
  have h5 : ∀ x : ℕ, Finset (coef (In x)) := by intro x; rw [coef]; exact Finset.univ
  have hg : ∀ x : ℕ, coef (In x) = {y : ℤ × ℤ | y ∈ In x} := by intro x; rfl
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint (coef (In a)) (coef (In b)) :=
    by
    intro a b hab; simp_rw [coef]
    rw [Finset.disjoint_coe]; apply hdis'; exact hab
  have h6 : ∀ x : ℕ, ∑' y : ↥(coef (In x)), f (h2 ⟨y, _⟩) = ∑ y in In x, f y := by simp only;
    intro x; apply Finset.tsum_subtype'
  simp_rw [h6]
  have HS : Summable (f ∘ h2) := by rw [Equiv.summable_iff h2]; exact hs
  have HH := tsum_disjoint_union_of_nonneg' hdis HS
  simp at HH 
  have := Equiv.tsum_eq h2 f
  rw [← this]
  rw [HH]
  simp_rw [h6]
  apply unionmem

theorem tsum_lemma' (f : ℤ × ℤ → ℂ) (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i)
    (hs : Summable f) : ∑' x, f x = ∑' n : ℕ, ∑ x in In n, f x :=
  by
  let h2 := union_equiv In HI
  have hdis' := disjoint_aux In HI
  have h5 : ∀ x : ℕ, Finset (coef (In x)) := by intro x; rw [coef]; exact Finset.univ
  have hg : ∀ x : ℕ, coef (In x) = {y : ℤ × ℤ | y ∈ In x} := by intro x; rfl
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint (coef (In a)) (coef (In b)) :=
    by
    intro a b hab
    simp_rw [coef]
    rw [Finset.disjoint_coe]
    apply hdis'
    exact hab
  have h6 : ∀ x : ℕ, ∑' y : ↥(coef (In x)), f (h2 ⟨y, _⟩) = ∑ y in In x, f y :=
    by
    simp only
    intro x
    apply Finset.tsum_subtype'
  simp_rw [h6]
  have HS : Summable (f ∘ h2) := by rw [Equiv.summable_iff h2]; exact hs
  have HH := tsum_disjoint_union_of_nonneg'' hdis HS
  simp at HH 
  have := Equiv.tsum_eq h2 f
  rw [← this]
  rw [HH]
  simp_rw [h6]
  apply unionmem

theorem realpow (n : ℕ) (k : ℤ) : (n : ℝ) ^ ((k : ℝ) - 1) = n ^ (k - 1) :=
  by
  have := Real.rpow_int_cast (n : ℝ) (k - 1)
  rw [← this]
  simp only [Int.cast_one, Int.cast_sub]

theorem summable_if_complex_abs_summable {f : α → ℂ} :
    (Summable fun x => Complex.abs (f x)) → Summable f :=
  by
  intro h
  apply summable_of_norm_bounded (fun x => Complex.abs (f x)) h
  intro i
  unfold norm
  exact complete_of_proper

theorem complex_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (∑ i in s, f i) ≤ ∑ i in s, Complex.abs (f i) :=
  abv_sum_le_sum_abv (fun k : ι => f k) s

theorem upper_gt_zero (z : ℍ) : 0 < (z : ℂ).im :=
  by
  have H := z.property
  simp at H 
  apply H

/-- Auxilary function use for bounding Eisentein series-/
def lb (z : ℍ) : ℝ :=
  (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2

theorem lb_pos (z : ℍ) : 0 < lb z := by
  rw [lb]
  simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re]
  have H1 : 0 < z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2 :=
    by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    nlinarith
    have h1 : z.1.2 ^ 4 = z.1.2 ^ 2 * z.1.2 ^ 2
    ring_nf
    rw [h1]
    apply mul_pos
    simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe]
    have := upper_gt_zero z
    rw [pow_two]
    apply mul_pos
    exact this
    exact this
    simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe]
    have := upper_gt_zero z
    rw [pow_two]
    apply mul_pos
    exact this
    exact this
  have H2 : 0 < (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 := by nlinarith
  have H3 :
    (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 =
      (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) * ((z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2)⁻¹ :=
    by ring
  simp at H3 
  rw [H3]
  have H4 : 0 < ((z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2)⁻¹ := by rw [inv_pos]; exact H2
  apply mul_pos H1 H4

/-- This function is used to give an upper bound on Eisenstein series-/
def rfunct (z : ℍ) : ℝ :=
  min (Real.sqrt (z.1.2 ^ 2)) (Real.sqrt (lb z))

theorem rfunct_pos (z : ℍ) : 0 < rfunct z :=
  by
  have H := z.property; simp at H 
  rw [rfunct]
  simp only [lt_min_iff, Real.sqrt_pos, UpperHalfPlane.coe_im, Subtype.val_eq_coe]
  constructor
  rw [pow_two]
  apply mul_pos
  exact H
  exact H
  apply lb_pos

theorem alem (a b c : ℝ) : a - b ≤ a + c ↔ -b ≤ c :=
  by
  have : a - b = a + -b := by ring
  constructor
  rw [this]
  simp_rw [add_le_add_iff_left]
  simp
  rw [this]
  simp_rw [add_le_add_iff_left]
  simp

theorem ineq1 (x y d : ℝ) : 0 ≤ d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 :=
  by
  have h1 :
    d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 =
      (d * (x ^ 2 + y ^ 2) + x) ^ 2 :=
    by ring
  rw [h1]
  nlinarith

theorem lowbound (z : ℍ) (δ : ℝ) :
    (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 ≤
      (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 :=
  by
  simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re]
  have H1 :
    (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 = δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + 2 * δ * z.1.1 + 1 :=
    by ring
  simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re] at H1 
  rw [H1]
  rw [div_le_iff]
  simp only
  have H2 :
    (δ ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) + 2 * δ * (z : ℂ).re + 1) *
        ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 =
      δ ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 3 +
          2 * δ * (z : ℂ).re * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 +
        ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 :=
    by ring
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H2 
  rw [H2]
  rw [← sub_nonneg]
  have H3 :
    ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 - ((z : ℂ).im ^ 4 + ((z : ℂ).re * (z : ℂ).im) ^ 2) =
      (z : ℂ).re ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) :=
    by ring
  have H4 :
    δ ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 3 +
            2 * δ * (z : ℂ).re * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 +
          ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 -
        ((z : ℂ).im ^ 4 + ((z : ℂ).re * (z : ℂ).im) ^ 2) =
      ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) *
        (δ ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 +
            2 * δ * (z : ℂ).re * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) +
          (z : ℂ).re ^ 2) :=
    by ring
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H4 
  rw [H4]
  have H5 :
    0 ≤
      δ ^ 2 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) ^ 2 +
          2 * δ * (z : ℂ).re * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) +
        (z : ℂ).re ^ 2 :=
    by apply ineq1
  have H6 : 0 ≤ (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 := by nlinarith
  apply mul_nonneg H6 H5
  have H7 := z.property; simp at H7 
  have H8 : 0 < (z : ℂ).im ^ 2 := by simp only [H7, pow_pos, UpperHalfPlane.coe_im]
  have H9 : 0 < (z : ℂ).im ^ 2 + (z : ℂ).re ^ 2 := by nlinarith
  apply pow_two_pos_of_ne_zero
  nlinarith

theorem auxlem (z : ℍ) (δ : ℝ) :
    rfunct z ≤ Complex.abs ((z : ℂ) + δ) ∧ rfunct z ≤ Complex.abs (δ * (z : ℂ) + 1) :=
  by
  constructor
  · rw [rfunct]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt ((z : ℂ).im ^ 2) ≤
        Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) :=
      by
      rw [Real.sqrt_le_sqrt_iff]
      nlinarith; nlinarith
    simp at *
    left
    rw [norm_sq_apply]
    simp
    simp_rw [H1]
  · rw [rfunct]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt (lb z) ≤
        Real.sqrt
          ((δ * (z : ℂ).re + 1) * (δ * (z : ℂ).re + 1) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
      by
      rw [lb]
      rw [Real.sqrt_le_sqrt_iff]
      have := lowbound z δ
      rw [← pow_two]
      rw [← pow_two]
      simp only [UpperHalfPlane.coe_im, Subtype.val_eq_coe, UpperHalfPlane.coe_re] at *
      apply this
      nlinarith
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1 
    rw [norm_sq_apply]
    right
    simp
    simp_rw [H1]

theorem le_of_pow' (a b : ℝ) (k : ℕ) (h : 0 ≤ a) (h2 : 0 ≤ b) (h3 : a ≤ b) : a ^ k ≤ b ^ k :=
  pow_le_pow_of_le_left h h3 k

theorem baux (a : ℝ) (k : ℕ) (b : ℂ) (h : 0 ≤ a) (h2 : a ≤ Complex.abs b) :
    a ^ k ≤ Complex.abs (b ^ k) := by
  rw [Complex.abs_pow]
  apply pow_le_pow_of_le_left
  exact h
  exact h2

theorem baux2 (z : ℍ) (k : ℕ) : Complex.abs (rfunct z ^ k) = rfunct z ^ k :=
  by
  norm_cast
  let a := rfunct z
  simp
  have ha : 0 ≤ a := by simp_rw [a]; have := rfunct_pos z; apply le_of_lt this
  have := Complex.abs_of_nonneg ha
  norm_cast at this 
  simp_rw [a] at this 
  rw [this]

theorem auxlem2 (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (h2 : x ∈ square n) (k : ℕ) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((z : ℂ) + (x.2 : ℂ) / (x.1 : ℂ)) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by apply baux2
  norm_cast at H1 
  rw [H1]
  apply baux
  have := rfunct_pos z
  apply le_of_lt this
  have := auxlem z (x.2 / x.1 : ℝ)
  norm_cast at this 
  apply this.1

theorem auxlem3 (z : ℍ) (n : ℕ) (x : ℤ × ℤ) (h2 : x ∈ square n) (k : ℕ) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ k) :=
  by
  norm_cast
  have H1 := baux2 z k
  norm_cast at H1 
  rw [H1]
  apply baux
  have := rfunct_pos z
  apply le_of_lt this
  have := auxlem z (x.1 / x.2 : ℝ)
  norm_cast at *
  apply this.2

end EisensteinSeries

