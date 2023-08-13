import Modformsported.ModForms.ModularGroup.ModGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Modformsported.ForMathlib.ModForms2
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Setoid.Partition
import Modformsported.ModForms.Riemzeta
import Modformsported.ModForms.HolomorphicFunctions
import Mathlib.Order.Filter.Archimedean
import Modformsported.ModForms.WeierstrassMTest
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.Modular
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic


universe u v w

open Complex

open ModularGroup

open IntegralMatricesWithDeterminante

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane

attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun

local notation "SL2Z" => Matrix.SpecialLinearGroup (Fin 2) ℤ

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

noncomputable section

namespace EisensteinSeries

/-
theorem ridic (a b c d : ℤ) : a * d - b * c = 1 → a * d - c * b = 1 := by intro h; linarith

theorem ridic2 (a b c d z : ℤ) (h : a * d - b * c = 1) : z * d * a - z * c * b = z := by ring_nf;
  rw [h]; rw [one_mul]
  -/

-- This is the permutation of the summation index coming from the moebius action
def indPerm (A : SL2Z) : ℤ × ℤ → ℤ × ℤ := fun z =>
  (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1)

theorem det_sl_one (M : SL2Z) : M.1 0 0 * M.1 1 1 -(M.1 0 1 * M.1 1 0) = 1 := by apply det_m

def indEquiv (A : SL2Z) : ℤ × ℤ ≃ ℤ × ℤ
    where
  toFun := indPerm A
  invFun := indPerm A⁻¹
  left_inv z := by
    simp_rw [indPerm]
    ring_nf
    have hdet := det_sl_one A
    simp only [SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *
    ring_nf
    have h1: z.fst * A.1 0 0 * A.1 1 1 - z.fst * A.1 0 1 * A.1 1 0 = z.fst := by
      trans (z.fst * (A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0))
      ring
      rw [hdet]
      apply mul_one
    have h2 :  A.1 0 0 * A.1 1 1* z.snd -  A.1 0 1 * A.1 1 0 * z.snd = z.snd := by
      trans ((A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0)* z.snd )
      ring
      rw [hdet]
      apply one_mul
    rw [h1,h2]  
  right_inv z := by
    simp_rw [indPerm]
    ring_nf
    have hdet := det_sl_one A
    simp only [SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *
    ring_nf
    have h1: z.fst * A.1 1 1 * A.1 0 0 - z.fst * A.1 0 1 * A.1 1 0 = z.fst := by
      trans (z.fst * (A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0))
      ring
      rw [hdet]
      apply mul_one
    have h2 :  A.1 1 1 * A.1 0 0* z.snd -  A.1 0 1 * A.1 1 0 * z.snd = z.snd := by
      trans ((A.1 0 0 * A.1 1 1 -  A.1 0 1 * A.1 1 0)* z.snd )
      ring
      rw [hdet]
      apply one_mul
    rw [h1,h2]   

@[simp]
theorem ind_simp (A : SL2Z) (z : ℤ × ℤ) :
    indEquiv A z = (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1) := by rfl

theorem max_aux'' (a b n : ℕ) (h : max a b = n) : a = n ∨ b = n :=
  by
  rw [← h]
  have hh := max_choice a b
  cases hh
  left
  linarith
  right
  linarith
  

theorem max_aux3 (a b n : ℕ) (h : max a b = n) : a ≤ n ∧ b ≤ n := by 
    rw [← h]
    simp only [ge_iff_le, le_max_iff, le_refl, true_or, or_true, and_self]

/-- For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that the maximum of the
absolute values of the pair is `m` -/
def square (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-m) (m)) ×ˢ (Finset.Icc (-m) (m))).filter fun x =>
    max x.1.natAbs x.2.natAbs = m

/-- For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that..-/
def square2 (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-m) (m)) ×ˢ  {(m)}) ∪ 
  (Finset.Icc (-m ) (m)) ×ˢ {-(m)} ∪
  ({(m)} : Finset ℤ) ×ˢ (Finset.Icc (-(m) + 1) (m-1)) ∪
  ({-(m)} : Finset ℤ) ×ˢ (Finset.Icc (-(m) + 1) (m-1))

lemma Icc_sub (m : ℤ) (hm : 1 ≤ m) : (Finset.Icc (-(m) + 1) (m-1)) ⊆  (Finset.Icc (-m) (m)) := by 
  refine Iff.mpr (Finset.Icc_subset_Icc_iff ?h₁) ?_
  linarith
  constructor
  linarith
  linarith


-- a re-definition in simp-normal form
lemma square_eq (m : ℤ) :
  square m = ((Finset.Icc (-m) (m)) ×ˢ (Finset.Icc (-m) (m))).filter fun x => max |x.1| |x.2| = m :=
  by simp [square]

open Finset

lemma mem_square_aux {m : ℤ} {i} : i ∈ Icc (-m) m ×ˢ Icc (-m) m ↔ max |i.1| |i.2| ≤ m :=
  by simp [abs_le]

lemma square_disj {n : ℤ} : Disjoint (square (n+1)) (Icc (-n) n ×ˢ Icc (-n) n) := by
  rw [square_eq]
  simp only [Finset.disjoint_left, mem_filter, mem_square_aux]
  intros x y
  simp_all

-- copied from the nat version, probably it already exists somewhere?
lemma Int.le_add_one_iff {m n : ℤ} : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 :=
  ⟨fun h =>
    match eq_or_lt_of_le h with
    | Or.inl h => Or.inr h
    | Or.inr h => Or.inl <| Int.lt_add_one_iff.1 h,
    Or.rec (fun h => le_trans h <| Int.le.intro 1 rfl) le_of_eq⟩

lemma square_union {n : ℤ} :
    square (n+1) ∪ Icc (-n) n ×ˢ Icc (-n) n = Icc (-(n+1)) (n+1) ×ˢ Icc (-(n+1)) (n+1) := by
  ext x
  rw [mem_union, square_eq, mem_filter, mem_square_aux, mem_square_aux,
    and_iff_right_of_imp le_of_eq, Int.le_add_one_iff, or_comm]

lemma square_disjunion (n : ℤ) :
  (square (n+1)).disjUnion (Icc (-n) n ×ˢ Icc (-n) n) square_disj =
    Icc (-(n+1)) (n+1) ×ˢ Icc (-(n+1)) (n+1) :=
  by rw [disjUnion_eq_union, square_union]

theorem square_size (n : ℕ) : Finset.card (square (n + 1)) = 8 * (n + 1) := by
  have : (((square (n+1)).disjUnion (Icc (-n : ℤ) n ×ˢ Icc (-n : ℤ) n) square_disj).card : ℤ) =
    (Icc (-(n+1 : ℤ)) (n+1) ×ˢ Icc (-(n+1 : ℤ)) (n+1)).card
  · rw [square_disjunion]
  rw [card_disjUnion, card_product, Nat.cast_add, Nat.cast_mul, card_product, Nat.cast_mul,
    Int.card_Icc, Int.card_Icc, Int.toNat_sub_of_le, Int.toNat_sub_of_le,
    ←eq_sub_iff_add_eq] at this
  · rw [←Nat.cast_inj (R := ℤ), this, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add_one]
    ring_nf
  · linarith
  · linarith

/-
theorem square2_card (n : ℕ) (h : 1 ≤ n) : (Finset.card (square2 n) : ℤ) = 8 * n :=
  by
  rw [square2, Finset.card_union_eq, Finset.card_union_eq, Finset.card_union_eq]
  simp_rw [Finset.card_product]
    --Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product]
  · simp only [Finset.card_singleton, mul_one, one_mul]
    have hn : -(n : ℤ) ≤ n + 1 := by linarith
    have hn2 : -(n : ℤ) +1  ≤ n-1 +1 := by linarith
    have r1 := Int.card_Icc_of_le (-(n : ℤ)) (n) hn
    have r2 := Int.card_Icc_of_le (-(n : ℤ) + 1) (n-1) hn2
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
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Ne.def, Finset.mem_union, Finset.mem_singleton, neg_add_le_iff_le_add,
      Finset.mem_product, Finset.mem_Icc] at * 
    cases' ha with ha ha
    have hbb := hb.2
    have haa:=ha.2
    by_contra H
    rw [← H] at hbb 
    rw [haa] at hbb 
    have hbb2:= hbb.2
    simp only [le_sub_self_iff] at hbb2 

    by_contra H
    have hbb := hb.2
    have haa:=ha.2
    rw [← H] at hbb 
    rw [haa] at hbb 
    have hbb1:= hbb.1
    simp only [add_right_neg] at hbb1  
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Ne.def, Finset.mem_union, Finset.union_assoc, Finset.mem_singleton,
      neg_add_le_iff_le_add, Finset.mem_product, Finset.mem_Ico] at *
    by_contra H
    cases' ha with ha ha
    · have hbb := hb.2
      have haa := ha.2
      rw [← H] at hbb 
      rw [← haa] at hbb 
      simp [lt_self_iff_false, and_false_iff] at hbb 
    cases' ha with ha ha
    · have hbb := hb.2
      have haa := ha.2
      rw [← H] at hbb 
      rw [haa] at hbb 
      rw [Finset.mem_Icc] at hbb
      have hbb1:= hbb.1
      simp only [add_le_iff_nonpos_right] at hbb1 
    · have hbb := hb.1
      have haa := ha.1
      rw [H] at haa 
      rw [hbb] at haa 
      have hv := eq_zero_of_neg_eq haa
      simp only [Int.coe_nat_eq_zero] at hv 
      rw [hv] at h 
      simp only [Nat.one_ne_zero, le_zero_iff] at h 


theorem natAbs_inter (a : ℤ) (n : ℕ) (h : a.natAbs < n) : a < (n : ℤ) ∧ 0 < (n : ℤ) + a :=
  by
  have := Int.natAbs_eq a
  cases' this with this this
  rw [this]
  constructor
  norm_cast
  norm_cast
  simp only [add_pos_iff]
  left
  have h1 : 0 ≤ Int.natAbs a := zero_le (Int.natAbs a)
  linarith
  rw [this]
  constructor
  rw [neg_lt_iff_pos_add]
  norm_cast
  simp only [add_pos_iff]
  have h1 : 0 ≤ Int.natAbs a := zero_le (Int.natAbs a)
  left
  linarith
  rw [← Int.ofNat_lt] at h 
  rw [← sub_pos] at h 
  simpa using h

theorem natAbs_inter2 (a : ℤ) (n : ℕ) (h : a.natAbs ≤ n) : a ≤ (n : ℤ) ∧ 0 ≤ (n : ℤ) + a :=
  by
  have := lt_or_eq_of_le h; 
  cases' this with this this
  have H := natAbs_inter a n this; 
  have H1 := le_of_lt H.1; have H2 := le_of_lt H.2; simp [H1, H2];
  rw [← this]
  constructor; exact Int.le_natAbs; rw [add_comm]; rw [← neg_le_iff_add_nonneg'];
  rw [← Int.abs_eq_natAbs]
  simp_rw [neg_le_abs_self]

-/
theorem natAbs_le_mem_Icc (a : ℤ) (n : ℕ) (h : Int.natAbs a ≤ n) : a ∈ Finset.Icc (-(n : ℤ)) (n) :=
  by
  simp
  have hm : max (a) (-a) ≤ n := by 
    have : ((Int.natAbs a) : ℤ) = |a| := by simp only [Int.coe_natAbs]
    rw [← abs_eq_max_neg]
    rw [← this]
    norm_cast 
  rw [max_le_iff] at hm
  constructor
  nlinarith
  exact hm.1

theorem natAbs_lt_mem_Icc (a : ℤ) (n : ℕ) (h : Int.natAbs a < n) : a ∈ Finset.Icc (-(n : ℤ)+1) (n-1) :=
  by
  simp
  have hm : max (a) (-a) < n := by 
    have : ((Int.natAbs a) : ℤ) = |a| := by simp only [Int.coe_natAbs]
    rw [← abs_eq_max_neg]
    rw [← this]
    norm_cast 
  rw [max_lt_iff] at hm
  constructor
  nlinarith
  nlinarith


@[simp]
theorem square_mem (n : ℕ) (x : ℤ × ℤ) : x ∈ square n ↔ max x.1.natAbs x.2.natAbs = n :=
  by
  constructor
  intro x
  rw [square] at x
  simp only [ge_iff_le,  Prod.forall, Finset.mem_filter] at x 
  have hx := x.2
  norm_cast at hx
  intro H
  rw [square]
  simp only [ge_iff_le, Prod.forall, Finset.mem_filter]
  constructor 
  simp only [ge_iff_le, Finset.mem_product]
  constructor
  apply natAbs_le_mem_Icc
  rw [← H]
  simp only [ge_iff_le, le_max_iff, le_refl, true_or]
  apply natAbs_le_mem_Icc
  rw [← H]
  simp only [ge_iff_le, le_max_iff, le_refl, or_true] 
  rw [H]


theorem square_mem' (n : ℕ) (x : ℤ × ℤ) :
    x ∈ square n ↔
      x.1.natAbs = n ∧ x.2.natAbs < n ∨
        x.2.natAbs = n ∧ x.1.natAbs < n ∨ x.1.natAbs = n ∧ x.2.natAbs = n :=
  by
  simp only [square_mem, ge_iff_le]
  constructor
  intro c1
  have := max_aux3 _ _ _ c1
  have H := max_aux'' _ _ _ c1
  have h1 := this.1
  have h2 := this.2
  rw [le_iff_lt_or_eq] at h2 
  rw [le_iff_lt_or_eq] at h1 
  cases' H with H H
  simp_rw [H]
  simp only [true_and, lt_self_iff_false, and_false, false_or]
  exact h2
  simp_rw [H]
  simp only [lt_self_iff_false, and_false, true_and, and_true, false_or]
  exact h1
  intro c2
  cases' c2 with c2 c2
  rw [c2.1]
  simp only [ge_iff_le, max_eq_left_iff]
  have := c2.2
  linarith
  cases' c2 with c2 c2
  rw [c2.1]
  simp only [ge_iff_le, max_eq_right_iff]
  have := c2.2
  linarith
  rw [c2.1, c2.2]
  simp only [max_self]

/-
theorem auxin (a : ℤ) (n : ℕ) (h : 0 < (n : ℤ) + a) : 1 ≤ (n : ℤ) + a := by assumption

theorem auxin2 (a : ℤ) (n : ℕ) (h : 0 < (n : ℤ) + a) : -(n : ℤ) ≤ a := by linarith

theorem cat (a b : ℤ) (n : ℕ) (h1 : b = (n : ℤ)) (h2 : -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ)) :
    b.natAbs = n ∧ (a.natAbs < n ∨ a.natAbs = n) :=
  by
  rw [h1]
  simp
  have := Int.natAbs_eq a
  cases' this with this this
  rw [this] at h2 
  norm_cast at h2 
  have h22 := h2.2
  exact lt_or_eq_of_le h22
  rw [this] at h2 
  have h22 := h2.1
  have H := lt_or_eq_of_le h22
  simp only [neg_lt_neg_iff, neg_inj] at H 
  norm_cast at H 
  have h234 : n = a.natAbs ↔ a.natAbs = n := comm
  rw [← h234]
  exact H

theorem cat1 (a b : ℤ) (n : ℕ) (h1 : b = -(n : ℤ)) (h2 : -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ)) :
    b.natAbs = n ∧ (a.natAbs < n ∨ a.natAbs = n) :=
  by
  rw [h1]
  simp
  have := Int.natAbs_eq a
  cases' this with this this
  rw [this] at h2 
  norm_cast at h2 
  have h22 := h2.2
  exact lt_or_eq_of_le h22
  rw [this] at h2 
  have h22 := h2.1
  have H := lt_or_eq_of_le h22
  simp only [neg_lt_neg_iff, neg_inj] at H 
  norm_cast at H 
  have h234 : n = a.natAbs ↔ a.natAbs = n := comm
  rw [← h234]
  exact H


    

theorem dog (a b : ℤ) (n : ℕ) (h1 : a = (n : ℤ)) (h2 : 1 ≤ (n : ℤ) + b ∧ b ≤ ((n : ℤ)-1)) :
    a.natAbs = n ∧ b.natAbs < n := by
  rw [h1]; simp; have := Int.natAbs_eq b; 
  cases' this with this this; 
  rw [this] at h2 ; 
  have hh : ((Int.natAbs b) : ℤ) < n := by linarith
  norm_cast at hh
  rw [this] at h2
  have hh : ((Int.natAbs b) : ℤ) < n := by linarith
  norm_cast at hh






theorem dog1 (a b : ℤ) (n : ℕ) (h1 : a = -(n : ℤ)) (h2 : 1 ≤ (n : ℤ) + b ∧ b ≤ (n : ℤ)-1) :
    a.natAbs = n ∧ b.natAbs < n := by
  rw [h1]; simp;  have := Int.natAbs_eq b; 
  cases' this with this this; 
  rw [this] at h2 ; 
  have hh : ((Int.natAbs b) : ℤ) < n := by linarith
  norm_cast at hh
  rw [this] at h2
  have hh : ((Int.natAbs b) : ℤ) < n := by linarith
  norm_cast at hh


-- example (s t : Set ℤ) (a : ℤ) (ha : a ∈ s) : ( s ⊆ t) →  a ∈ t := by exact fun a_1 => a_1 ha
-/
theorem square_zero : square (0) = {(0, 0)} := by rfl

/-
theorem square2_zero : square2 (0) = {(0, 0)} := by rfl

theorem sqr_eq_sqr2 (n : ℕ) : square n = square2 n :=
  by
  ext1
  by_cases hn0 : 1 ≤ n
  constructor
  intro H
  have HH := H
  rw [square_mem'] at HH
  rw [square2]
  rw [square] at H
  simp only [ge_iff_le, Nat.cast_max, Int.coe_natAbs, gt_iff_lt, lt_neg_self_iff, Finset.mem_product, 
    and_imp, Prod.forall, Finset.mem_filter] at H 
  simp only [Finset.mem_union, Finset.union_assoc, Finset.mem_product]
  rw [max_eq_iff] at H
  simp only [gt_iff_lt, lt_neg_self_iff] at H 
  have H1 := H.1
  cases' HH with H H
  have h1 := Int.natAbs_eq_iff.1 H.1
  cases' h1 with h1 h1
  right
  right
  left
  constructor
  simp [h1]
  exact (natAbs_lt_mem_Icc _ n) H.2
  right;right;right
  constructor
  simp [h1]
  exact (natAbs_lt_mem_Icc _ n) H.2
  cases' H with H H
  have h1 := Int.natAbs_eq_iff.1 H.1
  cases' h1 with h1 h1
  left
  constructor
  apply H1.1
  simp [h1]
  right; left
  constructor
  apply H1.1
  simp [h1]
  have h1 := Int.natAbs_eq_iff.1 H.1
  have h2 := Int.natAbs_eq_iff.1 H.2
  cases' h1 with h1 h1
  cases' h2 with h2 h2
  left
  constructor
  simp  [h1]
  simp [h2]
  right
  left
  constructor
  simp [h1]
  simp [h2]
  cases' h2 with h2 h2
  left
  constructor
  simp [h1]
  simp [h2]
  right; left
  constructor
  simp [h1]
  simp [h2]
  intro ha
  rw [square2] at ha 
  simp only [Finset.mem_union, Finset.union_assoc, Finset.mem_product, Finset.mem_Icc,
    neg_add_le_iff_le_add, Finset.mem_singleton] at ha 
  rw [square_mem']
  cases' ha with ha ha
  have := cat _ _ _ ha.2 ha.1
  simp_rw [this]
  simp only [true_and_iff, lt_self_iff_false, and_true_iff, false_or_iff, eq_self_iff_true,
    and_false_iff]
  exact this.2
  cases' ha with ha ha
  have := cat1 _ _ _ ha.2 ha.1
  simp_rw [this]
  simp
  exact this.2
  cases' ha with ha ha
  have := dog _ _ _ ha.1 ha.2
  simp_rw [this]
  simp only [true_or_iff, eq_self_iff_true, and_self_iff]
  have := dog1 _ _ _ ha.1 ha.2
  simp_rw [this]
  simp only [true_or_iff, eq_self_iff_true, and_self_iff] 
  simp at hn0
  simp_rw [hn0]
  rfl

-/

theorem square_size' (n : ℕ) (h : 1 ≤ n) : Finset.card (square n) = 8 * n :=
  by
  have := square_size (n-1)
  convert this
  norm_cast
  repeat {exact Nat.eq_add_of_sub_eq h rfl}



theorem Squares_are_disjoint : ∀ i j : ℕ, i ≠ j → Disjoint (square i) (square j) :=
  by
  intro i j hij
  rw [Finset.disjoint_iff_ne]
  intro a ha
  simp at ha 
  intro b hb
  simp at hb 
  by_contra h
  rw [h] at ha 
  rw [hb] at ha 
  induction ha
  induction h 
  cases a
  induction hb
  cases b
  dsimp at *
  simp at *
 

theorem Squares_cover_all : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ square i :=
  by
  intro y
  use max y.1.natAbs y.2.natAbs
  simp only [square_mem, and_self_iff, forall_eq']


theorem square_zero_card : Finset.card (square 0) = 1 :=
  by
  rw [square_zero]
  rfl

-- Some summable lemmas
variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

/-
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
-/
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

theorem disjoint_aux (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) :
    ∀ i j : ℕ, i ≠ j → Disjoint (In i) (In j) :=
  by
  intro i j h
  intro x h1 h2 a h3
  cases' a with a_fst a_snd
  dsimp at *
  simp at *
  have HI0 := HI a_fst a_snd
  have := ExistsUnique.unique HI0 (h1 h3) (h2 h3)
  rw [this] at h 
  simp at *
  

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

theorem realpow (n : ℕ) (k : ℤ) : (n : ℝ) ^ ((k : ℝ) - 1) = n ^ (k - 1) :=
  by
  have := Real.rpow_int_cast (n : ℝ) (k - 1)
  simp only [Int.cast_one, Int.cast_sub]

theorem summable_if_complex_abs_summable {f : α → ℂ} :
    (Summable fun x => Complex.abs (f x)) → Summable f :=
  by
  intro h
  apply summable_of_norm_bounded (fun x => Complex.abs (f x)) h
  intro i
  rfl
 

theorem complex_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (∑ i in s, f i) ≤ ∑ i in s, Complex.abs (f i) :=
  abv_sum_le_sum_abv (fun k : ι => f k) s

lemma upper_half_im_pow_pos (z : ℍ) (n : ℕ) : 0 < (z.1.2)^n := by 
    have:= pow_pos z.2 n
    norm_cast

/-- Auxilary function used for bounding Eisentein series-/
def lb (z : ℍ) : ℝ :=
  ((z.1.2 ^ (4 : ℕ) + (z.1.1 * z.1.2) ^ (2 : ℕ)) / (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)) ^ (2 : ℕ))

theorem lb_pos (z : ℍ) : 0 < lb z := by
  rw [lb]
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
  have H1 : 0 < z.1.2 ^ (4 : ℕ) + (z.1.1 * z.1.2) ^ (2 : ℕ) :=
    by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    have := pow_two_nonneg (z.1.1*z.1.2)
    simpa using this
    apply upper_half_im_pow_pos z 4
  have H2 : 0 < (z.1.1 ^ (2 : ℕ) + z.1.2 ^ (2 : ℕ)) ^ (2 : ℕ) := by 
    norm_cast
    apply pow_pos
    apply add_pos_of_nonneg_of_pos
    apply pow_two_nonneg
    have := upper_half_im_pow_pos z 2
    norm_cast at this
  norm_cast at *
  have := div_pos H1 H2
  norm_cast at *

/-- This function is used to give an upper bound on Eisenstein series-/
def rfunct (z : ℍ) : ℝ :=
  min (Real.sqrt (z.1.2 ^ (2))) (Real.sqrt (lb z))

theorem rfunct_pos (z : ℍ) : 0 < rfunct z :=
  by
  have H := z.property; simp at H 
  rw [rfunct]
  simp only [lt_min_iff, Real.sqrt_pos, UpperHalfPlane.coe_im]
  constructor
  have := upper_half_im_pow_pos z 2
  norm_cast at *
  apply lb_pos


theorem ineq1 (x y d : ℝ) : 0 ≤ d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 :=
  by
  have h1 :
    d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 + 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 =
      (d * (x ^ 2 + y ^ 2) + x) ^ 2 := by 
        norm_cast
        ring
  rw [h1]
  have := pow_two_nonneg  (d * (x ^ 2 + y ^ 2) + x)
  simp at *
  norm_cast at *


theorem lowbound (z : ℍ) (δ : ℝ) :
    (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 ≤
      (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 :=
  by
  simp only [UpperHalfPlane.coe_im,  UpperHalfPlane.coe_re]
  have H1 :
    (δ * z.1.1 + 1) ^ 2 + (δ * z.1.2) ^ 2 = δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) + 2 * δ * z.1.1 + 1 := by
      norm_cast
      ring
  simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1 
  rw [H1]
  rw [div_le_iff]
  simp only
  have H2 :
    (δ ^ 2 * ((z.1.1) ^ 2 + z.1.2 ^ 2) + 2 * δ * z.1.1 + 1) *
        (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 =
      δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 +
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
        (z.1.1^ 2 + z.1.2 ^ 2) ^ 2 := by 
          norm_cast
          ring
  --simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H2
  norm_cast at *
  simp at *
  rw [H2]
  rw [← sub_nonneg]
  have H3 :
    (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 - (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) =
      z.1.1 ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) :=by
        norm_cast 
        ring
  have H4 :
    δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 +
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
          (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 -
        (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) =
      (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
          z.1.1 ^ 2) :=by 
          norm_cast
          ring
  norm_cast at *        
  rw [H4]
  have H5 :
    0 ≤
      δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
        z.1.1 ^ 2 :=
    by apply ineq1
  have H6 : 0 ≤ z.1.1 ^ 2 + z.1.2 ^ 2 := by 
    norm_cast
    nlinarith  
  have HH :=mul_nonneg H6 H5
  simp at *
  norm_cast at *
  have H8 : 0 < z.1.2 ^ 2 := by 
    have := upper_half_im_pow_pos z 2
    norm_cast at *
  have H9 : 0 < z.1.2 ^ 2 + z.1.1 ^ 2 := by 
    norm_cast
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    apply pow_two_nonneg
    norm_cast at *
  norm_cast  
  apply sq_pos_of_ne_zero
  simp at H9
  norm_cast at H9
  linarith


theorem auxlem (z : ℍ) (δ : ℝ) :
    rfunct z ≤ Complex.abs ((z : ℂ) + δ) ∧ rfunct z ≤ Complex.abs (δ * (z : ℂ) + 1) := by
  constructor
  · rw [rfunct]
    rw [Complex.abs]
    simp
    have H1 :
      Real.sqrt ((z : ℂ).im ^ 2) ≤
        Real.sqrt (((z : ℂ).re + δ) * ((z : ℂ).re + δ) + (z : ℂ).im * (z : ℂ).im) :=
      by
      rw [Real.sqrt_le_sqrt_iff]
      norm_cast
      nlinarith; nlinarith
    simp at *
    left
    norm_cast
    simp
    rw [normSq_apply]
    simp
    norm_cast at *
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
      simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at *
      norm_cast at *
      nlinarith
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at H1 
    rw [normSq_apply]
    right
    simp at *
    norm_cast

theorem baux (a : ℝ) (k : ℕ) (b : ℂ) (h : 0 ≤ a) (h2 : a ≤ Complex.abs b) :
    a ^ k ≤ Complex.abs (b ^ k) := by
  have := pow_le_pow_of_le_left h h2 k
  norm_cast at *
  convert this
  simp only [cpow_nat_cast, map_pow]


theorem baux2 (z : ℍ) (k : ℕ) : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by
  have ha := (rfunct_pos z).le 
  have := Complex.abs_of_nonneg ha
  rw [←this]
  simp only [abs_ofReal, cpow_nat_cast, map_pow, _root_.abs_abs, Real.rpow_nat_cast]

theorem auxlem2 (z : ℍ) (x : ℤ × ℤ) (k : ℕ) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((z : ℂ) + (x.2 : ℂ) / (x.1 : ℂ)) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by apply baux2
  norm_cast at H1 
  rw [H1]
  have := auxlem z (x.2 / x.1 : ℝ)
  norm_cast at this 
  have HT := baux _ k _ ?_ this.1
  convert HT
  norm_cast
  norm_cast
  apply (rfunct_pos z).le


theorem auxlem3 (z : ℍ) (x : ℤ × ℤ) (k : ℕ) :
    Complex.abs ((rfunct z : ℂ) ^ k) ≤ Complex.abs (((x.1 : ℂ) / (x.2 : ℂ) * (z : ℂ) + 1) ^ k) :=
  by
  norm_cast
  have H1 : Complex.abs (rfunct z ^ k) = rfunct z ^ k := by apply baux2
  norm_cast at H1 
  rw [H1]
  have := auxlem z (x.1 / x.2 : ℝ)
  norm_cast at this 
  have HT := baux _ k _ ?_ this.2
  simp at *
  convert HT
  norm_cast
  norm_cast
  apply (rfunct_pos z).le

end EisensteinSeries
 