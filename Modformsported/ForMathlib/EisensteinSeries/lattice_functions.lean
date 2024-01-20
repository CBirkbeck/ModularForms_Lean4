import Mathlib.Data.Complex.Abs
import Mathlib.Data.IsROrC.Basic

open Complex

open scoped BigOperators NNReal Classical Filter Matrix

noncomputable section

namespace EisensteinSeries

/-- For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that the maximum of the
absolute values of the pair is `m` -/
def square (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-m) (m)) ×ˢ (Finset.Icc (-m) (m))).filter fun x =>
    max x.1.natAbs x.2.natAbs = m

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

theorem square_size' (n : ℕ) (h : 1 ≤ n) : Finset.card (square n) = 8 * n :=
  by
  have := square_size (n-1)
  convert this
  norm_cast
  repeat {exact Nat.eq_add_of_sub_eq h rfl}

theorem squares_cover_all (y : ℤ × ℤ) : ∃! i : ℕ, y ∈ square i :=
  by
  use max y.1.natAbs y.2.natAbs
  simp only [square_mem, and_self_iff, forall_eq']

/-
theorem squares_are_disjoint : ∀ i j : ℕ, i ≠ j → Disjoint (square i) (square j) := by
  apply disjoint_aux
  apply squares_cover_all
-/

theorem square_zero : square (0) = {(0, 0)} := by rfl

theorem square_zero_card : Finset.card (square 0) = 1 :=
  by
  rw [square_zero]
  rfl

lemma Complex_abs_square_left_ne (n : ℕ) (x : ℤ × ℤ) (h : x ∈ square n)
  (hx : Complex.abs (x.1) ≠ n) : Complex.abs (x.2) = n := by
  simp at h
  norm_cast at *
  have ht := max_choice (Int.natAbs x.1) (Int.natAbs x.2)
  rw [h] at ht
  cases' ht with h1 h2
  rw [h1] at hx
  exfalso
  have hh : Complex.abs (x.1) = Int.natAbs x.1 := by
    have := (int_cast_abs x.1).symm
    convert this
    rw [Int.cast_natAbs]
    norm_cast
  rw [hh] at hx
  simp at hx
  rw [h2]
  have := (int_cast_abs x.2).symm
  convert this
  rw [Int.cast_natAbs]
  norm_cast
