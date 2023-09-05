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
import Mathlib.Data.Finset.Basic

open Complex

open ModularGroup

open scoped BigOperators NNReal Classical Filter Matrix UpperHalfPlane

attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun



local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

noncomputable section

namespace EisensteinSeries

-- This is the permutation of the summation index coming from the moebius action
def MoebiusPerm (A : SL(2,ℤ)) : ℤ × ℤ → ℤ × ℤ := fun z =>
  (z.1 * A.1 0 0 + z.2 * A.1 1 0, z.1 * A.1 0 1 + z.2 * A.1 1 1)

theorem det_SL_eq_one (M : SL(2,ℤ)) : M.1 0 0 * M.1 1 1 -(M.1 0 1 * M.1 1 0) = 1 := by 
  have H := Matrix.det_fin_two M.1
  simp at *
  rw [← H]

lemma MoebiusPerm_left_inv (A : SL(2,ℤ)) (z : ℤ × ℤ) : MoebiusPerm A⁻¹ (MoebiusPerm A z) = z := by
    simp_rw [MoebiusPerm]
    ring_nf
    have hdet := det_SL_eq_one A
    have hi := Matrix.SpecialLinearGroup.SL2_inv_expl A
    rw [hi] at *
    simp at *
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

lemma MoebiusPerm_right_inv (A : SL(2,ℤ)) (z : ℤ × ℤ) : MoebiusPerm A (MoebiusPerm A⁻¹ z) = z := by
    have := MoebiusPerm_left_inv A⁻¹
    rw [inv_inv] at this 
    apply this

def MoebiusEquiv (A : SL(2,ℤ)) : ℤ × ℤ ≃ ℤ × ℤ
    where
  toFun := MoebiusPerm A
  invFun := MoebiusPerm A⁻¹
  left_inv z := by apply MoebiusPerm_left_inv A
  right_inv z := by apply MoebiusPerm_right_inv A


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
theorem squares_are_disjoint : ∀ i j : ℕ, i ≠ j → Disjoint (square i) (square j) := by
  apply disjoint_aux 
  apply squares_cover_all

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


-- Some summable lemmas
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

/-
theorem realpow (n : ℕ) (k : ℤ) : (n : ℝ) ^ ((k : ℝ) - 1) = n ^ (k - 1) :=
  by
  have := Real.rpow_int_cast (n : ℝ) (k - 1)
  simp only [Int.cast_one, Int.cast_sub]
-/

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

theorem rfunct_ne_zero (z : ℍ) :  rfunct z ≠ 0 := by 
  by_contra h
  have := rfunct_pos z
  rw [h] at this
  norm_cast at *

lemma rfunct_mul_n_pos (k : ℕ) (z : ℍ) (n : ℕ)  (hn : 1 ≤ n) : 
  0 < (Complex.abs (rfunct z ^ (k : ℤ) * n ^ (k : ℤ))) := by
  apply Complex.abs.pos
  apply mul_ne_zero
  norm_cast
  apply pow_ne_zero
  apply EisensteinSeries.rfunct_ne_zero  
  norm_cast
  apply pow_ne_zero 
  linarith

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
 