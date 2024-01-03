import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup


local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

def SpecialLinearGroup.transpose ( A:  Matrix.SpecialLinearGroup n R)  :
  Matrix.SpecialLinearGroup n R  := by
  use A.1.transpose
  rw [Matrix.det_transpose]
  apply A.2



def gcd_one_to_SL (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![a, -Int.gcdB a b;  b, Int.gcdA a b]
  simp only [Matrix.det_fin_two_of, neg_mul, sub_neg_eq_add]
  have := Int.gcd_eq_gcd_ab a b
  rw [hab] at this
  simp only [Nat.cast_one] at this
  rw [this]
  ring

def gcd_one_to_SL_bot_row (a b : ℤ) (hab : a.gcd b = 1) : SL(2, ℤ) := by
  use !![ Int.gcdB a b,  -Int.gcdA a b; a, b]
  simp
  have := Int.gcd_eq_gcd_ab a b
  rw [hab] at this
  simp at this
  rw [this]
  ring


lemma SL_to_gcd_one_fst_col (A: SL(2,ℤ)) : (A.1 0 0).gcd (A.1 0 1) = 1 := by
    rw [Int.gcd_eq_one_iff_coprime, IsCoprime]
    refine ⟨ (A.1 1 1), -(A.1 1 0), ?_⟩
    have T := Matrix.det_fin_two A.1
    simp at *
    ring_nf
    rw [mul_comm]
    have : A.1 0 1 * A.1 1 0 = A.1 1 0 * A.1 0 1 := by apply mul_comm
    rw [this] at T
    exact T.symm

/-- A vector of coprime entries multiplied by a matrix in `SL(2,ℤ)` has coprime entries-/
lemma SL2_gcd (a b : ℤ) (hab : a.gcd b = 1) (A : SL(2,ℤ)) :
  (Matrix.vecMul (![a,b]) A.1 0).gcd (Matrix.vecMul (![a,b]) A.1 1) = 1  := by
    let C := SpecialLinearGroup.transpose ((gcd_one_to_SL a b hab)) * A
    have := SL_to_gcd_one_fst_col C
    simp at this
    rw [SpecialLinearGroup.transpose, gcd_one_to_SL] at this
    simp at this
    norm_cast at this
