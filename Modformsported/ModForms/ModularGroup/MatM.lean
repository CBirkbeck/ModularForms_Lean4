import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Data.Complex.Basic



--import .matrix_groups
--import .matrix_groups
--  This is an attempt to update the kbb birthday repo, so most is not orginal to me
--  This is an attempt to update the kbb birthday repo, so most is not orginal to me
open Finset

open Matrix

open scoped Matrix

section

universe u

variable (n : Type _) [DecidableEq n] [Fintype n]  (m : ℤ)

def IntegralMatricesWithDeterminant (m : ℤ) :=
  { A : Matrix n n ℤ // A.det = m }

theorem SLnZ_eq_Mat_1 : SpecialLinearGroup n ℤ = IntegralMatricesWithDeterminant n 1 := by rfl

instance coeMatrix : CoeOut (IntegralMatricesWithDeterminant n m) (Matrix n n ℤ) :=
    ⟨fun A => A.val⟩
  

instance coeFun : CoeFun (IntegralMatricesWithDeterminant n m) fun _ => n → n → ℤ
    where coe A := A.val

def toLin' (A : IntegralMatricesWithDeterminant n m) :=
  Matrix.toLin' A.val

namespace IntegralMatricesWithDeterminante

theorem ext_iff (A B : IntegralMatricesWithDeterminant n m) : A = B ↔ ∀ i j, A i j = B i j :=
  Iff.trans Subtype.ext_iff_val ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]
theorem ext (A B : IntegralMatricesWithDeterminant n m) : (∀ i j, A i j = B i j) → A = B :=
  by
  rw [ext_iff]
  simp

@[simp]
theorem mat_m_vals (A : IntegralMatricesWithDeterminant n m) : ∀ i j, A i j = A.1 i j := by
  intro i j; rfl

def sLnZM (m : ℤ) :
    SpecialLinearGroup n ℤ →
      IntegralMatricesWithDeterminant n m → IntegralMatricesWithDeterminant n m :=
  fun A B => ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩

theorem one_smul' :
    ∀ M : IntegralMatricesWithDeterminant n m, sLnZM n m (1 : SpecialLinearGroup n ℤ) M = M :=
  by
  intro M
  rw [sLnZM]
  simp

theorem mul_smul' :
    ∀ A B : SpecialLinearGroup n ℤ,
      ∀ M : IntegralMatricesWithDeterminant n m,
        sLnZM n m (A * B) M = sLnZM n m A (sLnZM n m B M) :=
  by
  intro A B
  simp [sLnZM]
  simp [Matrix.mul_assoc]

instance (m : ℤ) : MulAction (SpecialLinearGroup n ℤ) (IntegralMatricesWithDeterminant n m)
    where
  smul := sLnZM n (m : ℤ)
  one_smul := one_smul' n (m : ℤ)
  mul_smul := mul_smul' n (m : ℤ)

variable (A : SpecialLinearGroup n ℤ) (M : IntegralMatricesWithDeterminant n m)

@[simp]
theorem smul_is_mul (A : SpecialLinearGroup n ℤ) (M : IntegralMatricesWithDeterminant n m) :
    (A • M).1 = A * M := by
  simp [sLnZM]
  rfl

instance : Coe (IntegralMatricesWithDeterminant n 1) (SpecialLinearGroup n ℤ) :=
  ⟨fun a => ⟨a.1, a.2⟩⟩

section Neg

variable (B : IntegralMatricesWithDeterminant n m) [Fact (Even (Fintype.card n))]

instance : Neg (IntegralMatricesWithDeterminant n m) :=
  ⟨fun g =>
    ⟨-g, by
      have := det_smul g.val (-1)
      simp at this 
      rw [this]
      have h : (Even (Fintype.card n)) := by apply Fact.out
      simp [Even.neg_one_pow, h ]
      have gdet := g.property
      simp at gdet 
      exact gdet⟩⟩

@[simp]
theorem mat_m_coe_neg (g : IntegralMatricesWithDeterminant n m) : ↑(-g) = -(↑g : Matrix n n ℤ) :=
  rfl

@[simp]
theorem mat_m_neg_elt (g : IntegralMatricesWithDeterminant n m) :
    ∀ i j, (↑(-g) : Matrix n n ℤ) i j = -g i j := by 
    intro i j
    rw [mat_m_coe_neg]
    simp 

end Neg

end IntegralMatricesWithDeterminante

end

