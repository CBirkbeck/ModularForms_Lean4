import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Hom.GroupAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Data.Complex.Basic
import Modformsported.ModForms.ModularGroup.MatM



--import .matrix_groups
--import .matrix_groups
--  This is an attempt to update the kbb birthday repo, so most is not orginal to me
--  This is an attempt to update the kbb birthday repo, so most is not orginal to me
open Finset

open Matrix

open scoped Matrix SpecialLinearGroup

section

universe u

variable (n : Type _) [DecidableEq n] [Fintype n] (m : ℤ)

namespace ModularGroup

attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun

local notation "SL2Z" => SpecialLinearGroup (Fin 2) ℤ

variable {R : Type _} [CommRing R]

theorem det_m (M : IntegralMatricesWithDeterminant (Fin 2) m) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = m :=
  by
  have H := Matrix.det_fin_two M.1
  simp at *
  have m2 := M.2
  rw [← H]
  simp_rw [← m2]

theorem det_one (M : SL2Z) : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by apply det_m

theorem det_onne (M : SL2Z) : M.1 0 0 * M.1 1 1 - M.1 1 0 * M.1 0 1 = 1 :=
  by
  have := det_one M
  have h1 : M.1 1 0 * M.1 0 1 = M.1 0 1 * M.1 1 0 := by apply mul_comm
  rw [h1]
  apply this

@[simp]
theorem mat_mul_expl (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
      (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
        (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
  by
  constructor; on_goal 2 => constructor; on_goal 2 => constructor
  all_goals
    simp only [mul_eq_mul]
    rw [Matrix.mul_apply]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    simp [Nat.succ_pos', lt_self_iff_false, dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty,
      not_le, Finset.range_zero, zero_add, add_right_inj, Fin.mk_one,ite_eq_left_iff]

@[simp]
theorem SL2Z_inv_a (A : SL2Z) : A⁻¹.1 0 0 = A.1 1 1 := by rw [SpecialLinearGroup.SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_b (A : SL2Z) : A⁻¹.1 0 1 = -A.1 0 1 := by rw [SpecialLinearGroup.SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_c (A : SL2Z) : A⁻¹.1 1 0 = -A.1 1 0 := by rw [SpecialLinearGroup.SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_d (A : SL2Z) : A⁻¹.1 1 1 = A.1 0 0 := by rw [SpecialLinearGroup.SL2_inv_expl]; simp

theorem m_a_b (m : ℤ) (A : SL2Z) (M N : IntegralMatricesWithDeterminant (Fin 2) m) :
    A • M = N ↔
      N 0 0 = A.1 0 0 * M 0 0 + A.1 0 1 * M 1 0 ∧
        N 0 1 = A.1 0 0 * M 0 1 + A.1 0 1 * M 1 1 ∧
          N 1 0 = A.1 1 0 * M 0 0 + A.1 1 1 * M 1 0 ∧ N 1 1 = A.1 1 0 * M 0 1 + A.1 1 1 * M 1 1 :=
  by
  have := mat_mul_expl A.1 M.1;
  constructor
  intro h
  rw [←h]; constructor ; apply this.1; constructor; apply this.2.1;
  constructor; apply this.2.2.1; apply this.2.2.2
  intro h
  ext i j;
  fin_cases i <;> fin_cases j;
  simp; rw [h.1]; convert this.1;
  simp; rw [h.2.1]; convert this.2.1; simp; rw [h.2.2.1]; convert this.2.2.1; simp; rw [h.2.2.2]
  convert this.2.2.2;

@[simp]
theorem SLnZ_M_a (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 0 0 = A.1 0 0 * M 0 0 + A.1 0 1 * M 1 0 := by
  apply (mat_mul_expl A.1 M).1

@[simp]
theorem SLnZ_M_b (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 0 1 = A.1 0 0 * M 0 1 + A.1 0 1 * M 1 1 := by
  apply (mat_mul_expl A.1 M).2.1

@[simp]
theorem SLnZ_M_c (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 1 0 = A.1 1 0 * M 0 0 + A.1 1 1 * M 1 0 := by
  apply (mat_mul_expl A.1 M).2.2.1

@[simp]
theorem SLnZ_M_d (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 1 1 = A.1 1 0 * M 0 1 + A.1 1 1 * M 1 1 := by
  apply (mat_mul_expl A.1 M).2.2.2

def matZToR (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![A 0 0, A 0 1], ![A 1 0, A 1 1]]

theorem nonzero_inv (a : ℝ) (h : 0 < a) : IsUnit a :=
  by
  have h2 : a ≠ 0 := by
    simp only [Ne.def]; by_contra h1; rw [h1] at h ;
    simp only [lt_self_iff_false] at h ;
  rw [isUnit_iff_exists_inv]; use a⁻¹; apply mul_inv_cancel h2

@[simp]
theorem mat_val (A : SL2Z) (i j : Fin 2) : (matZToR A.1) i j = (A.1 i j : ℝ) :=
  by
  rw [matZToR]; fin_cases i <;> fin_cases j; simp  [Matrix.cons_val_zero]
  simp  [Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp [Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp  [Matrix.head_cons, Matrix.cons_val_one]

@[simp]
theorem mat_vals (A : SL2Z) (i j : Fin 2) : (A : GL (Fin 2) ℝ) i j = (A.1 i j : ℝ) := by
  simp [mat_val, matZToR]; fin_cases i <;> fin_cases j; rfl; rfl; rfl; rfl

/-
@[simp]
theorem det_coe_sl (A : SpecialLinearGroup (Fin 2) ℤ) :
  (A : GeneralLinearGroup (Fin 2) ℝ).val.det = (A.val.det : ℝ) := by
  have := Matrix.SpecialLinearGroup.coeToGL_det A
  have := A.2
  rw [this]; simp;
 -/


end ModularGroup

end

