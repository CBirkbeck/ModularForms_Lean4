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

open scoped Matrix

section

universe u

variable (n : Type _) [DecidableEq n] [Fintype n] (m : ℤ)

namespace ModularGroup

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

local notation "SL2Z" => SpecialLinearGroup (Fin 2) ℤ

variable {R : Type _} [CommRing R]

theorem det_m (M : IntegralMatricesWithDeterminant (Fin 2) m) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = m :=
  by
  have H := Matrix.det_fin_two M.1
  simp at *
  have m2 := M.2
  rw [← H]
  simp_rw [← m2]
  simp

theorem det_one (M : SL2Z) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by apply det_m

theorem det_onne (M : SL2Z) : M 0 0 * M 1 1 - M 1 0 * M 0 1 = 1 :=
  by
  have := det_one M
  have h1 : M 1 0 * M 0 1 = M 0 1 * M 1 0 := by apply mul_comm
  rw [h1]
  apply this

@[simp]
theorem mat_mul_expl (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
      (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
        (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
  by
  constructor; on_goal 2 => constructor; on_goal 3 => constructor
  all_goals
    simp only [mul_eq_mul]
    rw [Matrix.mul_apply]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    simp [Nat.succ_pos', lt_self_iff_false, dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty,
      not_le, Finset.range_zero, Nat.one_lt_bit0_iff, zero_add, add_right_inj, Fin.mk_one,
      Subtype.val_eq_coe, ite_eq_left_iff]

theorem SL2_inv_det_expl (A : SL2Z) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 :=
  by
  rw [Matrix.det_fin_two, mul_comm]
  simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, mul_neg, neg_mul, neg_neg]
  have := A.2
  rw [Matrix.det_fin_two] at this 
  convert this

theorem SL2_inv_expl (A : SL2Z) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_det_expl A⟩ :=
  by
  ext
  have := Matrix.adjugate_fin_two A.1
  simp only [Subtype.val_eq_coe] at this 
  simp at *
  simp_rw [this]
  simp

@[simp]
theorem SL2Z_inv_a (A : SL2Z) : A⁻¹.1 0 0 = A.1 1 1 := by rw [SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_b (A : SL2Z) : A⁻¹.1 0 1 = -A.1 0 1 := by rw [SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_c (A : SL2Z) : A⁻¹.1 1 0 = -A.1 1 0 := by rw [SL2_inv_expl]; simp

@[simp]
theorem SL2Z_inv_d (A : SL2Z) : A⁻¹.1 1 1 = A.1 0 0 := by rw [SL2_inv_expl]; simp

theorem m_a_b (m : ℤ) (hm : m ≠ 0) (A : SL2Z) (M N : IntegralMatricesWithDeterminant (Fin 2) m) :
    A • M = N ↔
      N 0 0 = A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧
        N 0 1 = A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧
          N 1 0 = A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧ N 1 1 = A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
  by
  constructor
  intro h
  have := mat_mul_expl A M; rw [← h]; simp; intro h; ext i j; fin_cases i <;> fin_cases j;
  simp at *; rw [h.1]
  simp at *; rw [h.2.1]; simp at *; rw [h.2.2.1]; simp at *; rw [h.2.2.2]

@[simp]
theorem SLnZ_M_a (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 0 0 = A 0 0 * M 0 0 + A 0 1 * M 1 0 := by
  simp [IntegralMatricesWithDeterminante.sLnZM, add_mul, mul_add, mul_assoc]

@[simp]
theorem SLnZ_M_b (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 0 1 = A 0 0 * M 0 1 + A 0 1 * M 1 1 := by
  simp [IntegralMatricesWithDeterminante.sLnZM, add_mul, mul_add, mul_assoc]

@[simp]
theorem SLnZ_M_c (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 1 0 = A 1 0 * M 0 0 + A 1 1 * M 1 0 := by
  simp [IntegralMatricesWithDeterminante.sLnZM, add_mul, mul_add, mul_assoc]

@[simp]
theorem SLnZ_M_d (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M) 1 1 = A 1 0 * M 0 1 + A 1 1 * M 1 1 := by
  simp [IntegralMatricesWithDeterminante.sLnZM, add_mul, mul_add, mul_assoc]

def matZToR (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![A 0 0, A 0 1], ![A 1 0, A 1 1]]

instance zToR : Coe (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨fun A => matZToR A⟩

theorem nonzero_inv (a : ℝ) (h : 0 < a) : IsUnit a :=
  by
  have h2 : a ≠ 0 := by simp only [Ne.def]; by_contra h1; rw [h1] at h ;
    simp only [lt_self_iff_false] at h ; exact h
  rw [isUnit_iff_exists_inv]; use a⁻¹; apply mul_inv_cancel h2

@[simp]
theorem mat_val (A : SL2Z) (i j : Fin 2) : (matZToR A.1) i j = (A.1 i j : ℝ) :=
  by
  rw [mat_Z_to_R]; fin_cases i <;> fin_cases j; simp only [Matrix.cons_val_zero]
  simp only [Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp only [Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
  simp only [Matrix.head_cons, Matrix.cons_val_one]

instance sLZToGLZ : Coe SL2Z (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  ⟨fun A =>
    ⟨matZToR A.1, by
      rw [mat_Z_to_R]; rw [Matrix.det_fin_two]; have := Matrix.det_fin_two A
      simp at *
      norm_cast; exact this.symm⟩⟩

variable (C : GLPos (Fin 2) ℤ)

@[simp]
theorem mat_vals (A : SL2Z) (i j : Fin 2) : (A : GL (Fin 2) ℝ) i j = (A.1 i j : ℝ) := by
  simp [mat_val, mat_Z_to_R]; fin_cases i <;> fin_cases j; rfl; rfl; rfl; rfl

@[simp]
theorem det_coe_sl (A : SL2Z) : (A : GL (Fin 2) ℝ).val.det = (A.val.det : ℝ) := by have := A.2;
  rw [this]; simp; rw [← coe_coe]; rw [← coe_coe]; simp

end ModularGroup

end

