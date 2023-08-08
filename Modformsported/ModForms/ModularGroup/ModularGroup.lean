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


open Finset

open Matrix

open scoped Matrix

section

universe u

@[reducible]
def SL2Z :=
  SpecialLinearGroup (Fin 2) ℤ

variable (m : ℤ)

def n' : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![-1, 0], ![0, -1]]

theorem ND : n'.det = 1 := by
  rw [n']
  rfl

def n : SL2Z :=
  ⟨n', ND⟩

def sr : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![1, 0], ![0, 1]]

theorem SD2 : sr.det = 1 := by
  rw [sr]
  rfl

def ni : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨sr, SD2⟩

def s2 : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![-2, 0], ![0, -1]]

variable {R : Type _} [CommRing R]

theorem det_of_22 (M : Matrix (Fin 2) (Fin 2) R) : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_succ]; ring

@[simp]
theorem mat_mul_expl (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
      (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
        (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
  by
  constructor; simp
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_pos', dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty, Finset.range_zero,
    zero_add, Fin.mk_one, le_refl]
  constructor; simp
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_pos', dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty, Finset.range_zero,
    zero_add, Fin.mk_one, le_refl]
  constructor; simp
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_pos', dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty, Finset.range_zero,
    zero_add, Fin.mk_one, le_refl]
  simp
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_pos', dite_eq_ite, Fin.mk_zero, if_true, Finset.sum_empty, Finset.range_zero,
     zero_add, Fin.mk_one, le_refl]

theorem valorsl (A : SL2Z) :
    A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1 := by 
  constructor; rfl;
  constructor; 
  rfl; 
  constructor; rfl; rfl

theorem valor_mat_m (A : IntegralMatricesWithDeterminant (Fin 2) m) :
    A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1 := by 
    constructor; rfl;
    constructor; rfl; 
    constructor; rfl; rfl

theorem det_onee (A : SL2Z) : det A.1 = A 0 0 * A 1 1 - A 1 0 * A 0 1 :=
  by
  have := det_of_22 A.1
  have ad := A.2; simp [valorsl]
  rw [ad] at this 
  have cg : A.1 1 0 * A.1 0 1 = A.1 0 1 * A.1 1 0 := by ring
  simp at cg ; rw [cg]; exact this

theorem str (A : SL2Z) : det A.1 = 1 :=
  A.2

theorem det_onne (A : SL2Z) : A 0 0 * A 1 1 - A 1 0 * A 0 1 = 1 :=
  by
  have := A.2
  rw [det_onee] at this
  exact this

theorem det_onne' (A : SL2Z) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
  by
  have cg : A.1 1 0 * A.1 0 1 = A.1 0 1 * A.1 1 0 := by ring
  simp_rw [←cg]
  apply det_onne
  

theorem det_m (M : IntegralMatricesWithDeterminant (Fin 2) m) : M 0 0 * M 1 1 - M 1 0 * M 0 1 = m :=
  by
  have H := det_of_22 M.1
  simp [valor_mat_m] at *
  have m2 := M.2; 
  simp at m2 
  rw [m2] at H 
  have cg : M.1 1 0 * M.1 0 1 = M.1 0 1 * M.1 1 0 := by ring
  rw [cg]
  exact H.symm

theorem det_m''' (M : IntegralMatricesWithDeterminant (Fin 2) m) (h : M 1 0 = 0) :
    M 0 0 * M 1 1 = m := by have := det_m _ M; rw [h] at this ; simp at this ; exact this

theorem det_m' (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    M 0 0 * M 1 1 - M 1 0 * M 0 1 = M.val.det :=
  by
  have := det_of_22 M.1; simp [valor_mat_m]; simp at this 
  have cg : M.1 1 0 * M.1 0 1 = M.1 0 1 * M.1 1 0 := by ring; 
  simp at cg ; 
  rw [cg]; 
  exact this.symm

theorem det_m2 (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    M.1 0 0 * M.1 1 1 - M.1 1 0 * M.1 0 1 = M.val.det := by 
    have := det_m' _ M;
    exact this

@[simp]
theorem sL2Z_mul_a (A B : SL2Z) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 :=
  by
  have : (A * B).1 = A.1 * B.1 := by exact rfl
  rw [this]
  rw [mul_eq_mul]
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  simp only [Nat.succ_pos', Fin.mk_zero, dif_pos, sum_singleton, Fin.mk_one,
    range_one]

@[simp]
theorem sL2Z_mul_b (A B : SL2Z) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 :=
  by
  have : (A * B).1 = A.1 * B.1 := by exact rfl
  rw [this]
  rw [mul_eq_mul]
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  simp only [Nat.succ_pos', Fin.mk_zero, dif_pos, sum_singleton, Fin.mk_one,
    range_one]

@[simp]
theorem sL2Z_mul_c (A B : SL2Z) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 :=
  by
  have : (A * B).1 = A.1 * B.1 := by exact rfl
  rw [this]
  rw [mul_eq_mul]
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  simp only [Nat.succ_pos', Fin.mk_zero, dif_pos, sum_singleton, Fin.mk_one,
    range_one]

@[simp]
theorem sL2Z_mul_d (A B : SL2Z) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
  by
  have : (A * B).1 = A.1 * B.1 := by exact rfl
  rw [this]
  rw [mul_eq_mul]
  rw [Matrix.mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  simp only [Nat.succ_pos', Fin.mk_zero, dif_pos, sum_singleton, Fin.mk_one,
    range_one]

theorem mre : n * n = (1 : SL2Z) := by
  ext i j
  fin_cases i <;> fin_cases j
  simp; 
  simp
  simp
  simp

theorem ng : ni = (1 : SpecialLinearGroup (Fin 2) ℤ) := by 
  rw [ni]; 
  simp_rw [sr]; 
  ext i j;
  fin_cases i <;> fin_cases j; 
  simp [valorsl]; simp [valorsl]; simp [valorsl]; simp [valorsl]

theorem vale (A : IntegralMatricesWithDeterminant (Fin 2) m) :
    A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1 := by 
    constructor; rfl;
    constructor; rfl; 
    constructor; rfl; rfl

@[simp]
theorem sL2Z_one_a : (1 : SL2Z) 0 0 = 1 :=
  rfl

@[simp]
theorem sL2Z_one_b : (1 : SL2Z) 0 1 = 0 :=
  rfl

@[simp]
theorem sL2Z_one_c : (1 : SL2Z) 1 0 = 0 :=
  rfl

@[simp]
theorem sL2Z_one_d : (1 : SL2Z) 1 1 = 1 :=
  rfl

theorem sl2_inv (A : SL2Z) (B : SL2Z) (h1 : B.1 0 0 = A.1 1 1) (h2 : B.1 0 1 = -A.1 0 1)
    (h3 : B.1 1 0 = -A.1 1 0) (h4 : B.1 1 1 = A.1 0 0) : A.1 * B.1 = (1 : SL2Z).1 :=
  by
  have := mat_mul_expl A.1 B.1
  ext i j
  fin_cases i <;> fin_cases j
  have e1 := this.1; 
  simp only [Fin.mk_zero, mat_mul_expl, IntegralMatricesWithDeterminante.mat_m_vals]
  simp_rw [e1]; 
  rw [h1]; rw [h3]; simp
  have Adet := Matrix.det_fin_two A.1; 
  simp only [SpecialLinearGroup.det_coe, IntegralMatricesWithDeterminante.mat_m_vals] at Adet  
  apply Adet.symm; have e2 := this.2.1; 
  simp only [Fin.mk_zero, Fin.mk_one, mat_mul_expl, IntegralMatricesWithDeterminante.mat_m_vals]
  simp_rw [h2, h4]; 
  ring_nf
  simp
  have e3 := this.2.2.1; 
  rw [h1, h3]; 
  ring_nf 
  simp only [Fin.mk_one, mat_mul_expl, IntegralMatricesWithDeterminante.mat_m_vals]
  rw [h2, h4]; 
  simp only [IntegralMatricesWithDeterminante.mat_m_vals, mul_neg]
  have Adet := Matrix.det_fin_two A.1; 
  simp only [SpecialLinearGroup.det_coe, IntegralMatricesWithDeterminante.mat_m_vals] at Adet  
  rw [add_comm]
  rw [mul_comm]
  have cg : A.1 1 0 * A.1 0 1 = A.1 0 1 * A.1 1 0 := by ring; 
  rw [cg]
  ring_nf
  rw [Adet.symm] 
  simp


/-
theorem sl2_inv' (A : SL2Z) (B : SL2Z) (h1 : B 0 0 = A 1 1) (h2 : B 0 1 = -A 0 1)
    (h3 : B 1 0 = -A 1 0) (h4 : B 1 1 = A 0 0) : A * B = 1 :=
  by
  have H := sl2_inv A B h1 h2 h3 h4; 
  simp at H ; rw [← Matrix.mul_eq_mul] at H 
  simp only [valorsl] at *; cases B; cases A; dsimp at *; ext1; cases j
  cases i; dsimp at *; simp at *; solve_by_elim

theorem sl2_inv'' (A : SL2Z) (B : SL2Z) (h1 : B 0 0 = A 1 1) (h2 : B 0 1 = -A 0 1)
    (h3 : B 1 0 = -A 1 0) (h4 : B 1 1 = A 0 0) : A⁻¹ = B := by have H := sl2_inv' A B h1 h2 h3 h4;
  have := eq_inv_iff_mul_eq_one.2 H; simp_rw [this]; simp

def ainv' (A : SL2Z) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![A 1 1, -A 0 1], ![-A 1 0, A 0 0]]

theorem ainvdet (A : SL2Z) : (ainv' A).det = 1 :=
  by
  rw [ainv']; rw [det_of_22]; simp; have := det_onne A; simp only [valorsl] at *;
  rw [mul_comm] at this 
  have cg : A.val 0 1 * A.val 1 0 = A.val 1 0 * A.val 0 1 := by ring; simp at cg 
  rw [cg]; exact this

def ainv (A : SL2Z) : SL2Z :=
  ⟨ainv' A, ainvdet A⟩

theorem ainv_is_inv (A : SL2Z) : A⁻¹ = ainv A :=
  by
  rw [sl2_inv'' A (ainv A)]; simp [valorsl] at *; rw [ainv]; simp_rw [ainv']; ring
  simp [valorsl] at *; rw [ainv]; simp_rw [ainv'];
  simp only [cons_val_one, neg_inj, cons_val_zero, Subtype.coe_mk, head_cons]
  simp only [valorsl]; simp
  simp [valorsl] at *; rw [ainv]; simp_rw [ainv']; simp; simp only [valorsl]; simp; rw [ainv];
  simp_rw [ainv']; simp [valorsl]

@[simp]
theorem sL2Z_inv_a (A : SL2Z) : A⁻¹ 0 0 = A 1 1 := by simp only [valorsl]; rw [ainv_is_inv];
  rw [ainv]; simp_rw [ainv']; simp only [valorsl, cons_val_zero]

@[simp]
theorem sL2Z_inv_b (A : SL2Z) : A⁻¹ 0 1 = -A 0 1 := by simp only [valorsl]; rw [ainv_is_inv];
  rw [ainv]; simp_rw [ainv']; simp only [valorsl, cons_val_one, cons_val_zero, head_cons]

@[simp]
theorem sL2Z_inv_c (A : SL2Z) : A⁻¹ 1 0 = -A 1 0 := by simp only [valorsl]; rw [ainv_is_inv];
  rw [ainv]; simp_rw [ainv']; simp only [valorsl, cons_val_one, cons_val_zero, head_cons]

@[simp]
theorem sL2Z_inv_d (A : SL2Z) : A⁻¹ 1 1 = A 0 0 := by simp only [valorsl]; rw [ainv_is_inv];
  rw [ainv]; simp_rw [ainv']; simp only [valorsl, cons_val_one, head_cons]

def sL2ZM (m : ℤ) :
    SL2Z → IntegralMatricesWithDeterminant (Fin 2) m → IntegralMatricesWithDeterminant (Fin 2) m :=
  fun A B => ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩

theorem one_smull : ∀ M : IntegralMatricesWithDeterminant (Fin 2) m, sL2ZM m (1 : SL2Z) M = M :=
  by
  rw [sL2ZM]
  simp

theorem mul_smull :
    ∀ A B : SL2Z,
      ∀ M : IntegralMatricesWithDeterminant (Fin 2) m,
        sL2ZM m (A * B) M = sL2ZM m A (sL2ZM m B M) :=
  by
  simp [sL2ZM]
  intro A B M
  simp [Matrix.mul_assoc]

variable (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m)

@[simp]
theorem smul_is_mul (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M).1 = A * M := by simp [sL2ZM]

theorem SLEQ : SL2Z = IntegralMatricesWithDeterminant (Fin 2) 1 := by rfl

instance : Coe (IntegralMatricesWithDeterminant (Fin 2) 1) SL2Z :=
  ⟨fun a => ⟨a.1, a.2⟩⟩

theorem smul_is_mul_1 (A : SL2Z) (M : IntegralMatricesWithDeterminant (Fin 2) 1) :
    (A • M : SL2Z) = A * (M : SL2Z) := by simp [sL2ZM]

theorem m_a_b (m : ℤ) (hm : m ≠ 0) (A : SL2Z) (M N : IntegralMatricesWithDeterminant (Fin 2) m) :
    (A • M : IntegralMatricesWithDeterminant (Fin 2) m) = n ↔
      n 0 0 = A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧
        n 0 1 = A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧
          n 1 0 = A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧ n 1 1 = A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
  by
  constructor
  intro h
  have := mat_mul_expl A M; rw [← h]; simp [valor_mat_m]; intro h; ext i j;
  fin_cases i <;> fin_cases j
  simp [valor_mat_m] at *; rw [h.1]
  simp [valor_mat_m] at *; rw [h.2.1]; simp [valor_mat_m] at *; rw [h.2.2.1];
  simp [valor_mat_m] at *
  rw [h.2.2.2]

@[simp]
theorem sL2ZM_a : (sL2ZM m A M).1 0 0 = A.1 0 0 * M.1 0 0 + A.1 0 1 * M.1 1 0 :=
  by
  simp [sL2ZM, add_mul, mul_add, mul_assoc]
  rw [mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

@[simp]
theorem sL2Z_M_aa : (A • M) 0 0 = A 0 0 * M 0 0 + A 0 1 * M 1 0 := by apply sL2ZM_a

@[simp]
theorem sL2ZM_b : (sL2ZM m A M).1 0 1 = A.1 0 0 * M.1 0 1 + A.1 0 1 * M.1 1 1 :=
  by
  simp [sL2ZM, add_mul, mul_add, mul_assoc]
  rw [mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

@[simp]
theorem sL2Z_M_ba : (A • M) 0 1 = A 0 0 * M 0 1 + A 0 1 * M 1 1 := by apply sL2ZM_b

@[simp]
theorem sL2ZM_c : (sL2ZM m A M).1 1 0 = A.1 1 0 * M.1 0 0 + A.1 1 1 * M.1 1 0 :=
  by
  simp [sL2ZM, add_mul, mul_add, mul_assoc]
  rw [mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

@[simp]
theorem sL2Z_M_ca : (A • M) 1 0 = A 1 0 * M 0 0 + A 1 1 * M 1 0 := by apply sL2ZM_c

@[simp]
theorem sL2ZM_d : (sL2ZM m A M).1 1 1 = A.1 1 0 * M.1 0 1 + A.1 1 1 * M.1 1 1 :=
  by
  simp [sL2ZM, add_mul, mul_add, mul_assoc]
  rw [mul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

@[simp]
theorem sL2Z_M_da : (A • M) 1 1 = A 1 0 * M 0 1 + A 1 1 * M 1 1 := by apply sL2ZM_d

namespace IntegralMatricesWithDeterminante

variable (B : IntegralMatricesWithDeterminant (Fin 2) m)

def mi (m : ℤ) (M : IntegralMatricesWithDeterminant (Fin 2) m) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![-M 0 0, -M 0 1], ![-M 1 0, -M 1 1]]

theorem fff (m : ℤ) (M : IntegralMatricesWithDeterminant (Fin 2) m) : (mi m M).det = m :=
  by
  rw [mi]; rw [det_of_22]; simp; have := det_m m M; simp [valor_mat_m] at *
  have cg : M.1 1 0 * M.1 0 1 = M.1 0 1 * M.1 1 0 := by ring; simp at cg ; rw [← cg]; exact this

def mATINV (m : ℤ) :
    IntegralMatricesWithDeterminant (Fin 2) m → IntegralMatricesWithDeterminant (Fin 2) m :=
  fun A => ⟨mi m A, by apply fff⟩

/-
instance (m : ℤ) : has_neg (integral_matrices_with_determinant (fin 2) m) :=
⟨λ A, MATINV m A ⟩


@[simp] lemma neg_a : (-B) 0 0 = -B 0 0 := rfl
@[simp] lemma neg_b : (-B) 0 1 = -B 0 1 := rfl
@[simp] lemma neg_c : (-B) 1 0 = -B 1 0  := rfl
@[simp] lemma neg_d : (-B) 1 1 = -B 1 1 := rfl
@[simp]  lemma neg_neg : -(-B) = B :=
begin
ext i j, fin_cases i; fin_cases j,simp,simp, simp,simp,
end
-/
end IntegralMatricesWithDeterminante

namespace SL2Z

variable (C D B : SL2Z)

instance : Neg SL2Z := by simp_rw [SL2Z]; have := special_linear_group.has_neg; apply this; simp;
  fconstructor; tauto

--
@[simp]
theorem neg_a : (-B) 0 0 = -B 0 0 :=
  rfl

@[simp]
theorem neg_b : (-B) 0 1 = -B 0 1 :=
  rfl

@[simp]
theorem neg_c : (-B) 1 0 = -B 1 0 :=
  rfl

@[simp]
theorem neg_d : (-B) 1 1 = -B 1 1 :=
  rfl

@[simp]
theorem neg_neg : - -B = B := by ext i j; fin_cases i <;> fin_cases j; simp; simp; simp; simp

@[simp]
protected theorem neg_one_mul : -1 * C = -C := by ext i j; fin_cases i <;> fin_cases j; simp; simp;
  simp; simp

@[simp]
protected theorem neg_mul_neg : -C * -D = C * D := by ext i j; fin_cases i <;> fin_cases j <;> simp

@[simp]
protected theorem neg_mul : -(C * D) = -C * D := by ext i j; fin_cases i <;> fin_cases j; simp;
  ring; simp; ring; simp; ring; simp; ring

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
      rw [mat_Z_to_R]; rw [det_of_22]; have := det_onne' A; simp; simp at this 
      norm_cast; exact this⟩⟩

@[simp]
theorem mat_vals (A : SL2Z) (i j : Fin 2) : (A : GL (Fin 2) ℝ) i j = (A.1 i j : ℝ) := by
  simp [mat_val, mat_Z_to_R]; fin_cases i <;> fin_cases j; rfl; rfl; rfl; rfl

/-
@[simp]
theorem det_coe_sl (A : SL2Z) : (A : GL (Fin 2) ℝ).val.det = (A.val.det : ℝ) := by 
  have := A.2;
  rw [this]; simp; 
-/ 
-/
end SL2Z

end

