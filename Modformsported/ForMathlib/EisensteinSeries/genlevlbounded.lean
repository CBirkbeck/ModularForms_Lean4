/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.SL2lemmas
import Modformsported.ForMathlib.EisensteinSeries.Basic2


noncomputable section

open ModularForm UpperHalfPlane TopologicalSpace Set
 Metric Filter Function Complex  Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace EisensteinSeries

section SL_slash_actions

def gammaSLFun (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ)) (f : gammaSet N a b) :
  (gammaSet N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) := by
  use Matrix.vecMul f.1 A.1
  simp
  have hf := f.2
  rw [gammaSet_mem] at hf
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A
  simp_rw [Matrix.vecMul, Matrix.dotProduct] at *
  simp at *
  simp_rw [hf.1, hf.2.1]
  simp
  convert this

@[simp]
lemma gammaSLFun_apply (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ)) (f : gammaSet N a b) :
  (gammaSLFun N a b A f).1 = Matrix.vecMul f.1 A.1 := by rfl

lemma gammaSetSLmul (N : ℕ) (a b : ℤ) (A : SL(2,ℤ)) (v : (gammaSet N a b)) :
  (Matrix.vecMul v.1 A.1) ∈
    gammaSet N (Matrix.vecMul v.1 A.1 0) (Matrix.vecMul v.1 A.1 1) := by
    have h2 := v.2
    simp only [gammaSet_mem, true_and] at *
    have := SL2_gcd (v.1 0) (v.1 1) h2.2.2 A
    apply this

lemma SL_diag_prod_eq (A : SL(2,ℤ)) : (A.1 0 0) * (A.1 1 1) = 1 + (A.1 0 1) * (A.1 1 0) := by
  have hA:= A.2
  rw [Matrix.det_fin_two] at hA
  linarith

def gammaSLFunInv (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ))
  (f : gammaSet N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) :
  (gammaSet N a b) := by
  use Matrix.vecMul f.1 A⁻¹.1
  have h1 := gammaSet_mem_iff N (Matrix.vecMul f A⁻¹.1 0) (Matrix.vecMul f A⁻¹.1 1) a b
    ⟨Matrix.vecMul f.1 A⁻¹.1, gammaSetSLmul N (Matrix.vecMul (![a,b]) A.1 0)
      (Matrix.vecMul (![a,b]) A.1 1) A⁻¹ f⟩
  rw [h1, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [Matrix.vecMul, Matrix.vec2_dotProduct, Matrix.dotProduct, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Matrix.head_fin_const, mul_neg, Int.cast_add, Int.cast_mul, Int.cast_neg, Matrix.head_cons]
  rw [f.2.1, f.2.2.1]
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Int.cast_add, Int.cast_mul]
  ring_nf
  norm_cast
  conv =>
    enter [1,1,1]
    rw [mul_assoc]
    rw [SL_diag_prod_eq A]
  conv =>
    enter [2,1,1,1,1]
    rw [mul_comm]
  conv =>
    enter [2,1,1,1]
    rw [mul_assoc]
    rw [SL_diag_prod_eq A]
  ring_nf
  exact (true_and_iff True).mpr trivial

lemma GammaSLleftinv (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ)) (v :gammaSet N a b) :
    gammaSLFunInv N a b A (gammaSLFun N a b A v) = v := by
  rw [gammaSLFunInv, gammaSLFun]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.vecMul_vecMul, Matrix.mul_adjugate,
    Matrix.SpecialLinearGroup.det_coe, one_smul, Matrix.vecMul_one]

lemma GammaSLrightinv (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ))
  (v :gammaSet N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) :
    gammaSLFun N a b A (gammaSLFunInv N a b A v) = v := by
  rw [gammaSLFunInv, gammaSLFun]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.vecMul_vecMul, Matrix.adjugate_mul,
    Matrix.SpecialLinearGroup.det_coe, one_smul, Matrix.vecMul_one]

def gammaSLFun_equiv (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ)) : (gammaSet N a b) ≃
  (gammaSet N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) where
    toFun := gammaSLFun N a b A
    invFun := gammaSLFunInv N a b A
    left_inv v:= GammaSLleftinv N a b A v
    right_inv v:= GammaSLrightinv N a b A v

lemma gammaSLFun_equiv_apply (N : ℕ) (a b : ℤ ) (A : SL(2,ℤ)) (f : gammaSet N a b) :
  (gammaSLFun_equiv N a b A f).1 = (moebiusEquiv A f.1) := by
  simp only [gammaSLFun_equiv, Equiv.coe_fn_mk, gammaSLFun_apply, moebiusEquiv,
    SpecialLinearGroup.transpose, EquivLike.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply', Matrix.mulVecLin_transpose, Matrix.vecMulLinear_apply]
