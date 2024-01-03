/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Modformsported.ForMathlib.EisensteinSeries.SL2lemmas


noncomputable section

open ModularForm UpperHalfPlane TopologicalSpace Set
 Metric Filter Function Complex  Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace EisensteinSeries

/--Subtype of functions valued in pars of coprime integers congruent to `a,b`.-/
def gammaSet (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ | (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧
  (f 0).gcd (f 1) = 1 }

@[simp]
lemma gammaSet_mem (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ gammaSet N a b ↔
  (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ (f 0).gcd (f 1) = 1 := by rfl

lemma gammaSet_mem_iff (N : ℕ) (a b c d : ℤ) (v : (gammaSet N a b)) : v.1 ∈ gammaSet N c d ↔
  (a : ZMod N) = c ∧ (b : ZMod N) = d := by
  have h2 := v.2
  simp only [gammaSet_mem] at *
  rw [h2.1, h2.2.1]
  simp only [h2.2.2, and_true]

lemma gammaSet_one_eq (a b c d : ℤ ) : gammaSet 1 a b = gammaSet 1 c d := by
  simp [gammaSet, eq_iff_true_of_subsingleton]

/--For level one the gamma sets are all equivalent, this is the equivalence-/
def gammaSet_one_equiv (a b c d : ℤ) : (gammaSet 1 a b) ≃ (gammaSet 1 c d) := by
  refine Equiv.Set.ofEq (gammaSet_one_eq a b c d)

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series.-/
def eise (k : ℤ) (z : ℍ) : (Fin 2 → ℤ) → ℂ := fun x => 1 / (x 0 * z.1 + x 1) ^ k

/--The Moebius transformation defined by a matrix in `SL(2,ℤ)` sending a function (or vector)
  `v` to `A v`-/
def moebiusEquiv (A : SL(2,ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
  (Matrix.SpecialLinearGroup.toLin' (SpecialLinearGroup.transpose A))

theorem moebius_aux_lem (k : ℤ) (a b c d i1 i2 : ℂ) (z : ℍ) (h : c * z + d ≠ 0) :
    ((i1 * ((a * z + b) / (c * z + d)) + i2) ^ k)⁻¹ =
      (c * z + d) ^ k * (((i1 * a + i2 * c ) * z + ( i1 * b + i2 * d)) ^ k)⁻¹ :=
  by
  have h1 : i1 * ((a * z + b) / (c * z + d)) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  have h2 : i1 * (a * z + b) / (c * z + d) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  have h3 := div_add' (i1 * (a * z + b)) i2 (c * z + d) h
  rw [h1,h2,h3, div_eq_inv_mul, mul_comm]
  ring_nf
  field_simp

-- How the Eise function changes under the Moebius action
theorem eise_Moebius (k : ℤ) (z : ℍ) (A : SL(2,ℤ)) (i : (Fin 2 → ℤ)) :
    eise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * eise k z (moebiusEquiv A i) :=
  by
  simp only [eise, specialLinearGroup_apply, algebraMap_int_eq, eq_intCast, ofReal_int_cast,
    one_div, moebiusEquiv, SpecialLinearGroup.transpose, EquivLike.coe_coe,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply', Matrix.mulVecLin_transpose,
    Matrix.vecMulLinear_apply, Matrix.vecMul, Matrix.vec2_dotProduct, Int.cast_add, Int.cast_mul]
  have hc := moebius_aux_lem k (A 0 0) (A 0 1) (A 1 0) (A 1 1) (i 0) (i 1) z ?_
  norm_cast at *
  apply UpperHalfPlane.denom_ne_zero A

/--The permutation of a gammaSet given by multiplying by an element `Γ(N)` -/
def gammaMoebiusFun (N : ℕ) (a b : ℤ) (γ : Gamma N) (f : gammaSet N a b) : (gammaSet N a b) := by
  use Matrix.vecMul f.1 γ.1.1
  simp only [gammaSet_mem, Matrix.vecMul, Matrix.vec2_dotProduct, Int.cast_add, Int.cast_mul]
  have hγ := (Gamma_mem N _).1 γ.2
  have hf := f.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, hf.1, hf.2.1]
  simp only [mul_one, mul_zero, add_zero, zero_add, true_and]
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 γ
  convert this
  repeat{
  simp_rw [Matrix.vecMul,Matrix.dotProduct,Matrix.vecCons]
  simp only [Fin.sum_univ_two, Fin.cons_zero, Fin.cons_one]}

lemma gammaMoebiusFun_eq_Moebequiv (N : ℕ) (a b : ℤ ) (γ : Gamma N) (f : gammaSet N a b) :
  (gammaMoebiusFun N a b γ f).1 = (moebiusEquiv γ.1 f.1) := by
  simp only [gammaMoebiusFun, moebiusEquiv, SpecialLinearGroup.transpose, EquivLike.coe_coe,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply', Matrix.mulVecLin_transpose,
    Matrix.vecMulLinear_apply]

lemma gamma_left_inv (N : ℕ) (a b : ℤ ) (γ : Gamma N) (v : gammaSet N a b) :
  gammaMoebiusFun N a b γ⁻¹ (gammaMoebiusFun N a b γ v) = v := by
  simp_rw [gammaMoebiusFun, SubgroupClass.coe_inv, Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.mul_adjugate, γ.1.2]
  simp

lemma gamma_right_inv (N : ℕ) (a b : ℤ ) (γ : Gamma N) (v : gammaSet N a b) :
  gammaMoebiusFun N a b γ (gammaMoebiusFun N a b γ⁻¹ v) = v := by
  simp_rw [gammaMoebiusFun]
  simp only [SubgroupClass.coe_inv, Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.adjugate_mul, γ.1.2]
  simp

/--The equivalence of gammaSets given by an element of `Γ(N)`-/
def gammaMoebiusEquiv (N : ℕ) (a b : ℤ ) (γ : Gamma N) : (gammaSet N a b) ≃ (gammaSet N a b)
    where
  toFun := gammaMoebiusFun N a b γ
  invFun := gammaMoebiusFun N a b γ⁻¹
  left_inv v:= by
    apply gamma_left_inv
  right_inv v:= by
    apply gamma_right_inv

/-- The Eisenstein series of weight `k : ℤ` and level `Γ(N)`, for `N : ℕ`. -/
def EisensteinLevelNtsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (gammaSet N a b),
  (eise k z x)

/-- The SlashInvariantForm defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
  and congruence condition given by `a b : ℤ`. -/
def eisensteinLevelNSIF (N : ℕ) (k a b : ℤ) : SlashInvariantForm (Gamma N) k
    where
  toFun := EisensteinLevelNtsum k N a b
  slash_action_eq' := by
    intro A
    ext1 x
    simp_rw [slash_action_eq'_iff, EisensteinLevelNtsum, UpperHalfPlane.subgroup_to_sl_moeb,
      UpperHalfPlane.sl_moeb, ←(Equiv.tsum_eq (gammaMoebiusEquiv N a b A) (fun v => eise k x v)),
      ←tsum_mul_left]
    apply tsum_congr
    intro v
    have := eise_Moebius k x A v
    simp at this
    rw [this]
    congr
    symm
    apply gammaMoebiusFun_eq_Moebequiv

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
