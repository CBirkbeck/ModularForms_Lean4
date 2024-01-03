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

open ModularForm  UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex   Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace EisensteinSeries

def gammaSet (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  | (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧
  (f 0).gcd (f 1) = 1 }

@[simp]
lemma gammaSet_mem (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ gammaSet N a b ↔
  (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ (f 0).gcd (f 1) = 1 := by rfl

lemma gammaSet_one_eq (a b c d : ℤ ) : gammaSet 1 a b = gammaSet 1 c d := by
  simp [gammaSet, eq_iff_true_of_subsingleton]

def gammaSet_one_equiv (a b c d : ℤ) : (gammaSet 1 a b) ≃ (gammaSet 1 c d) := by
  refine Equiv.Set.ofEq (gammaSet_one_eq a b c d)

/-- The function on `(Fin 2 → ℤ)` whose sum defines an Eisenstein series.-/
def eise (k : ℤ) (z : ℍ) : (Fin 2 → ℤ) → ℂ := fun x => 1 / (x 0 * z.1 + x 1) ^ k

def moebiusEquiv (A : SL(2,ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
  (Matrix.SpecialLinearGroup.toLin' (SpecialLinearGroup.transpose A))

theorem moebius_aux_lem (k : ℤ) (a b c d i1 i2 : ℂ) (z : ℍ) (h : c * z + d ≠ 0) :
    ((i1 * ((a * z + b) / (c * z + d)) + i2) ^ k)⁻¹ =
      (c * z + d) ^ k * (((i1 * a  +  i2 * c ) * z + ( i1 * b  +  i2 * d)) ^ k)⁻¹ :=
  by
  have h1 : i1 * ((a * z + b) / (c * z + d)) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h1]
  have h2 : i1 * (a * z + b) / (c * z + d) + i2 = i1 * (a * z + b) / (c * z + d) + i2 := by ring;
  rw [h2]
  have h3 := div_add' (i1 * (a * z + b)) i2 (c * z + d) h
  rw [h3]
  rw [div_eq_inv_mul, mul_comm]
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

def gammaMoebiusFun (N : ℕ)  (a b : ℤ) (γ  : Gamma N) (f : gammaSet N a b) : (gammaSet N a b) := by
  use Matrix.vecMul f.1 γ.1.1
  simp only [gammaSet_mem]
  simp only [Matrix.vecMul, Matrix.vec2_dotProduct, Int.cast_add, Int.cast_mul]
  have hγ := (Gamma_mem N _).1 γ.2
  have hf := f.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, hf.1, hf.2.1]
  simp only [mul_one, mul_zero, add_zero, zero_add, true_and]
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 γ
  convert this
  repeat{
  simp_rw [Matrix.vecMul,Matrix.dotProduct,Matrix.vecCons]
  simp}

lemma gammaMoebiusFun_eq_Moebequiv (N : ℕ)  (a b : ℤ ) (γ  : Gamma N) (f : gammaSet N a b) :
  (gammaMoebiusFun N a b γ f).1 = (moebiusEquiv γ.1 f.1) := by
  simp_rw [gammaMoebiusFun, moebiusEquiv]
  simp only [SpecialLinearGroup.transpose, EquivLike.coe_coe,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply', Matrix.mulVecLin_transpose,
    Matrix.vecMulLinear_apply]

lemma Gammaleftinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : gammaSet N a b) :
  gammaMoebiusFun N a b γ⁻¹ (gammaMoebiusFun N a b γ v) = v := by
  simp_rw [gammaMoebiusFun]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.mul_adjugate]
  rw [γ.1.2]
  simp

lemma Gammarightinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : gammaSet N a b) :
  gammaMoebiusFun N a b γ (gammaMoebiusFun N a b γ⁻¹ v) = v := by
  simp_rw [gammaMoebiusFun]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.adjugate_mul]
  rw [γ.1.2]
  simp

def gammaMoebiusEquiv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) : (gammaSet N a b) ≃ (gammaSet N a b)
    where
  toFun := gammaMoebiusFun N a b γ
  invFun := gammaMoebiusFun N a b γ⁻¹
  left_inv v:= by
    apply Gammaleftinv
  right_inv v:= by
    apply Gammarightinv

/-- The Eisenstein series of weight `k : ℤ` and level `Γ(N)`, for `N : ℕ`. -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (gammaSet N a b),
  (eise k z  x)

def Eisenstein_SIF_lvl_N (N : ℕ) (k a b : ℤ) : SlashInvariantForm (Gamma N) k
    where
  toFun := Eisenstein_N_tsum k N a b
  slash_action_eq' := by
    intro A
    ext1 x
    simp_rw [slash_action_eq'_iff, Eisenstein_N_tsum, UpperHalfPlane.subgroup_to_sl_moeb,
      UpperHalfPlane.sl_moeb,  ←(Equiv.tsum_eq (gammaMoebiusEquiv N a b A) (fun v => eise k x v)),
      ←tsum_mul_left]
    apply tsum_congr
    intro v
    have := eise_Moebius k x A v
    simp at this
    rw [this]
    congr
    symm
    apply gammaMoebiusFun_eq_Moebequiv
