/- 
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R  

def lvl_N_congr (N : ℕ) (a b : ℤ ) := {x : ℤ × ℤ  // (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 }

def lvl_N_congr' (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  // (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ 
  (f 0).gcd (f 1) = 1 }

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

def SpecialLinearGroup.transpose ( A:  Matrix.SpecialLinearGroup n R)  :  
  Matrix.SpecialLinearGroup n R  := by
  use A.1.transpose
  rw [Matrix.det_transpose]
  apply A.2

def gcd_one_to_SL (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![a, -Int.gcdB a b;  b, Int.gcdA a b]
  simp
  have := Int.gcd_eq_gcd_ab a b 
  rw [hab] at this
  simp at this
  rw [this]
  ring


def SL_to_gcd_one_fst_col (A: SL(2,ℤ)) : (A.1 0 0).gcd (A.1 0 1) = 1 := by
    rw [Int.gcd_eq_one_iff_coprime]
    rw [IsCoprime]
    use (A.1 1 1)
    use -(A.1 1 0)
    have T:= EisensteinSeries.det_SL_eq_one A
    norm_cast at *
    ring_nf
    rw [mul_comm] 
    norm_cast at *
    have : A.1 0 1 * A.1 1 0 = A.1 1 0 * A.1 0 1 := by ring
    rw [this] at T
    exact T

   
lemma SL2_gcd (a b : ℤ) (hab : a.gcd b = 1) (A : SL(2,ℤ)) : 
  (Matrix.vecMul (![a,b]) A.1 0).gcd (Matrix.vecMul (![a,b]) A.1 1) = 1  := by
    let C := SpecialLinearGroup.transpose ((gcd_one_to_SL a b hab)) *A
    have := SL_to_gcd_one_fst_col C
    simp at this
    rw [SpecialLinearGroup.transpose, gcd_one_to_SL] at this
    simp at this
    simp_rw [Matrix.vecMul] at *
    simp at *
    norm_cast at *
    simp_rw [Matrix.vecHead, Matrix.vecTail,  Matrix.mul, Matrix.dotProduct, Matrix.transpose] at *
    simp at *
    simp_rw [Matrix.vecHead] at this
    simp at this
    exact this

def Gammainv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (f : lvl_N_congr' N a b) : (lvl_N_congr' N a b) := by 
  use Matrix.vecMul f.1 γ.1.1 
  simp
  simp_rw [Matrix.vecMul]
  simp
  have hγ := (Gamma_mem N _).1 γ.2
  have hf := f.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, hf.1, hf.2.1]
  simp
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 γ
  simp_rw [Matrix.vecMul,  Matrix.dotProduct, Matrix.vecMul] at this
  convert this
  simp
  simp

lemma Gammaleftinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : lvl_N_congr' N a b) : 
  Gammainv N a b γ⁻¹ (Gammainv N a b γ v) = v := by
  simp_rw [Gammainv]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp 
  rw [Matrix.mul_adjugate]
  rw [γ.1.2]
  simp

lemma Gammarightinv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (v : lvl_N_congr' N a b) : 
  Gammainv N a b γ (Gammainv N a b γ⁻¹ v) = v := by
  simp_rw [Gammainv]
  simp only [SubgroupClass.coe_inv,  Matrix.vecMul_vecMul]
  apply Subtype.ext
  simp 
  rw [Matrix.adjugate_mul]
  rw [γ.1.2]
  simp
  

def Gammainv_Equiv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) : (lvl_N_congr' N a b) ≃ (lvl_N_congr' N a b) 
    where
  toFun := Gammainv N a b γ 
  invFun := Gammainv N a b γ⁻¹ 
  left_inv v:= by 
    apply Gammaleftinv
  right_inv v:= by
    apply Gammarightinv
    


def prod_fun_equiv : ℤ × ℤ ≃ (Fin 2 → ℤ) := by exact (piFinTwoEquiv fun _ => ℤ).symm

def index_equiv (N : ℕ)  (a b : ℤ ) : (lvl_N_congr' N a b) ≃ (lvl_N_congr N a b)  := by
  apply Equiv.subtypeEquiv (piFinTwoEquiv fun _ => ℤ)
  rw [piFinTwoEquiv ]
  simp

/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (lvl_N_congr  N a b), 
  (eise k z  x.1)

lemma summable_Eisenstein_N_tsum (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1) ) := by 
  apply (Eisenstein_tsum_summable k z hk).subtype

def feise (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b)) : ℂ := (eise k z ((piFinTwoEquiv fun _ => ℤ) v.1))

lemma summable_Eisenstein_N_tsum' (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr'  N a b)) => feise k z x)  := by 
  have : (fun (x : (lvl_N_congr'  N a b)) => feise k z x) = 
   (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1)) ∘ (index_equiv N a b) := by 
    ext1 v
    simp
    congr
  rw [this, Equiv.summable_iff] 
  apply summable_Eisenstein_N_tsum k hk




theorem feise_Moebius (k : ℤ) (z : ℍ) (N : ℕ) (A : Gamma N) (i : (lvl_N_congr'  N a b)) :
    feise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * feise k z ((Gammainv_Equiv N a b A)  i) := by
    simp_rw [feise,UpperHalfPlane.specialLinearGroup_apply]
    have := eise_Moebius k z A.1 ((piFinTwoEquiv fun _ => ℤ) i.1)
    stop






variable  (a : ℤ × ℤ)


def equivla (A : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ :=  
  (prod_fun_equiv.trans (Matrix.SpecialLinearGroup.toLin' A).toEquiv).trans  prod_fun_equiv.symm



lemma averaver (A: SL(2, ℤ)) : equivla  (SpecialLinearGroup.transpose A)  = MoebiusPerm A  := by
  rw [equivla, prod_fun_equiv]
  simp [MoebiusPerm]
  simp
  ext1 v
  simp
  constructor
  rw [Matrix.SpecialLinearGroup.toLin'_apply,SpecialLinearGroup.transpose ]
  simp
  rw [Matrix.mulVec, Matrix.dotProduct]
  simp
  ring_nf
  have  : v.snd * A.1 1 0 = A.1 1 0 * v.snd := by ring
  congr
  rw [Matrix.SpecialLinearGroup.toLin'_apply,SpecialLinearGroup.transpose ]
  simp
  rw [Matrix.mulVec, Matrix.dotProduct]
  simp 
  ring_nf
  congr

  

