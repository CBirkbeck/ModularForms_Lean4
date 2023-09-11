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

def lvl_N_congr (N : ℕ) (a b : ℤ ) := {x : ℤ × ℤ  // x.1 % N = a ∧ x.2 % N = b ∧ a.gcd b = 1 }

def lvl_N_congr' (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  // (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ 
  (f 0).gcd (f 1) = 1 }

def gcd_one_to_SL (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![a, -Int.gcdB a b; b, Int.gcdA a b]
  simp
  have := Int.gcd_eq_gcd_ab a b
  rw [hab] at this
  simp at this
  rw [this]
  ring


def SL_to_gcd_one_fst_col (A: SL(2,ℤ)) : (A.1 0 0).gcd (A.1 1 0) = 1 := by
    rw [Int.gcd_eq_one_iff_coprime]
    rw [IsCoprime]
    use (A.1 1 1)
    use -(A.1 0 1)
    have := EisensteinSeries.det_SL_eq_one A
    norm_cast at *
    ring_nf
    rw [mul_comm] 
    exact this

   
lemma SL2_gcd (a b : ℤ) (hab : a.gcd b = 1) (A : SL(2,ℤ)) : 
  (Matrix.vecMul (![a,b]) A.1 0).gcd (Matrix.vecMul (![a,b]) A.1 0) = 1  := by
    simp
    simp_rw [Matrix.vecMul]
    


def Gammainv (N : ℕ)  (a b : ℤ )  (γ  : Gamma N) (f : lvl_N_congr' N a b) : (lvl_N_congr' N a b) := by 
  use Matrix.vecMul f.1 γ.1.1 
  simp
  simp_rw [Matrix.vecMul]
  simp
  have hγ := (Gamma_mem N _).1 γ.2
  have hf := f.2
  rw [hγ.1, hγ.2.2.1, hγ.2.2.2, hγ.2.1, hf.1, hf.2.1]
  simp
  
  

/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (lvl_N_congr  N a b), 
  eise k z x.1

lemma summable_Eisenstein_N_tsum (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr  N a b)) => eise k z x.1) := by 
  apply (Eisenstein_tsum_summable k z hk).subtype

variable  (a : ℤ × ℤ)


def equiv1 : ℤ × ℤ ≃ (Fin 2 → ℤ) := by exact (piFinTwoEquiv fun i => ℤ).symm

def equivla (A : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ :=  
  (equiv1.trans (Matrix.SpecialLinearGroup.toLin' A).toEquiv).trans  equiv1.symm

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

def SpecialLinearGroup.transpose ( A:  Matrix.SpecialLinearGroup n R)  :  
  Matrix.SpecialLinearGroup n R  := by
  use A.1.transpose
  rw [Matrix.det_transpose]
  apply A.2

lemma averaver (A: SL(2, ℤ)) : equivla  (SpecialLinearGroup.transpose A)  = MoebiusPerm A  := by
  rw [equivla, equiv1]
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

  

