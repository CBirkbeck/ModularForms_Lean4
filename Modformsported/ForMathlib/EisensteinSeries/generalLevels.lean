/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Modformsported.ForMathlib.AuxpLemmas
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Modformsported.ForMathlib.EisensteinSeries.partial_sum_tendsto_uniformly
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Analysis.Normed.Field.InfiniteSum

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex   Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

def lvl_N_congr (N : ℕ) (a b : ℤ ) := {x : ℤ × ℤ  | (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 }

def lvl_N_congr' (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  | (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧
  (f 0).gcd (f 1) = 1 }

def int_vec_gcd_n (n : ℕ) := {f : (Fin 2) → ℤ  | (f 0).gcd (f 1) = n }

@[simp]
lemma inv_vec_gcd_n_mem (n : ℕ) (f : (Fin 2) → ℤ ) : f ∈ int_vec_gcd_n n ↔ (f 0).gcd (f 1) = n := by
  rfl


def vec_gcd_vec_equiv : ((Fin 2) → ℤ) ≃ (⋃ n : ℕ, int_vec_gcd_n n) where
  toFun  := by
    intro v
    refine ⟨v,?_⟩
    simp
  invFun := fun v => v.1
  left_inv := by
    intro v
    simp
  right_inv := by
    intro v
    simp

@[simp]
lemma lvl_N_congr_mem (N : ℕ) (a b : ℤ ) (x : ℤ × ℤ) : x ∈ lvl_N_congr N a b ↔
  (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 := by rfl

@[simp]
lemma lvl_N_congr'_mem (N : ℕ) (a b : ℤ ) (f : (Fin 2) → ℤ ) : f ∈ lvl_N_congr' N a b ↔
  (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ (f 0).gcd (f 1) = 1 := by rfl

lemma lvl_1_congr (a b c d : ℤ ) : lvl_N_congr' 1 a b = lvl_N_congr' 1 c d := by
  simp [lvl_N_congr']
  simp only [eq_iff_true_of_subsingleton]



def lvl1_equiv (a b c d : ℤ) : (lvl_N_congr' 1 a b) ≃ (lvl_N_congr' 1 c d) := by
  refine Equiv.Set.ofEq (lvl_1_congr a b c d)

open Pointwise


def vec_equiv_2 : (⋃ n : ℕ, int_vec_gcd_n n)  ≃  (⋃ n : ℕ, ({n} : Set ℕ)  • (lvl_N_congr' 1 0 0)) where
  toFun := fun v =>
    ⟨(v.1 0).gcd (v.1 1) • ![(v.1 0)/(v.1 0).gcd (v.1 1), (v.1 1)/(v.1 0).gcd (v.1 1)], by
    simp only [mem_iUnion]
    use (v.1 0).gcd (v.1 1)
    by_cases hn : 0 < (v.1 0).gcd (v.1 1)
    apply Set.smul_mem_smul
    simp
    rw [lvl_N_congr'_mem]
    simp  [Matrix.cons_val_zero, Int.cast_zero, Matrix.cons_val_one,eq_iff_true_of_subsingleton,
       Matrix.head_cons]

    apply  Int.gcd_div_gcd_div_gcd hn
    simp at hn
    rw [hn]
    simp
    rw [Set.zero_smul_set]
    simp
    use ![1,1]
    simp [eq_iff_true_of_subsingleton]
    ⟩
  invFun := fun v => ⟨ v.1, by simp⟩
  left_inv := by
    intro v
    simp
    ext i
    fin_cases i
    by_cases hv : v.1 = 0
    simp
    rw [hv]
    simp
    simp
    apply Int.mul_ediv_cancel'
    exact Int.gcd_dvd_left (v.1 0) (v.1 1)
    apply Int.mul_ediv_cancel'
    exact Int.gcd_dvd_right (v.1 0) (v.1 1)
  right_inv := by
    intro v
    ext i
    fin_cases i
    simp
    apply Int.mul_ediv_cancel'
    exact Int.gcd_dvd_left (v.1 0) (v.1 1)
    apply Int.mul_ediv_cancel'
    exact Int.gcd_dvd_right (v.1 0) (v.1 1)

def top_equiv : ((Fin 2) → ℤ) ≃ (⋃ n : ℕ, ({n} : Set ℕ)  • (lvl_N_congr' 1 0 0)) := by
  apply Equiv.trans vec_gcd_vec_equiv vec_equiv_2



lemma smul_disjoint ( i j : ℕ) (hij : i ≠ j) : Disjoint (({i} : Set ℕ)  • (lvl_N_congr' 1 0 0))
  (({j} : Set ℕ)  • (lvl_N_congr' 1 0 0)) := by
  simp only [singleton_smul]
  sorry


section

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

def gcd_one_to_SL_bot_row (a b : ℤ) (hab : a.gcd b =1) : SL(2, ℤ) := by
  use !![ Int.gcdB a b,  -Int.gcdA a b; a, b]
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
    norm_cast at this

def GammaSLinv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) (f : lvl_N_congr' N a b) :
  (lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) := by
  use Matrix.vecMul f.1 A.1
  simp
  have hf := f.2
  rw [lvl_N_congr'_mem] at hf
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A
  simp_rw [Matrix.vecMul, Matrix.dotProduct] at *
  simp at *
  simp_rw [hf.1, hf.2.1]
  simp
  convert this

@[simp]
lemma GammaSLinv_apply (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) (f : lvl_N_congr' N a b) :
  (GammaSLinv N a b A f).1 = Matrix.vecMul f.1 A.1 := by rfl

lemma a_a_inv  (a b : ℤ )  (A  : SL(2,ℤ)) :
  Matrix.vecMul (Matrix.vecMul (![a,b]) A.1) A⁻¹.1 = ![a,b] := by
  --have hi := Matrix.vecMul_vecMul ![a,b]
  simp
  rw [Matrix.mul_adjugate, A.2]
  simp

def GammaSLinv' (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ))
  (f : lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) :
  (lvl_N_congr' N a b) := by
  use Matrix.vecMul f.1 A⁻¹.1
  have hf := f.2
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A⁻¹
  have hi := Matrix.vecMul_vecMul ![(a : ZMod N),(b : ZMod N)]
    (Matrix.map A.1 ((↑) : ℤ→  (ZMod N))) (Matrix.map A⁻¹.1 ((↑) : ℤ→  (ZMod N)))
  have hi2 := a_a_inv a b A
  have hh :  (![(a : ZMod N),(b : ZMod N)] : (Fin 2) → (ZMod N)) =  ((↑) : ℤ →  (ZMod N)) ∘ ![a,b] :=
    by
    funext i
    fin_cases i
    simp
    rfl
  have HI : ((↑) : ℤ →  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))  =
    (![(a : ZMod N),(b : ZMod N)] : (Fin 2) → (ZMod N)) := by
    rw [hh]
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl] at *
    convert hi
    ext i
    fin_cases i
    simp  [Fin.mk_zero, comp_apply, Matrix.vecMul_vecMul]
    simp_rw [Matrix.vecMul,  Matrix.dotProduct] at *

    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_fin_const, mul_neg, Int.cast_add,
      Int.cast_mul, Int.cast_neg, Matrix.head_cons]
    --simp_rw [Matrix.vecHead,Matrix.vecTail,Matrix.transpose,Matrix.cramer,Matrix.cramerMap, Matrix.mul]

    rw [hf.1, hf.2.1]
    simp  [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul, Matrix.mul_apply]
    ring
    simp  [Fin.mk_zero, comp_apply, Matrix.vecMul_vecMul]
    simp_rw [Matrix.vecMul,  Matrix.dotProduct] at *

    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_fin_const, mul_neg, Int.cast_add,
      Int.cast_mul, Int.cast_neg, Matrix.head_cons]
    --simp_rw [Matrix.vecHead,Matrix.vecTail,Matrix.transpose,Matrix.cramer,Matrix.cramerMap, Matrix.mul]

    rw [hf.1, hf.2.1]
    simp  [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul, Matrix.mul_apply]
    ring
    rw [←hi2]
    simp only [Matrix.vecMul_vecMul]
    ext i
    fin_cases i
    simp only [Fin.mk_zero, comp_apply]
    simp_rw [Matrix.vecMul,  Matrix.dotProduct] at *
    simp  [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul, Matrix.mul_apply]
    simp only [Fin.mk_zero, comp_apply]
    simp_rw [Matrix.vecMul,  Matrix.dotProduct] at *
    simp  [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul, Matrix.mul_apply]
  constructor
  have HI0 : (((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))) 0 = (a : ZMod N) := by
    rw [HI]
    simp only [Matrix.cons_val_zero]
  simpa using HI0
  constructor
  have HI1 : (((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))) 1 = (b : ZMod N) := by
    rw [HI]
    simp [Matrix.cons_val_zero]
  simpa using HI1
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A⁻¹
  convert this
  ext i
  fin_cases i
  rfl
  rfl
  ext i
  fin_cases i
  rfl
  rfl


lemma GammaSLleftinv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ))  (v : lvl_N_congr' N a b) :
    GammaSLinv' N a b A  (GammaSLinv N a b A v) = v := by
  rw [GammaSLinv', GammaSLinv]
  simp
  apply Subtype.ext
  simp
  rw [Matrix.mul_adjugate, A.2]
  simp

lemma GammaSLrightinv (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ))
  (v : lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) :
    GammaSLinv N a b A  (GammaSLinv' N a b A v) = v := by
  rw [GammaSLinv', GammaSLinv]
  simp
  apply Subtype.ext
  simp
  rw [Matrix.adjugate_mul, A.2]
  simp

def GammaSLinv_equiv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) : (lvl_N_congr' N a b) ≃
  (lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) where
    toFun := GammaSLinv N a b A
    invFun := GammaSLinv' N a b A
    left_inv v:= GammaSLleftinv N a b A v
    right_inv v:= GammaSLrightinv N a b A v

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
  convert this
  simp
  simp_rw [Matrix.vecMul,Matrix.dotProduct,Matrix.vecCons]
  simp
  simp_rw [Matrix.vecMul,Matrix.dotProduct,Matrix.vecCons]
  simp


/-
variables (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ))(v : lvl_N_congr' N a b)
#check  GammaSLinv N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) A⁻¹ (GammaSLinv N a b A v)


lemma GammaSLleftinv (N : ℕ)  (a b : ℤ ) (A  : SL(2,ℤ))(v : lvl_N_congr' N a b) :
  GammaSLinv N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) A⁻¹  (GammaSLinv N a b A v)  := by
-/


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


def Gammainv_Equiv_eq (N : ℕ)  (a b : ℤ ) (γ  : Gamma N) (v : (lvl_N_congr' N a b)) :
  ((Gammainv N a b γ) v).1 =
    ( (Matrix.SpecialLinearGroup.toLin' (SpecialLinearGroup.transpose γ.1) ).toEquiv) v.1 := by
  simp_rw [Gammainv]
  simp
  simp_rw [Matrix.SpecialLinearGroup.toLin'_apply, SpecialLinearGroup.transpose]
  simp
  rw [Matrix.mulVec_transpose]


def prod_fun_equiv : ℤ × ℤ ≃ (Fin 2 → ℤ) := by exact (piFinTwoEquiv fun _ => ℤ).symm

def index_equiv (N : ℕ)  (a b : ℤ ) : (lvl_N_congr' N a b) ≃ (lvl_N_congr N a b)  := by
  apply Equiv.subtypeEquiv (piFinTwoEquiv fun _ => ℤ)
  rw [piFinTwoEquiv ]
  simp



lemma summable_Eisenstein_N_tsum (k : ℤ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ):
  Summable (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1) ) := by
  apply (Eisenstein_tsum_summable k z hk).subtype


def vector_eise (k : ℤ) (z : ℍ) (v : (Fin 2) → ℤ) : ℂ := (eise k z ((piFinTwoEquiv fun _ => ℤ) v))

def feise (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b)) : ℂ := (eise k z ((piFinTwoEquiv fun _ => ℤ) v.1))


section smulsec

open Pointwise


def smullset (n N : ℕ) ( a b : ℤ): Set ((Fin 2) → ℤ) := ( ({n} : Set ℕ)  • (lvl_N_congr' N a b))



def lvl_n_smul_dvd (n N : ℕ) (a b  : ℤ) (v : smullset (n+1) N a b) :
  (lvl_N_congr'  N a b) := by
  use ![v.1 0 /(n + 1), v.1 1 /(n + 1)]
  have hv2 := v.2
  simp_rw [smullset] at *
  rw [Set.mem_smul] at hv2
  simp at hv2
  obtain ⟨H, HH⟩:= hv2
  simp at *
  rw [←HH.1.1, ←HH.1.2.1]

  have HT := HH.2
  rw [←HT]
  simp
  norm_cast
  have B : ((n + 1)  * H) 0 /(n + 1) = H 0 :=  by
    refine Int.ediv_eq_of_eq_mul_right ?H1 rfl
    norm_cast at *
    linarith
  have B1 : ((n + 1)  * H) 1 /(n + 1) = H 1 :=  by
    refine Int.ediv_eq_of_eq_mul_right ?H2 rfl
    norm_cast at *
    linarith
  constructor
  exact congrArg Int.cast B
  constructor
  exact congrArg Int.cast B1
  norm_cast at *
  convert HH.1.2.2
/-
have hv2 := v.2
rw [Set.mem_smul] at hv2
let H:= hv2.choose_spec
use H.choose
have := H.choose_spec
apply this.2.1
  -/
lemma lvl_n_smul_eq_dvd (n : ℕ)  (v : smullset (n+1) N a b) :
  (lvl_n_smul_dvd n _ _ _ v).1 = ![ v.1 0 / (n + 1), v.1 1 /(n + 1)] := by
  rfl

lemma nsmul_v_zero (m N : ℕ) (a b  : ℤ) (h : m = 0) (v : smullset m N a b) :
   v.1 = 0 := by
  have hv2 := v.2
  simp_rw [smullset] at *
  rw [Set.mem_smul] at hv2
  obtain ⟨x,y,H1, H2⟩ := hv2
  rw [h] at *
  simp at *
  rw [y] at H2
  simp at H2
  have H22:= H2.2
  rw [←H22]
  ext1
  simp

lemma nsmul_div_n (n N : ℕ) (a b  : ℤ) (v : smullset n N a b) (i : Fin 2) :
  n * ((v.1 i) /n) = v.1 i := by
  by_cases hn : n = 0
  have := nsmul_v_zero n N a b hn v
  rw [this]
  simp
  apply Int.mul_ediv_cancel'
  have hv2 := v.2
  simp_rw [smullset] at *
  rw [Set.mem_smul] at hv2
  obtain ⟨x,y,H1, H2⟩ := hv2
  simp at *
  have h2 := H2.2
  refine dvd_def.mpr ?_
  use H1 i
  rw [←h2]
  simp
  left
  exact y


def prod_equiv : ℕ × (lvl_N_congr' 1 0 0) ≃ (Σ n : ℕ, smullset (n+1) 1 0 0) where
  toFun := fun r => ⟨r.1,(r.1+1) • r.2.1, by
    simp_rw [smullset] at *
    rw [Set.mem_smul]
    use r.1+1
    simp
    use r.2
    simp [eq_iff_true_of_subsingleton]
    have hr2 := r.2.2
    rw [lvl_N_congr'_mem] at hr2
    exact hr2.2.2
    ⟩
  invFun := fun v => ⟨v.1, (lvl_n_smul_dvd v.1 _ _ _ v.2), by simp  ⟩
  left_inv := by
    intro v
    simp
    congr
    rw [lvl_n_smul_dvd]
    simp
    congr
    ext i
    fin_cases i
    simp
    refine EuclideanDomain.mul_div_cancel_left (v.2.1 0) ?e_snd.e_val.h.head.a0
    linarith
    simp
    refine EuclideanDomain.mul_div_cancel_left (v.2.1 1) ?e_snd.e_val.h.head.a0
  right_inv := by
    intro v
    simp
    congr
    rw [lvl_n_smul_dvd]
    simp
    ext i
    fin_cases i
    simp
    apply nsmul_div_n
    simp
    apply nsmul_div_n



lemma feise_smul (k a b : ℤ) (n N: ℕ) (z : ℍ) (v : smullset (n+1) N a b):
  vector_eise k z v = (1/((n+1)^k)) * feise k z (lvl_n_smul_dvd n _ _ _ v) := by
    simp_rw [vector_eise, feise,  smullset,lvl_n_smul_dvd, eise]
    simp
    field_simp
    congr
    rw [← mul_zpow]
    have := nsmul_div_n (n+1) N a b v 1
    have t0 := nsmul_div_n (n+1) N a b v 0
    conv =>
      enter [2,1]
      rw [mul_add]
      norm_cast
      rw [this]
      conv =>
        enter [1]
        rw [←mul_assoc]
        norm_cast
        rw [t0]


def nsmul_equiv (n : ℕ) :  smullset (n+1) 1 0 0 ≃ (lvl_N_congr' 1 0 0) where
  toFun := fun v => lvl_n_smul_dvd n _ _ _ v
  invFun := fun v => ⟨(n+1 : Fin 2 → ℤ) * v.1, by
    rw [smullset, Set.mem_smul]
    use n+1
    simp
    use v
    have hv := v.2
    rw [lvl_N_congr'_mem] at hv
    simp [hv]⟩
  left_inv := by
    intro v
    simp
    ext1
    simp [lvl_n_smul_dvd]
    ext1 i
    fin_cases i
    simp
    apply nsmul_div_n
    simp
    apply nsmul_div_n
  right_inv := by
    intro v
    ext1
    simp [lvl_n_smul_dvd]
    ext1 i
    fin_cases i
    simp
    rw [Int.mul_ediv_cancel_left ]
    linarith
    simp
    rw [Int.mul_ediv_cancel_left ]
    linarith

lemma mul_gcd_div_gcd_cancel_a (a b : ℤ) : (a.gcd b) * (a / (a.gcd b)) = a := by
  refine Int.mul_ediv_cancel' ?H
  exact Int.gcd_dvd_left a b


lemma mul_gcd_div_gcd_cancel_b (a b : ℤ) : (a.gcd b) * (b / (a.gcd b)) = b := by
  refine Int.mul_ediv_cancel' ?H
  exact Int.gcd_dvd_right a b

lemma feise_smul2 (k : ℤ)  (z : ℍ) (v : (Fin 2) → ℤ):
  vector_eise k z v =
    (1/(((v 0).gcd (v 1))^k)) * eise k z ⟨(v 0 / ((v 0).gcd (v 1))), (v 1 / ((v 0).gcd (v 1)))⟩ := by
    simp_rw [vector_eise, eise]
    simp
    field_simp
    congr
    rw [← mul_zpow]
    ring_nf
    conv =>
     enter [2,1,2]
     norm_cast
     rw [mul_gcd_div_gcd_cancel_b (v 0) (v 1)]
    conv =>
     enter [2,1,1]
     rw [mul_assoc]
     norm_cast
     rw [mul_gcd_div_gcd_cancel_a (v 0) (v 1), mul_comm]

def Eisenstein_1_tsum (k : ℤ) : ℍ → ℂ := fun z =>  ∑' x : Fin 2 → ℤ, (vector_eise k z x)



/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (lvl_N_congr'  N a b),
  (feise k z  x)


lemma summable_vector_eise (k : ℤ) (hk : 3 ≤ k): Summable (fun x => (vector_eise k z x)) := by
  let e := (piFinTwoEquiv fun _ => ℤ)
  have : (fun x => (vector_eise k z x)) = (fun x : ℤ × ℤ => eise k z x) ∘ e := by
    simp [vector_eise]
    rfl
  rw [this, Equiv.summable_iff]
  exact (Eisenstein_tsum_summable k z hk)


lemma summable_Eisenstein_N_tsum' (k : ℤ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ):
  Summable (fun (x : (lvl_N_congr'  N a b)) => feise k z x)  := by
  have : (fun (x : (lvl_N_congr'  N a b)) => feise k z x) =
   (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1)) ∘ (index_equiv N a b) := by
    ext1 v
    simp
    congr
  rw [this, Equiv.summable_iff]
  apply summable_Eisenstein_N_tsum k hk



lemma feise_eq_one_div_denom (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b))  : feise k z v =
  1/(UpperHalfPlane.denom (gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) z)^(k) := by
  rw [feise, denom,gcd_one_to_SL_bot_row]
  simp
  rw [eise]
  simp



def equivla (A : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ :=
  (prod_fun_equiv.trans (Matrix.SpecialLinearGroup.toLin' A).toEquiv).trans  prod_fun_equiv.symm



lemma averaver (A: SL(2, ℤ)) : equivla  (SpecialLinearGroup.transpose A)  = MoebiusEquiv A  := by
  rw [equivla, prod_fun_equiv]
  simp only [Equiv.symm_symm, Equiv.coe_trans, piFinTwoEquiv_apply, LinearEquiv.coe_toEquiv,
  piFinTwoEquiv_symm_apply,
    MoebiusEquiv,MoebiusPerm, Matrix.SpecialLinearGroup.coe_inv]
  ext1 v
  simp only [Equiv.trans_apply, piFinTwoEquiv_symm_apply, LinearEquiv.coe_toEquiv,
    piFinTwoEquiv_apply, Equiv.coe_fn_mk, Prod.mk.injEq, MoebiusPerm]
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


theorem feise_Moebius (k : ℤ) (z : ℍ) (N : ℕ) (A : Gamma N) (i : (lvl_N_congr'  N a b)) :
    feise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * feise k z ((Gammainv_Equiv N a b A)  i) := by
    simp_rw [feise]
    have := eise_Moebius k z A.1 ((piFinTwoEquiv fun _ => ℤ) i.1)
    convert this
    rw [←averaver A, equivla,Gammainv_Equiv]
    simp
    rw [Gammainv_Equiv_eq]
    simp
    simp_rw [Matrix.SpecialLinearGroup.toLin'_apply,prod_fun_equiv]
    simp
    constructor
    rfl
    rfl

def Eisenstein_SIF_lvl_N (N : ℕ) (k a b : ℤ) : SlashInvariantForm (Gamma N) k
    where
  toFun := Eisenstein_N_tsum k N a b
  slash_action_eq' := by
    intro A
    ext1 x
    simp_rw [slash_action_eq'_iff]
    rw [Eisenstein_N_tsum]
    simp only [UpperHalfPlane.subgroup_to_sl_moeb, UpperHalfPlane.sl_moeb]
    convert (tsum_congr (feise_Moebius k x N A))
    have h3 := Equiv.tsum_eq (Gammainv_Equiv N a b A) (feise k x)
    rw [tsum_mul_left, h3, Eisenstein_N_tsum]
    norm_cast

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f


lemma int_cast_abs_self (N : ℤ) : (N : ZMod (Int.natAbs N)) = 0 := by
  refine Iff.mpr (ZMod.int_cast_zmod_eq_zero_iff_dvd N (Int.natAbs N)) ?_
  simp only [Int.coe_natAbs, abs_dvd, dvd_refl]

lemma T_pow_N_mem_Gamma (N : ℤ) : (ModularGroup.T^N) ∈ _root_.Gamma (Int.natAbs N) := by
  simp
  simp_rw [ModularGroup.coe_T_zpow]
  simp
  apply int_cast_abs_self

lemma T_pow_N_mem_Gamma' (N n : ℤ) : (ModularGroup.T^N)^n ∈ _root_.Gamma (Int.natAbs N) := by
  exact Subgroup.zpow_mem (_root_.Gamma (Int.natAbs N)) (T_pow_N_mem_Gamma N) n


local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)


lemma slash_apply (k : ℤ) (A : SL(2,ℤ)) (f : ℍ → ℂ) (z : ℍ): (f∣[k,A]) z =
  f (A • z)  * denom A z ^ (-k) := by
  simp only [SL_slash, slash_def, ModularForm.slash,denom, Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
    zpow_neg, Matrix.SpecialLinearGroup.det_coe, ofReal_one, one_zpow, mul_one, subgroup_to_sl_moeb]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply,
    ofReal_int_cast, uhc, UpperHalfPlane.sl_moeb]
  norm_cast

  congr
  simp

lemma denom_cocycle_SL  (N : ℕ) (a b : ℤ) (A : SL(2,ℤ)) (v : (lvl_N_congr'  N a b)) (z : ℍ) :
  denom ((gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) * A) z =
    denom ((gcd_one_to_SL_bot_row ((GammaSLinv_equiv N a b A v).1 0)
      ((GammaSLinv_equiv N a b A v).1 1) (GammaSLinv_equiv N a b A v).2.2.2)) z := by
  simp
  simp_rw [denom, gcd_one_to_SL_bot_row, GammaSLinv_equiv]
  simp [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul,
    Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom, uhc, Equiv.coe_fn_mk, GammaSLinv_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_fin_const, ofReal_int_cast, Matrix.head_cons]
  simp_rw [Matrix.vecMul, Matrix.dotProduct, Matrix.mul_apply]
  simp


lemma Eisenstein_lvl_N_Sl_inv (N : ℕ) (k : ℤ) (hk : 3 ≤ k) (a b : ℤ) (A : SL(2,ℤ)) :
  (((Eisenstein_SIF_lvl_N N (k : ℤ) a b).1)∣[(k : ℤ),A]) =
    (((Eisenstein_SIF_lvl_N N k (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)).1)) := by
  ext1 z
  have := slash_apply k A ((Eisenstein_SIF_lvl_N N k a b).1) z
  rw [this]
  simp only [SlashInvariantForm.toFun_eq_coe]
  simp_rw [Eisenstein_SIF_lvl_N]
  simp only [SlashInvariantForm.coe_mk]
  rw [Eisenstein_N_tsum]
  rw [Eisenstein_N_tsum]
  have := @feise_eq_one_div_denom N a b k (A • z)
  have t2 := @feise_eq_one_div_denom N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1) k (z)
  simp [uhc]
  convert (Equiv.tsum_eq (GammaSLinv_equiv N a b A) _)
  norm_cast
  rw [←Summable.tsum_mul_right]
  apply tsum_congr
  intro v
  have tt2 := this v
  simp at tt2
  simp_rw [tt2]
  rw [t2]
  simp only [cpow_int_cast, one_div, zpow_neg]
  rw [←mul_inv]
  congr
  rw [←mul_zpow]
  congr
  have cocy:= UpperHalfPlane.denom_cocycle (gcd_one_to_SL_bot_row (v.1 0) (v.1 1) v.2.2.2) A z
  have seq : A • z = smulAux A z := by rfl
  simp at seq
  rw [seq]
  rw [←cocy]
  have HF:= denom_cocycle_SL N a b A v z
  exact HF
  apply summable_Eisenstein_N_tsum' k hk
  exact T25Space.t2Space

lemma tsum_subtype_le {α : Type} (f : α → ℝ) (β : Set α) (hf : ∀ a : α, 0 ≤ f a) (hf2 : Summable f) :
  (∑' (b : β), f b) ≤ (∑' (a : α), f a) := by
  have := tsum_subtype_add_tsum_subtype_compl hf2 β
  rw [← this]
  simp
  apply tsum_nonneg
  intro b
  apply hf b

lemma UBOUND (N : ℕ) (a b : ℤ) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
  Complex.abs ((((Eisenstein_SIF_lvl_N N k a b))) z) ≤ (AbsEisenstein_tsum k z) := by
  simp_rw [Eisenstein_SIF_lvl_N, AbsEisenstein_tsum]
  simp
  apply le_trans (abs_tsum' ?_)
  simp_rw [feise, eise]
  have := Equiv.tsum_eq prod_fun_equiv.symm (fun x : ℤ × ℤ => (AbsEise k z x))
  rw [←this]

  have Ht := tsum_subtype_le (fun x : (Fin 2 → ℤ)  => (AbsEise k z (prod_fun_equiv.symm x)))
    (lvl_N_congr' N a b) ?_ ?_
  simp_rw [AbsEise] at *
  simp at *
  apply le_trans Ht
  rfl
  intro v
  simp_rw [AbsEise]
  simp

  apply zpow_nonneg (Complex.abs.nonneg _)
  have := real_eise_is_summable k z hk
  rw [←Equiv.summable_iff prod_fun_equiv.symm] at this
  exact this
  rw [←summable_iff_abs_summable]
  apply summable_Eisenstein_N_tsum' k hk


theorem lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T^N)^n)  • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k (Gamma N) f
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h
  have Hn :=  (T_pow_N_mem_Gamma' N n)
  simp only [zpow_coe_nat, Int.natAbs_ofNat] at Hn
  have H:= h ((ModularGroup.T^N)^n) Hn z
  rw [H]
  have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by
      rw [zpow_mul]
      simp
  simp_rw [this]
  have hh := ModularGroup.coe_T_zpow (N*n)
  rw [slcoe (ModularGroup.T^(N*n)) 1 0, slcoe (ModularGroup.T^(N*n)) 1 1, hh]
  ring_nf
  simp

theorem Eisenstein_series_is_bounded (a b: ℤ) (N: ℕ) (k : ℤ) (hk : 3 ≤ k) (A : SL(2, ℤ)) (hN : 0 < (N : ℤ)) :
    IsBoundedAtImInfty ((Eisenstein_SIF_lvl_N N (k : ℤ) a b).1∣[(k : ℤ),A]) :=
  by
  simp_rw [UpperHalfPlane.bounded_mem] at *
  let M : ℝ := 8 / rfunct (lbpoint N 2 <| by linarith) ^ k * Complex.abs (riemannZeta (k - 1))
  use M
  use 2
  intro z hz
  obtain ⟨n, hn⟩ := (upp_half_translation_N z N hN)
  rw [Eisenstein_lvl_N_Sl_inv]
  have := lvl_N_periodic N k (Eisenstein_SIF_lvl_N N k (Matrix.vecMul ![a, b] (A.1) 0)
    (Matrix.vecMul ![a, b] (A.1) 1)) z n
  simp only [SlashInvariantForm.toFun_eq_coe, Real.rpow_int_cast, ge_iff_le]
  rw [←this]
  apply le_trans (UBOUND N _ _ k hk ((ModularGroup.T ^ N) ^ n • z))
  let Z := ((ModularGroup.T ^ N) ^ n) • z
  have hZ : Z ∈ upperHalfSpaceSlice N 2 :=
    by
    norm_cast at *
    rw [slice_mem] at *
    constructor
    apply hn.1
    simp only [map_zpow, map_pow, abs_ofReal, ge_iff_le] at *
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by
      rw [zpow_mul]
      simp
    rw [this] at *
    rw [modular_T_zpow_smul] at *
    simp
    have va := UpperHalfPlane.vadd_im ((N : ℝ)*n) z
    simp_rw [UpperHalfPlane.im] at *
    simp at va
    rw [va]
    convert hz
    simp
    apply z.2.le
  have := AbsEisenstein_bound_unifomly_on_stip ( k) hk N 2 (by linarith) ⟨Z, hZ⟩
  convert this
  apply hk

def upperHalfPlaneSlice (A B : ℝ) :=
  {z : ℍ | Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B}

lemma compact_in_some_slice (K : Set ℍ) (hK : IsCompact K) : ∃  A B : ℝ, 0 < B ∧
    K ⊆ upperHalfPlaneSlice A B  := by
  by_cases hne : Set.Nonempty K
  have hcts : ContinuousOn (fun t =>  t.im) K := by
    apply Continuous.continuousOn
    apply UpperHalfPlane.continuous_im
  have := IsCompact.exists_isMinOn hK hne hcts
  obtain ⟨b, _, HB⟩ := this
  let t := (⟨Complex.I, by simp⟩ : ℍ)
  have hb2 := Bornology.IsBounded.subset_closedBall_lt hK.isBounded 0 t
  obtain ⟨r, hr, hr2⟩ := hb2
  refine' ⟨Real.sinh (r) + Complex.abs ((UpperHalfPlane.center t r)), b.im, _⟩
  constructor
  apply b.2
  intro z hz
  simp  [slice_mem, coe_re, coe_im, ge_iff_le, top_eq_univ,
    image_univ, range_inclusion] at *
  constructor
  have hr3 := hr2 hz
  simp  at hr3
  norm_cast at *
  apply le_trans (abs_re_le_abs z)
  have := Complex.abs.sub_le (z : ℂ) (UpperHalfPlane.center t r) 0
  simp  [sub_zero, Subtype.coe_mk, abs_I] at this
  rw [dist_le_iff_dist_coe_center_le] at hr3
  simp at *
  apply le_trans this
  simp
  have htim : UpperHalfPlane.im t = 1 := by
     simp [UpperHalfPlane.im ]
  rw [htim] at hr3
  simp at hr3
  apply hr3
  have hbz := HB  hz
  simp at *
  convert hbz
  simp [UpperHalfPlane.im ]
  apply z.2.le
  rw [not_nonempty_iff_eq_empty] at hne
  rw [hne]
  simp
  use 1
  linarith



def lvl_N_upp_bound (a b : ℤ) (N k : ℕ)  : (lvl_N_congr'  N a b) → ℍ → ℝ :=
  fun x : (lvl_N_congr'  N a b)  => fun (z : ℍ') =>
    (1/(rfunct (z)^k))* ( (max (((piFinTwoEquiv fun _ => ℤ).1 x).1).natAbs
    (((piFinTwoEquiv fun _ => ℤ).1 x).2).natAbs : ℝ)^k)⁻¹

lemma  Eisenstein_lvl_N_tendstolocunif2 (a b k: ℤ) (N : ℕ) (hk : 3 ≤ k) :
  TendstoLocallyUniformlyOn ((fun (s : Finset (lvl_N_congr'  N a b)) =>
    (fun (z : ℍ) => ∑ x in s, eise k z ((piFinTwoEquiv fun _ => ℤ).1 x)) ) )
    ( fun (z : ℍ) => (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1 z) atTop  ⊤ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  --intro K hK hK2
  rw [Eisenstein_SIF_lvl_N]

  simp [Eisenstein_N_tsum]
  intros K hK
  obtain ⟨A,B,hB, HABK⟩:= compact_in_some_slice K hK
  let u :=  fun x : (lvl_N_congr'  N a b)  =>
    (1/(rfunct (lbpoint A B hB)^k))* ( (max (((piFinTwoEquiv fun _ => ℤ).1 x).1).natAbs
    (((piFinTwoEquiv fun _ => ℤ).1 x).2).natAbs : ℝ)^k)⁻¹
  have hu : Summable u := by
    have := summable_upper_bound k hk (lbpoint A B hB)
    rw [← Equiv.summable_iff (piFinTwoEquiv fun _ => ℤ)] at this
    simp at this
    have := Summable.subtype this (lvl_N_congr'  N a b)
    apply this.congr
    intro v
    simp
  apply tendstoUniformlyOn_tsum hu
  intro v x hx
  have hkgt1 : 1 ≤ k := by linarith
  have sq := square_mem (max (((piFinTwoEquiv fun _ => ℤ).1 v).1).natAbs
  (((piFinTwoEquiv fun _ => ℤ).1 v).2).natAbs ) ⟨(v.1 0), v.1 1⟩
  simp at sq
  have hk0 : 0 ≤ k := by linarith
  have := Eise_on_square_is_bounded'' k hk0 x (max (((piFinTwoEquiv fun _ => ℤ).1 v).1).natAbs
    (((piFinTwoEquiv fun _ => ℤ).1 v).2).natAbs ) hkgt1 ⟨(v.1 0), v.1 1⟩
  simp  at this
  rw [eise]
  simp
  apply le_trans (this sq)
  rw [mul_comm]
  apply mul_le_mul
  rw [inv_le_inv]
  lift k to ℕ using hk0
  apply pow_le_pow_left
  apply (rfunct_pos _).le
  rw [abs_of_pos (rfunct_pos _)]
  exact rfunct_lower_bound_on_slice A B hB ⟨x, HABK hx⟩
  lift k to ℕ using hk0
  apply pow_pos (rfunct_abs_pos _)
  lift k to ℕ using hk0
  apply pow_pos (rfunct_pos _)
  rfl
  simp only [ge_iff_le, Nat.cast_le, inv_nonneg, le_max_iff, Nat.cast_nonneg, or_self, zpow_nonneg]
  simp only [inv_nonneg, ge_iff_le]
  apply zpow_nonneg (rfunct_pos _).le
  simp only [top_eq_univ, isOpen_univ]



lemma  Eisenstein_lvl_N_tendstolocunif (a b: ℤ) (N : ℕ) (k : ℤ) (hk : 3 ≤ k) :
  TendstoLocallyUniformlyOn ((fun (s : Finset (lvl_N_congr'  N a b)) => extendByZero
    (fun (z : ℍ) => ∑ x in s, eise k z  ((piFinTwoEquiv fun _ => ℤ).1 x)) ) )
    (extendByZero (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1) atTop ℍ' := by
  have := Eisenstein_lvl_N_tendstolocunif2 a b k N hk
  simp at *
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact] at *
  simp at this
  intro K hk1 hk2
  let S := Set.image (Set.inclusion hk1) ⊤
  have HH := this S
  have hS : IsCompact S := by
    simp
    refine Subtype.isCompact_iff.mpr ?_
    convert hk2
    exact Subtype.coe_image_of_subset hk1
    --apply upper_half_plane_isOpen
  have H3:= HH hS
  clear HH
  rw [tendstoUniformlyOn_iff] at *
  intro ε hε
  have H4:= H3 ε hε
  simp at *
  obtain ⟨T, H5⟩ := H4
  use T
  intro J hJ r hr
  have H6 := H5 J hJ ⟨r, hk1 hr⟩ hr
  simp at *
  convert H6
  have t1:= ext_by_zero_apply ℍ' (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1 ⟨r, hk1 hr⟩
  exact t1
  have t2 := ext_by_zero_apply ℍ'
    (fun (z : ℍ) => ∑ x in J, eise k z  ((piFinTwoEquiv fun _ => ℤ).1 x)) ⟨r, hk1 hr⟩
  exact t2
  simp
  apply upper_half_plane_isOpen

local notation "↑ₕ" => holExtn

theorem Eisenstein_lvl_N_is_holomorphic (a b: ℤ) (N : ℕ) (k : ℤ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (Eisenstein_SIF_lvl_N N (k : ℤ) a b).1) :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  have hc := Eisenstein_lvl_N_tendstolocunif a b N k hk
  haveI : NeBot (⊤ : Filter (Finset (lvl_N_congr'  N a b))) := by
    refine Iff.mp forall_mem_nonempty_iff_neBot ?_
    intro t ht
    simp at *
    rw [ht]
    simp only [univ_nonempty]
  refine' hc.differentiableOn (eventually_of_forall fun s => _) ?_
  have := Eise'_has_diff_within_at k
  have ht : (extendByZero fun z => ∑ x in s, eise (↑k) z (Equiv.toFun (piFinTwoEquiv fun _ => ℤ) ↑x))
    = (fun w => ∑ y in s,  extendByZero (fun z => eise (↑k) z ((Equiv.toFun (piFinTwoEquiv fun _ => ℤ)) y)) w) :=
    by
    funext z
    simp  [extendByZero, Finset.sum_dite_irrel, Finset.sum_const_zero]
  simp at *
  have hd : DifferentiableOn  ℂ
    (extendByZero fun z => ∑ x in s, eise (↑k) z (Equiv.toFun (piFinTwoEquiv fun _ => ℤ) ↑x)) ℍ' :=
      by
      simp at *
      rw [ht]
      apply DifferentiableOn.sum
      intro v _
      apply this
      linarith
  exact hd
  apply upper_half_plane_isOpen



theorem Eisenstein_lvl_N_is_mdiff (a b: ℤ) (N : ℕ) (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑ₕ (Eisenstein_SIF_lvl_N N (k : ℤ) a b)) :=
  by
  have := Eisenstein_lvl_N_is_holomorphic a b N k hk
  have h2 := (mdiff_iff_holo ( ↑ₕ (Eisenstein_SIF_lvl_N N k a b).toFun)).2 this
  convert h2


def EisensteinSeries_lvl_N_ModularForm (a b : ℤ) (N : ℕ) (k : ℤ) (hk : 3 ≤ k) (hN : 0 < (N : ℤ)) :
  ModularForm (Gamma N) k
    where
  toFun :=  (Eisenstein_SIF_lvl_N N (k : ℤ) a b)
  slash_action_eq' := by convert  (Eisenstein_SIF_lvl_N N (k : ℤ) a b).2
  holo' := Eisenstein_lvl_N_is_mdiff a b N k hk
  bdd_at_infty' A :=  Eisenstein_series_is_bounded a b N k hk A hN



lemma level_one : ModularForm (Gamma 1) k = ModularForm ⊤ k := by
  congr
  apply  Gamma_one_top

def mcastlevel {k : ℤ} {A B : Subgroup SL(2, ℤ)} (h : A = B) (f : ModularForm A k) : ModularForm B k
    where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' := by
    intro γ
    have :  γ.1 ∈ A := by
      rw [h]
      apply γ.2
    apply (f.slash_action_eq' ⟨γ.1, this⟩)
  holo' := f.holo'
  bdd_at_infty' := by
    intro S
    apply (f.bdd_at_infty' S)




theorem type_eq_level {k : ℤ} {A B : Subgroup SL(2, ℤ)} (h : A = B) :
  ModularForm A k = ModularForm B k := by
  induction h
  rfl

theorem cast_eq_mcast_level {k : ℤ} {A B : Subgroup SL(2, ℤ)} (h : A = B) (f : ModularForm A k) :
    cast (type_eq_level h) f = mcastlevel h f := by
  induction h
  ext1
  rfl

variable (a b : ℤ) (k : ℤ) (hk : 3 ≤ k )
/-
instance (k : ℤ) : Coe (ModularForm (Gamma 1) k) (ModularForm ⊤ k) where
  coe f := by
    use ⟨f.toFun, by
      have := f.slash_action_eq'
      intro γ

      have t := this
         ⟩
    apply f.holo'
    apply f.bdd_at_infty'
-/



lemma level_1_tsum_eq (a b c d : ℤ) : Eisenstein_N_tsum k 1 a b = Eisenstein_N_tsum k 1 c d := by
  funext z
  simp_rw [Eisenstein_N_tsum]
  have : (fun (x : (lvl_N_congr'  1 a b)) => feise k z x) =
   (fun (x : (lvl_N_congr'  1 c d)) => (feise k z  x)) ∘ (lvl1_equiv a b c d) := by
    ext1 v
    simp
    congr
  rw [this]
  apply Equiv.tsum_eq


lemma level_1_SIF_eq (a b c d : ℤ) : (Eisenstein_SIF_lvl_N 1 (k : ℤ) a b) =
  (Eisenstein_SIF_lvl_N 1 (k : ℤ) c d) := by
  simp_rw [Eisenstein_SIF_lvl_N]
  simp
  apply (level_1_tsum_eq k a b c d)

lemma level_1_mod_form_eq (a b c d : ℤ) : EisensteinSeries_lvl_N_ModularForm a b 1 k hk one_pos =
  EisensteinSeries_lvl_N_ModularForm c d 1 k hk one_pos := by
  apply ModularForm.ext
  intro z
  simp_rw [EisensteinSeries_lvl_N_ModularForm]
  congr
  simp
  apply (level_1_SIF_eq k a b c d)


lemma Aux1 (z : ℍ) (k : ℕ ) :  ∑' (x : (⋃ n : ℕ, ({n} : Set ℕ)  • (lvl_N_congr' 1 0 0))),
    vector_eise k z (top_equiv.symm x) =  ∑' (x : (Σn : ℕ, smullset (n) 1 0 0)),
    vector_eise k z x.2 := by
    have := smul_disjoint
    let h0 := (Set.unionEqSigmaOfDisjoint this).symm
    rw [ ← h0.tsum_eq]
    apply tsum_congr
    intro v
    congr

lemma Aux2 (z : ℍ) (k : ℕ) : ∑' (n : ℕ) (v : smullset (n+1) 1 0 0 ), vector_eise k z v =
    ∑' (n : ℕ) (v : smullset (n+1) 1 0 0 ),
      (1/((n +1)^k)) * feise k z (lvl_n_smul_dvd n _ _ _ v) := by
      apply tsum_congr
      intro b
      apply tsum_congr
      intro v
      apply feise_smul k 0 0 (b) 1 z v

lemma Aux3 (z : ℍ) (k : ℕ ) (hk : 3 ≤ k) : ∑' (n : ℕ) (v : smullset (n+1) 1 0 0 ),
      (1/((n +1)^k)) * feise k z (lvl_n_smul_dvd n _ _ _ v) = ∑' (n : ℕ) (v : (lvl_N_congr' 1 0 0) ),
      (1/((n +1)^k)) * feise k z (v) := by
        apply tsum_congr
        intro b
        rw [Summable.tsum_mul_left]
        rw [Summable.tsum_mul_left]
        simp
        left
        have := Equiv.tsum_eq (nsmul_equiv b)  (feise (k) z)
        convert this
        apply summable_Eisenstein_N_tsum'
        linarith
        have := ((nsmul_equiv b).summable_iff).2   (summable_Eisenstein_N_tsum' k ?_ 1 0 0 z)
        convert this
        linarith

lemma Aux4 (z : ℍ) (k : ℕ) (hk : 3 ≤ k):
  ∑' v : ( (lvl_N_congr' 1 0 0) ),  ((0 : ℂ)^k)⁻¹ * feise k z v = 0  := by
  have h0 : (0 : ℂ)^k = 0 := by
    simp
    linarith
  rw [h0]
  simp only [inv_zero, zero_mul, tsum_zero]

lemma aa (v : (0 : Set ((Fin 2) → ℤ))) : v.1 = 0 := by
  refine Set.mem_zero.mp ?_
  use v.2


lemma Aux5 (z : ℍ) (k : ℕ) (hk : 3 ≤ k) : ∑' (c : (smullset 0 1 0 0)), vector_eise (k) z c = 0  := by
  have h0 :  (({0} : Set ℕ) • lvl_N_congr' 1 0 0) = 0 := by
    simp
    rw [Set.zero_smul_set]
    use ![1,1]
    simp [eq_iff_true_of_subsingleton]

  have := tsum_zero (α := ℂ) (β :=  (smullset 0 1 0 0))
  rw [← this,smullset,h0]
  apply tsum_congr
  intro b
  rw [vector_eise, eise]
  simp
  constructor
  rw [aa]
  simp
  linarith



lemma Aux6 (z : ℍ) (k : ℕ) (hk : 1 < k) :
  Summable fun (b : ℕ) => ((b : ℂ) ^ k)⁻¹ * ∑' (c : (lvl_N_congr' 1 0 0)),  feise (↑k) z c := by
    apply Summable.mul_right
    have hkr : (1 : ℝ) < k := by norm_cast at *
    have riesum := Real.summable_nat_rpow_inv.2 hkr
    rw [←coe_summable] at riesum
    apply Summable.congr riesum
    intro v
    simp


lemma Aux7 (z : ℍ) (k : ℕ) (hk : 3 ≤ k) :
  Summable fun (b : ℕ) => ∑' (c : ↑(smullset b 1 0 0)), vector_eise (↑k) z ↑c := by
  have hk1 : 1 < k := by linarith
  apply Summable.congr (Aux6 z k hk1)
  intro b
  by_cases hb : b = 0
  rw [hb]
  simp
  have h0 : (0 : ℂ)^k = 0 := by
    simp
    linarith
  rw [h0]
  simp
  rw [Aux5]
  exact hk
  have := feise_smul2 k z
  have hbb : (b-1)+1=b := by
    exact Nat.succ_pred hb
  rw [←Summable.tsum_mul_left]
  rw [←hbb]
  have := Equiv.tsum_eq (j := (nsmul_equiv (b-1)).symm) (f := fun (v : smullset (b-1+1) 1 0 0)=> vector_eise k z v)
  rw [←this]
  apply tsum_congr
  intro v
  have ew := feise_smul k 0 0 (b-1) 1 z ((nsmul_equiv (b-1)).symm v)
  rw [ew]
  congr
  simp [lvl_n_smul_dvd, nsmul_equiv]
  rw [lvl_n_smul_dvd, nsmul_equiv]
  simp
  ext1
  ext1 i
  fin_cases i
  simp
  rw [Int.mul_ediv_cancel_left ]
  linarith
  simp
  rw [Int.mul_ediv_cancel_left ]
  linarith
  apply summable_Eisenstein_N_tsum'
  norm_cast

def equivvv : (Σn : ℕ, smullset (n) 1 0 0) ≃ (Fin 2 → ℤ) := by
  have e1 := Equiv.trans   vec_gcd_vec_equiv vec_equiv_2
  have := smul_disjoint
  let h0 := (Set.unionEqSigmaOfDisjoint this)
  have := (Equiv.trans e1 h0).symm
  convert this



lemma Aux8 (z : ℍ) (k : ℕ) (hk : 3 ≤ k) :
    Summable (fun x : (Σn : ℕ, smullset (n) 1 0 0)  => vector_eise k z x.2) := by
    have : (fun x : (Σn : ℕ, smullset (n) 1 0 0)  => vector_eise k z x.2) =
      vector_eise k z ∘ equivvv := by
      simp_rw [equivvv,  vec_gcd_vec_equiv, vec_equiv_2]
      simp
      ext1
      simp
      congr
    rw [this]
    rw [Equiv.summable_iff]
    apply summable_vector_eise
    norm_cast


lemma Eis_1_eq_Eis (k : ℕ ) (hk : 3 ≤ k) :
  (fun z : ℍ => (riemannZeta (k))*(Eisenstein_N_tsum k 1 0 0 z)) = Eisenstein_1_tsum k := by
  ext1 z
  have : ∑' (x : (⋃ n : ℕ, ({n} : Set ℕ)  • (lvl_N_congr' 1 0 0))),
    vector_eise k z (top_equiv.symm x) = Eisenstein_1_tsum k z := by
    rw [Eisenstein_1_tsum]
    apply top_equiv.symm.tsum_eq
  rw [←this]
  rw [Eisenstein_N_tsum]
  have H := Aux1 z k
  rw [H]
  rw [tsum_sigma]
  rw [tsum_eq_zero_add]
  have hk1 : 1 < k := by linarith
  have hr := zeta_nat_eq_tsum_of_gt_one hk1
  rw [hr]
  rw [tsum_mul_tsum_of_summable_norm]
  rw [tsum_prod]
  rw [tsum_eq_zero_add]
  have H2 := Aux2 z k
  rw [H2]
  have H3 := Aux3 z k hk
  rw [H3]
  simp only [CharP.cast_eq_zero, ne_eq, one_div, Nat.cast_add, Nat.cast_one, cpow_nat_cast,
    add_left_inj]
  have H4 := Aux4 z k hk
  simp at H4
  rw [H4]
  symm
  apply Aux5 (hk := hk)
  simp only [one_div]
  apply Summable.congr (Aux6 z k hk1)
  intro b
  symm
  apply Summable.tsum_mul_left
  apply summable_Eisenstein_N_tsum'
  norm_cast
  simp only [one_div]
  have := summable_mul_of_summable_norm (f:= fun (n : ℕ)=> ((n : ℂ)^k)⁻¹ )
    (g := fun (v : (lvl_N_congr' 1 0 0) ) => feise k z v)
  apply this
  simp
  have hkr : (1 : ℝ)< k := by norm_cast
  convert Real.summable_nat_rpow_inv.2 hkr
  simp only [Real.rpow_nat_cast]
  rw [summable_norm_iff]
  apply summable_Eisenstein_N_tsum'
  norm_cast
  simp only [one_div, norm_inv, norm_pow, norm_nat]
  have hkr : (1 : ℝ)< k := by norm_cast
  convert Real.summable_nat_rpow_inv.2 hkr
  simp only [Real.rpow_nat_cast]
  rw [summable_norm_iff]
  apply summable_Eisenstein_N_tsum'
  norm_cast
  simp
  apply Aux7
  exact hk
  apply Aux8
  exact hk
