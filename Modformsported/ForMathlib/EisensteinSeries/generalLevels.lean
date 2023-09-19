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

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

def lvl_N_congr (N : ℕ) (a b : ℤ ) := {x : ℤ × ℤ  // (x.1 : ZMod N) = a ∧ (x.2 : ZMod N) = b ∧ (x.1).gcd (x.2) = 1 }

def lvl_N_congr' (N : ℕ) (a b : ℤ ) := {f : (Fin 2) → ℤ  // (f 0 : ZMod N) = a ∧ (f 1 : ZMod N) = b ∧ 
  (f 0).gcd (f 1) = 1 }

section

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

def SpecialLinearGroup.transpose ( A:  Matrix.SpecialLinearGroup n R)  :  
  Matrix.SpecialLinearGroup n R  := by
  use A.1.transpose
  rw [Matrix.det_transpose]
  apply A.2

section gcd_to_sl_lemmas

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
    simp_rw [Matrix.vecMul] at *
    simp at *
    norm_cast at *
    simp_rw [Matrix.vecHead, Matrix.vecTail,  Matrix.mul, Matrix.dotProduct, Matrix.transpose] at *
    simp at *
    simp_rw [Matrix.vecHead] at this
    simp at this
    exact this

def GammaSLinv (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) (f : lvl_N_congr' N a b) : 
  (lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) := by
  use Matrix.vecMul f.1 A.1 
  simp
  have hf := f.2  
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A
  simp_rw [Matrix.vecMul, Matrix.vecHead] at *
  simp at *
  simp_rw [Matrix.vecHead,Matrix.vecTail, hf.1, hf.2.1]
  simp
  convert this

def GammaSLinv' (N : ℕ)  (a b : ℤ )  (A  : SL(2,ℤ)) 
  (f : lvl_N_congr' N (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)) : 
  (lvl_N_congr' N a b) := by
  use Matrix.vecMul f.1 A⁻¹.1 
  have hf := f.2  
  have := SL2_gcd (f.1 0) (f.1 1) hf.2.2 A⁻¹
  have hi := Matrix.vecMul_vecMul ![(a : ZMod N),(b : ZMod N)] 
    (Matrix.map A.1 ((↑) : ℤ→  (ZMod N))) (Matrix.map A⁻¹.1 ((↑) : ℤ→  (ZMod N)))
  have HI : ((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))  = 
    (![(a : ZMod N),(b : ZMod N)] : (Fin 2) → (ZMod N)) := by
   
   
   

    convert hi
    ext i
    fin_cases i
    simp [hf.1]
    


  constructor
  have HI0 : (((↑) : ℤ→  (ZMod N)) ∘ (Matrix.vecMul (f.1) (A⁻¹.1))) 0 = (a : ZMod N) := by 
    rw [HI]
    simp only [Matrix.cons_val_zero]
  simpa using HI0  
  

  stop
  simp [Matrix.vecMul_vecMul]
  simp_rw [Matrix.vecMul, Matrix.vecHead, Matrix.adjugate, Matrix.dotProduct] at *
  simp at *
  simp_rw [Matrix.vecHead,Matrix.vecTail,Matrix.adjugate,Matrix.transpose,Matrix.cramer,Matrix.cramerMap, hf.1, hf.2.1]
  simp


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


lemma summable_Eisenstein_N_tsum (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
  Summable (fun (x : (lvl_N_congr  N a b)) => (eise k z  x.1) ) := by 
  apply (Eisenstein_tsum_summable k z hk).subtype

def feise (k : ℤ) (z : ℍ) (v : (lvl_N_congr'  N a b)) : ℂ := (eise k z ((piFinTwoEquiv fun _ => ℤ) v.1))

/-- The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_N_tsum (k : ℤ) (N : ℕ) (a b : ℤ) : ℍ → ℂ := fun z => ∑' x : (lvl_N_congr'  N a b), 
  (feise k z  x)


lemma summable_Eisenstein_N_tsum' (k : ℕ) (hk : 3 ≤ k) (N : ℕ) (a b : ℤ) (z : ℍ): 
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
    MoebiusEquiv,MoebiusPerm]
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

theorem feise_Moebius (k : ℤ) (z : ℍ) (N : ℕ) (A : Gamma N) (i : (lvl_N_congr'  N a b)) :
    feise k (A • z) i =
      (A.1 1 0 * z.1 + A.1 1 1) ^ k * feise k z ((Gammainv_Equiv N a b A)  i) := by
    simp_rw [feise,UpperHalfPlane.specialLinearGroup_apply]
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

variables (k a b: ℤ) (A: SL(2,ℤ)) (N : ℤ) (z : ℍ)

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
  f (A • z)  * UpperHalfPlane.denom A z ^ (-k) := by
  rw [denom]
  simp

  sorry



lemma Eisenstein_lvl_N_Sl_inv (N : ℕ) (k a b : ℤ) (A : SL(2,ℤ)) : 
  (((Eisenstein_SIF_lvl_N N k a b).1)∣[k,A]) = 
    (((Eisenstein_SIF_lvl_N N k (Matrix.vecMul (![a,b]) A.1 0) (Matrix.vecMul (![a,b]) A.1 1)).1)) := by
 
  ext1 z
  have := slash_apply k A ((Eisenstein_SIF_lvl_N N k a b).1) z
  rw [this] 
  simp only [SlashInvariantForm.toFun_eq_coe]
  simp_rw [Eisenstein_SIF_lvl_N, Eisenstein_N_tsum]
  simp only [SlashInvariantForm.coe_mk]
  rw [Eisenstein_N_tsum]
  rw [Eisenstein_N_tsum]
  have := @feise_eq_one_div_denom N a b k (A • z) 
  

  simp_rw [feise, denom]
  simp only [piFinTwoEquiv_apply, Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply,
    ofReal_int_cast, uhc]


  

  
   
  sorry 

lemma UBOUND (N : ℕ) (k a b : ℤ) (z : ℍ) (A: SL(2, ℤ)): 
  Complex.abs ((((Eisenstein_SIF_lvl_N N k a b))) z) ≤ (AbsEisenstein_tsum k z) := by
  simp_rw [Eisenstein_SIF_lvl_N, AbsEisenstein_tsum, Eisenstein_N_tsum]
  simp
  apply le_trans (abs_tsum' ?_)
  sorry
  
 /-
  have hr := (Eisenstein_SIF ⊤ k).2 ⟨A, by tauto⟩
  simp only [SlashInvariantForm.toFun_eq_coe, ge_iff_le] at *
  have : Complex.abs (Eisenstein_SIF ⊤ k z) = Complex.abs ((((Eisenstein_SIF ⊤ k).1)∣[k,A]) z) := by
    congr
    apply symm
    rw [←hr]
    rfl
  rw [this]
-/
  sorry

/-

lemma denom_bound  (k : ℕ) (γ : SL(2,ℤ)) (z : ℍ') : 
  Complex.abs (1/(UpperHalfPlane.denom γ z)^(k)) ≤ (1/ ((γ.1 1 1 : ℝ) * rfunct (z : ℍ')) ^ k) := by
  simp_rw [denom]
  simp
  rw [inv_le_inv]
  norm_cast
  rw [←Complex.abs_pow]
  have H : rfunct (z : ℍ') ≤  Complex.abs ((γ.1 1 0) * z.1+ γ.1 1 1) := by
    sorry
  sorry
  sorry
  sorry



theorem AbsEisenstein_bound_unifomly_on_stip' (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) 
    (γ : SL(2,ℤ)) (z : upperHalfSpaceSlice A B) :
    Complex.abs ((UpperHalfPlane.denom γ z)^(-(k : ℤ)))*(AbsEisenstein_tsum k z.1) ≤ 
    (8 / ((γ.1 1 1)*rfunct (lbpoint A B hb)) ^ k) * Complex.abs (riemannZeta (k - 1)) := by
  have : 8 / rfunct (z : ℍ') ^ k * Complex.abs (riemannZeta (k - 1 )) ≤ 
    8 / rfunct (lbpoint A B hb) ^ k * Complex.abs (riemannZeta (k - 1)) := by
    apply rfunctbound;
  have h1 := ( AbsEisenstein_bound k (z : ℍ') h)  
  have hk11 : 1 < k := by linarith
  have H:= Int.ofNat_sub hk11.le
  have H2 : (((k-1) : ℕ) : ℂ) = k - 1 := by norm_cast
  rw [H2] at h1
  sorry
  --apply le_trans h1 this
-/

theorem lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T^N)^n)  • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k (Gamma N) f
  simp only [SlashInvariantForm.slash_action_eqn']
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h 
  have Hn :=  (T_pow_N_mem_Gamma' N n)
  simp only [zpow_coe_nat, Int.natAbs_ofNat] at Hn   
  have H:= h ((ModularGroup.T^N)^n) Hn z
  rw [H]
  have h0 : (((ModularGroup.T^N)^n) : GL (Fin 2) ℤ) 1 0 = 0  := by 
    rw [slcoe]
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by 
      rw [zpow_mul]
      simp
    rw [this]
    rw [ModularGroup.coe_T_zpow (N*n)]
    rfl
  have h1: (((ModularGroup.T^N)^n) : GL (Fin 2) ℤ) 1 1 = 1  := by 
    rw [slcoe]
    have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by 
      rw [zpow_mul]
      simp
    rw [this]
    rw [ModularGroup.coe_T_zpow (N*n)]
    rfl   
  rw [h0,h1]
  ring_nf
  simp

theorem Eisenstein_series_is_bounded (k a b: ℤ) (N : ℕ) (hk : 3 ≤ k) (A : SL(2, ℤ)) (hN : 0 < (N : ℤ)) :
    IsBoundedAtImInfty ( (Eisenstein_SIF_lvl_N N k a b).1∣[k,A]) :=
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

  apply le_trans (UBOUND N k _ _ ((ModularGroup.T ^ N) ^ n • z) A)
  let Z := ((ModularGroup.T ^ N) ^ n) • z
  have hZ : Z ∈ upperHalfSpaceSlice N 2 :=
    by
    sorry
  have hkk : 3 ≤ Int.natAbs k := by sorry  
  have := AbsEisenstein_bound_unifomly_on_stip (Int.natAbs k) hkk N 2 (by linarith) ⟨Z, hZ⟩
  sorry
  --convert this
  

  /-
  have := Eisenstein_is_bounded k hk 
  simp_rw [UpperHalfPlane.bounded_mem,Eisenstein_SIF_lvl_N] at *
  obtain ⟨M, B, H ⟩:= this
  use M 
  use B
  intro z hz
  apply le_trans (UBOUND N k a b z A)
  apply H z hz
  -/

  

  
 
