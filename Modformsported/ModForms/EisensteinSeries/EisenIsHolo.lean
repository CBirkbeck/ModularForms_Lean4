import Modformsported.ModForms.EisensteinSeries.EisensteinSeries 
import Modformsported.ForMathlib.UnformLimitsOfHolomorphic
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit 
  
universe u v w

open Complex UpperHalfPlane

open scoped BigOperators NNReal Classical Filter

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

local notation "SL2Z" => Matrix.SpecialLinearGroup (Fin 2) ℤ

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

noncomputable section

namespace EisensteinSeries

theorem eisenSquare_diff_on (k : ℤ) (hkn : k ≠ 0) (n : ℕ) :
    IsHolomorphicOn fun z : ℍ' => eisenSquare k n z :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  have h1 :
    (extendByZero fun z : ℍ' => eisenSquare k n z) = fun x : ℂ =>
      ∑ y in square n, (extendByZero fun z : ℍ' => eise k z y) x :=
    by
    simp_rw [eisenSquare]
    funext z
    simp only [extendByZero, Finset.sum_dite_irrel, Finset.sum_const_zero]
  simp only [Ne.def] at *
  rw [h1]
  apply DifferentiableOn.sum
  intro i _
  apply Eise'_has_diff_within_at k i hkn

def eisenSquare' (k : ℤ) (n : ℕ) : ℍ' → ℂ := fun z : ℍ' => ∑ x in Finset.range n, eisenSquare k x z

theorem eisenSquare'_diff_on (k : ℤ) (hkn : k ≠ 0) (n : ℕ) : IsHolomorphicOn (eisenSquare' k n) :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  have h1 :
    extendByZero (eisenSquare' k n) = fun x : ℂ =>
      ∑ y in Finset.range n, (extendByZero fun z : ℍ' => eisenSquare k y z) x :=
    by
    simp_rw [eisenSquare']
    simp only [extendByZero, Finset.sum_dite_irrel, Finset.sum_const_zero]
  rw [h1]
  apply DifferentiableOn.sum
  exact fun i _ => (isHolomorphicOn_iff_differentiableOn _ _).mpr (eisenSquare_diff_on k hkn i)

variable (A B : ℝ)

theorem Eisen_partial_tends_to_uniformly_on_ball (k : ℕ) (h : 3 ≤ k) (z : ℍ') :
    ∃ A B ε : ℝ,
      0 < ε ∧
        Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧
          0 < B ∧
            ε < B ∧
              TendstoUniformlyOn (eisenSquare' k) (eisensteinSeriesOfWeight_ k) Filter.atTop
                (Metric.closedBall z ε) :=
  by
  have h1 := closedBall_in_slice z
  obtain ⟨A, B, ε, hε, hB, hball, hA, hεB⟩ := h1
  use A
  use B
  use ε
  simp only [hε, hB, hball, hεB, true_and_iff]
  have hz : z ∈ upperHalfSpaceSlice A B := by apply hball; simp [hε.le]
  have hu := Eisen_partial_tends_to_uniformly k h A B hA hB
  have hu2 :
    TendstoUniformlyOn (eisenParSumSlice k A B) (eisensteinSeriesRestrict k A B) Filter.atTop
      (Metric.closedBall ⟨z, hz⟩ ε) :=
    by apply hu.tendstoUniformlyOn
  clear hu
  simp_rw [eisensteinSeriesRestrict] at *
  simp_rw [Metric.tendstoUniformlyOn_iff] at *
  simp_rw [eisenParSumSlice] at *
  simp_rw [eisenSquareSlice] at *
  simp_rw [eisenSquare']
  simp  [Filter.eventually_atTop, gt_iff_lt, ge_iff_le, instNonempty,
    Metric.mem_closedBall, Subtype.forall, SetCoe.forall, UpperHalfPlane.coe_im, Subtype.coe_mk,
      UpperHalfPlane.coe_re] at *
  intro δ hδ
  have hu3 := hu2 δ hδ
  clear hu2
  obtain ⟨a, ha⟩ := hu3
  use a
  intro b hb x hx hxx
  have ha2 := ha b hb x ?_
  apply ha2
  exact hxx
  apply hball
  simp only [hxx, Metric.mem_closedBall]


theorem Eisen_partial_tends_to_uniformly_on_ball' (k : ℕ) (h : 3 ≤ k) (z : ℍ') :
    ∃ A B ε : ℝ,
      0 < ε ∧
        Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧
          0 < B ∧
            ε < B ∧
              TendstoUniformlyOn (fun n => extendByZero (eisenSquare' k n))
                (extendByZero (eisensteinSeriesOfWeight_ k)) Filter.atTop (Metric.closedBall z ε) :=
  by
  have H := Eisen_partial_tends_to_uniformly_on_ball k h z
  obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ := H
  use A
  use B
  use ε
  simp only [hε, hball, hB, hεB, true_and_iff]
  simp_rw [Metric.tendstoUniformlyOn_iff] at *
  intro ε' hε'
  have h2 := hunif ε' hε'
  simp only [Filter.eventually_atTop, gt_iff_lt, ge_iff_le, Metric.mem_closedBall] at *
  obtain ⟨a, ha⟩ := h2
  use a
  have Hba := ball_in_upper_half z A B ε hε hεB hball
  intro b hb x hx
  have hxx : x ∈ ℍ'.1 := by apply Hba; simp [hx]
  have hf := ext_by_zero_apply ℍ' (eisensteinSeriesOfWeight_ k) ⟨x, hxx⟩
  let F : ℕ → ℍ' → ℂ := fun n => eisenSquare' k n
  have hFb := ext_by_zero_apply ℍ' (F b) ⟨x, hxx⟩
  simp  at *
  rw [hf]
  rw [hFb]
  apply ha b hb x hxx hx


/-
lemma eisenSquare_tendstolocunif (k : ℕ) (h : 3 ≤ k):
  TendstoLocallyUniformly (eisenSquare' k) (eisensteinSeriesOfWeight_ k) Filter.atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intros ε hε z 
  have := Eisen_partial_tends_to_uniformly_on_ball k h z
  obtain ⟨A, B, e,he, hee, hB, heB, H⟩ := this
  rw [Metric.tendstoUniformlyOn_iff] at H 
  sorry 


lemma eisenSquare_tendstolocunif' (k : ℕ) (h : 3 ≤ k):
  TendstoLocallyUniformlyOn (fun (n: ℕ) => (eisenSquare' k n) ∘ ⇑(chartAt ℂ z).symm) 
  ((eisensteinSeriesOfWeight_ k) ∘ ⇑(chartAt ℂ z).symm) Filter.atTop ℍ' := by
  have H := eisenSquare_tendstolocunif k h
  have HH := tendstoLocallyUniformlyOn_univ.2 H
  sorry
  
  

lemma eisenSquare_tendstolocunif'' (k : ℕ) (h : 3 ≤ k):
  TendstoLocallyUniformlyOn (fun (n: ℕ) => extendByZero (eisenSquare' k n))
  (extendByZero (eisensteinSeriesOfWeight_ k)) Filter.atTop UpperHalfPlane.upperHalfSpace := by
  have H := eisenSquare_tendstolocunif k h
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  rw [Metric.tendstoLocallyUniformly_iff] at H
  simp at *
  intros ε hε x hx
  have H2 := H ε hε x hx
  obtain ⟨t, ht, H3⟩:= H2
  use t 
  sorry
-/

  

/-- The extension of a function from `ℍ` to `ℍ'`-/
def holExtn (f : ℍ → ℂ) : ℍ' → ℂ := fun z : ℍ' => f (z : ℍ)

local notation "↑ₕ" => holExtn

instance : Coe (ℍ → ℂ) (ℍ' → ℂ) :=
  ⟨fun f => holExtn f⟩

  
/-
open scoped Manifold

lemma tsum_circ {ι : Type} (f : ι → ℍ → ℂ) : 
  (fun (z : ℍ) => ∑' (i : ι), f i z) ∘ ⇑(chartAt ℂ z).symm = 
    ∑' (i : ι), (f i  ∘ ⇑(chartAt ℂ z).symm) := by
  ext1
  simp only [OpenEmbedding.toLocalHomeomorph_source, LocalHomeomorph.singletonChartedSpace_chartAt_eq,
    Function.comp_apply]
  norm_cast
  sorry



theorem Eisenstein_is_mdiff (k : ℕ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinSeriesOfWeight_ k) :=
  by
  rw [mdiff_iff_diffOn]
  simp_rw [eisensteinSeriesOfWeight_ ]
  have H:=eisenSquare_tendstolocunif'' k h
  have HH :=H.differentiableOn ?_ ?_
  apply HH.congr
  intros x hx
  have := ext_chart (eisensteinSeriesOfWeight_ k) ⟨x, hx⟩
  rw [this]
  simp_rw [eisensteinSeriesOfWeight_ ]
  rfl
  sorry

  -/

  

theorem Eisenstein_is_holomorphic' (k : ℕ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (eisensteinSeriesOfWeight_ k)) :=
  by
  rw [← isHolomorphicOn_iff_differentiableOn]
  apply diff_on_diff
  intro x
  have H := Eisen_partial_tends_to_uniformly_on_ball' k hk x
  obtain ⟨A, B, ε, hε, hball, _, hεB, hunif⟩ := H
  use ε
  have hball2 : Metric.closedBall (↑x) ε ⊆ ℍ'.1 := by
    apply ball_in_upper_half x A B ε  hε hεB hball
  constructor
  apply hε
  constructor
  intro w hw
  have hwa : w ∈ ℍ'.1 := by apply hball2; simp; simp at hw ; apply le_trans hw.le; field_simp
  apply hwa
  have hkn : (k : ℤ) ≠ 0 := by norm_cast; linarith
  let F : ℕ → ℂ → ℂ := fun n => extendByZero (eisenSquare' k n)
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (Metric.closedBall x ε) :=
    by
    intro n
    have := eisenSquare'_diff_on k hkn n
    rw [← isHolomorphicOn_iff_differentiableOn] at this 
    apply this.mono
    apply hball2
  rw [←tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact] at hunif
  have mbb : Metric.ball x.1 ε ⊆  Metric.closedBall (x) ε := by exact Metric.ball_subset_closedBall
  have :=TendstoLocallyUniformlyOn.mono hunif mbb
  have := this.differentiableOn ?_ ?_
  apply this
  apply Filter.eventually_of_forall
  apply (fun n : ℕ => (hdiff n).mono mbb)
  exact Metric.isOpen_ball
  exact isCompact_closedBall (x.1) ε
  

theorem Eisenstein_is_holomorphic (k : ℤ) (hk : 3 ≤ k) :
    IsHolomorphicOn (↑ₕ (eisensteinSeriesOfWeight_ k)) :=
  by
  have : ∃ n : ℕ, (n : ℤ) = k :=
    haveI hk' : 0 ≤ k := by linarith
    CanLift.prf k hk'
  obtain ⟨n, hn⟩ := this
  have hn3 : 3 ≤ n := by linarith
  have := Eisenstein_is_holomorphic' n hn3
  convert this
  apply hn.symm

/-
def myVadd : ℤ → ℍ → ℍ := fun n => fun z : ℍ => ⟨z.1 + n, by simp; apply z.2⟩

instance : VAdd ℤ ℍ where vadd := myVadd

theorem my_add_im (n : ℤ) (z : ℍ) : (myVadd n z).im = z.im :=
  by
  simp_rw [myVadd]
  have : (z.1+n).im = z.1.im := by simp only [add_im, int_cast_im, add_zero]
  simp_rw [UpperHalfPlane.im]
  convert this

  

theorem my_add_re (n : ℤ) (z : ℍ) : (myVadd n z).re = z.re + n :=
  by
  simp_rw [myVadd]
  simp_rw [UpperHalfPlane.re]
  simp only [int_cast_re, add_re, Subtype.coe_mk]
  exact rfl

theorem zero_vadd' (z : ℍ) : myVadd (0 : ℤ) z = z :=
  by
  simp_rw [myVadd]
  simp  [add_zero, Int.cast_zero, Subtype.coe_eta]

theorem add_vadd' (n m : ℤ) (z : ℍ) : myVadd (n + m) z = myVadd n (myVadd m z) :=
  by
  simp_rw [myVadd]
  simp only [Int.cast_add]
  abel_nf

instance : AddAction ℤ ℍ where
  zero_vadd := by apply zero_vadd'
  add_vadd := by apply add_vadd'

def tn (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![1, n], ![0, 1]]

theorem Tndet (n : ℤ) : Matrix.det (tn n) = 1 :=
  by
  simp_rw [tn]
  rw [Matrix.det_fin_two]
  simp only [Matrix.head_cons, mul_one, sub_zero, Matrix.cons_val_one, MulZeroClass.mul_zero,
    Matrix.cons_val_zero]

/-
theorem coe_aux (γ : SL2Z) : ∀ i j, ((γ : Matrix.GLPos (Fin 2) ℝ) i j : ℝ) = ((γ i j : ℤ) : ℝ) :=
  by
  intro i j
  have := ModularGroup.mat_vals γ i j
  simp [Matrix.GeneralLinearGroup.coeFn_eq_coe, coe_coe] at *
  rw [← this]
  cases j; cases i; cases γ; dsimp at *; solve_by_elim

-/

def tN (n : ℤ) : SL2Z :=
  ⟨tn n, Tndet n⟩

theorem TN00 (n : ℤ) : (tN n) 0 0 = 1 := by rfl

theorem TN01 (n : ℤ) : (tN n) 0 1 = n := by rfl

theorem TN10 (n : ℤ) : (tN n) 1 0 = 0 := by rfl

theorem TN11 (n : ℤ) : (tN n) 1 1 = 1 := by rfl
-/
open scoped ModularGroup

lemma slcoe (M : SL(2, ℤ)) : (M : GL (Fin 2) ℤ) i j = M i j  := by
  rfl
    


theorem mod_form_periodic (k : ℤ) (f : SlashInvariantForm (⊤ : Subgroup SL2Z) k) :
    ∀ (z : ℍ) (n : ℤ), f ((ModularGroup.T^n)  • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k ⊤ f
  simp only [SlashInvariantForm.slash_action_eqn']
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h 
  have H:= h (ModularGroup.T^n) z
  rw [H]
  have h0 : ((ModularGroup.T^n) : GL (Fin 2) ℤ) 1 0 = 0  := by 
    rw [slcoe]
    rw [ModularGroup.coe_T_zpow n]
    rfl
  have h1: ((ModularGroup.T^n) : GL (Fin 2) ℤ) 1 1 = 1  := by 
    rw [slcoe]
    rw [ModularGroup.coe_T_zpow n]
    rfl    
  rw [h0,h1]
  ring_nf
  simp



theorem abs_floor_sub (r : ℝ) : |r - Int.floor r| < 1 :=
  by
  simp only [Int.self_sub_floor]
  rw [_root_.abs_of_nonneg (Int.fract_nonneg r)]
  apply Int.fract_lt_one r

theorem upp_half_translation (z : ℍ) :
    ∃ n : ℤ, ((ModularGroup.T^n)) • z ∈ upperHalfSpaceSlice 1 z.1.2 :=
  by
  let n := Int.floor z.1.1
  use-n
  have := modular_T_zpow_smul z (-n)
  simp_rw [this]
  simp  [ge_iff_le, slice_mem, UpperHalfPlane.coe_im, 
    UpperHalfPlane.coe_re]
  constructor
  have : (-(n : ℝ) +ᵥ z).1.re= -Int.floor z.1.1 + z.re := by rfl
  norm_cast at *
  rw [this]
  simp
  rw [add_comm]
  apply (abs_floor_sub z.1.1).le
  have : (-(n : ℝ) +ᵥ z).1.im = z.im := by 
    have := vadd_im (-(n : ℝ)) z
    rw [← this]
    congr
  rw [this]
  apply le_abs_self

theorem eis_bound_by_real_eis (k : ℕ) (z : ℍ) (hk : 3 ≤ k) :
    Complex.abs (eisensteinSeriesOfWeight_ k z) ≤ realEisensteinSeriesOfWeight_ k z :=
  by
  simp_rw [eisensteinSeriesOfWeight_]
  simp_rw [realEisensteinSeriesOfWeight_]
  simp_rw [realEise]
  simp_rw [eise]
  apply abs_tsum'
  have := real_eise_is_summable k z hk
  simp_rw [realEise] at this 
  simp only [one_div, Complex.abs_pow, abs_inv, norm_eq_abs, zpow_ofNat] at *
  apply this

theorem Eisenstein_is_bounded' (k : ℕ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty ((eisensteinIsSlashInv ⊤ k)) :=
  by
  simp only [UpperHalfPlane.bounded_mem, Subtype.forall, UpperHalfPlane.coe_im]
  let M : ℝ := 8 / rfunct (lbpoint 1 2 <| by linarith) ^ k * rZ (k - 1)
  use M, 2
  intro z hz
  obtain ⟨n, hn⟩ := upp_half_translation z
  have := mod_form_periodic k (eisensteinIsSlashInv ⊤ k) z n
  rw [← this]
  let Z := (ModularGroup.T^n) • z
  apply le_trans (eis_bound_by_real_eis k Z hk)
  have hZ : Z ∈ upperHalfSpaceSlice 1 2 :=
    by
    simp only [map_zpow, slice_mem, abs_ofReal, ge_iff_le] at hn ⊢
    refine' ⟨hn.1, _⟩
    apply le_trans hz
    rw [modular_T_zpow_smul]
    have : ((n : ℝ) +ᵥ z).1.im = z.im := by 
      have := vadd_im ((n : ℝ)) z
      rw [← this]
      congr
    rw [this]
    apply le_abs_self
  convert Real_Eisenstein_bound_unifomly_on_stip k hk 1 2 (by linarith) ⟨Z, hZ⟩


theorem Eisenstein_is_bounded (k : ℤ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty ((eisensteinIsSlashInv ⊤ k)) :=
  by
  have : ∃ n : ℕ, (n : ℤ) = k :=
    haveI hk' : 0 ≤ k := by linarith
    CanLift.prf k hk'
  obtain ⟨n, hn⟩ := this
  have hn3 : 3 ≤ n := by linarith
  have := Eisenstein_is_bounded' n hn3
  convert this
  apply hn.symm
  apply hn.symm
  apply hn.symm


example (k : ℤ) (hk : 0 ≤ k) : ∃ n : ℕ, (n : ℤ) = k :=
  CanLift.prf k hk

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

open scoped Manifold

theorem Eisenstein_series_is_mdiff (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (↑ₕ (eisensteinIsSlashInv ⊤ ↑k)) :=
  by
  have := Eisenstein_is_holomorphic k hk
  have h2 := (mdiff_iff_holo (↑ₕ (eisensteinIsSlashInv ⊤ k).toFun)).2 this
  convert h2

theorem Eisenstein_series_is_bounded (k : ℤ) (hk : 3 ≤ k) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty ( (eisensteinIsSlashInv ⊤ k)∣[k,A]) :=
  by
  simp_rw [(eisensteinIsSlashInv ⊤ k).2]
  have := Eisenstein_is_bounded k hk
  convert this
  have hr := (eisensteinIsSlashInv ⊤ k).2 ⟨A, by tauto⟩
  convert hr

def eisensteinSeriesIsModularForm (k : ℤ) (hk : 3 ≤ k) : ModularForm ⊤ k
    where
  toFun := (eisensteinIsSlashInv ⊤ k)
  slash_action_eq' := by convert (eisensteinIsSlashInv ⊤ k).2
  holo' := Eisenstein_series_is_mdiff k hk
  bdd_at_infty' A :=  Eisenstein_series_is_bounded k hk A
  

end EisensteinSeries

