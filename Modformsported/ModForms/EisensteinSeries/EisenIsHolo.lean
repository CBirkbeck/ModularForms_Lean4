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


lemma eisenSquare_tendstolocunif (k : ℕ) (h : 3 ≤ k):
  TendstoLocallyUniformly (eisenSquare' k) (eisensteinSeriesOfWeight_ k) Filter.atTop := by
   
 


/-- The extension of a function from `ℍ` to `ℍ'`-/
def holExtn (f : ℍ → ℂ) : ℍ' → ℂ := fun z : ℍ' => f (z : ℍ)

local notation "↑ₕ" => holExtn

instance : Coe (ℍ → ℂ) (ℍ' → ℂ) :=
  ⟨fun f => holExtn f⟩

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
  

  stop


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
  apply
    uniform_of_diff_circle_int_is_diff F (extendByZero (eisensteinSeriesOfWeight_ k)) x hε hdiff
      hunif

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

def myVadd : ℤ → ℍ → ℍ := fun n => fun z : ℍ => ⟨z.1 + n, by simp; apply z.2⟩

instance : VAdd ℤ ℍ where vadd := myVadd

theorem my_add_im (n : ℤ) (z : ℍ) : (myVadd n z).im = z.im :=
  by
  simp_rw [my_vadd]
  simp only [Subtype.val_eq_coe]
  simp_rw [UpperHalfPlane.im]
  simp only [add_zero, int_cast_im, add_im, Subtype.coe_mk]

theorem my_add_re (n : ℤ) (z : ℍ) : (myVadd n z).re = z.re + n :=
  by
  simp_rw [my_vadd]
  simp only [Subtype.val_eq_coe]
  simp_rw [UpperHalfPlane.re]
  simp only [int_cast_re, add_re, Subtype.coe_mk]

theorem zero_vadd' (z : ℍ) : myVadd (0 : ℤ) z = z :=
  by
  simp_rw [my_vadd]
  simp only [add_zero, Int.cast_zero, Subtype.coe_eta, Subtype.val_eq_coe]

theorem add_vadd' (n m : ℤ) (z : ℍ) : myVadd (n + m) z = myVadd n (myVadd m z) :=
  by
  simp_rw [my_vadd]
  simp only [Int.cast_add, Subtype.val_eq_coe]
  abel

instance : AddAction ℤ ℍ where
  zero_vadd := by apply zero_vadd'
  add_vadd := by apply add_vadd'

def tn (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![1, n], ![0, 1]]

theorem Tndet (n : ℤ) : Matrix.det (tn n) = 1 :=
  by
  simp_rw [Tn]
  rw [Matrix.det_fin_two]
  simp only [Matrix.head_cons, mul_one, sub_zero, Matrix.cons_val_one, MulZeroClass.mul_zero,
    Matrix.cons_val_zero]

theorem coe_aux (γ : SL2Z) : ∀ i j, ((γ : Matrix.GLPos (Fin 2) ℝ) i j : ℝ) = ((γ i j : ℤ) : ℝ) :=
  by
  intro i j
  have := ModularGroup.mat_vals γ i j
  simp [of_real_int_cast, Subtype.val_eq_coe, Matrix.GeneralLinearGroup.coeFn_eq_coe, coe_coe] at *
  rw [← this]
  cases j; cases i; cases γ; dsimp at *; solve_by_elim

def tN (n : ℤ) : SL2Z :=
  ⟨tn n, Tndet n⟩

theorem TN00 (n : ℤ) : (tN n) 0 0 = 1 := by rfl

theorem TN01 (n : ℤ) : (tN n) 0 1 = n := by rfl

theorem TN10 (n : ℤ) : (tN n) 1 0 = 0 := by rfl

theorem TN11 (n : ℤ) : (tN n) 1 1 = 1 := by rfl

theorem mod_form_periodic (k : ℤ) (f : SlashInvariantForm (⊤ : Subgroup SL2Z) k) :
    ∀ (z : ℍ) (n : ℤ), f ((tN n : Matrix.GLPos (Fin 2) ℝ) • z) = f z :=
  by
  have h := SlashInvariantForm.slash_action_eqn' k ⊤ f
  simp only [SlashInvariantForm.slash_action_eqn', coe_coe]
  intro z n
  have htop : TN n ∈ (⊤ : Subgroup SL2Z) := by simp
  have H := h ⟨TN n, htop⟩ z
  simp only [Subgroup.coe_mk] at H 
  have hoo' : (TN n) 1 0 = 0 := by rfl
  have h11' : (TN n) 1 1 = 1 := by rfl
  simp at *
  simp_rw [hoo'] at H 
  simp_rw [h11'] at H 
  simp [Int.cast_zero, one_mul, MulZeroClass.zero_mul, Int.cast_one, zero_add, one_zpow] at H 
  apply H

theorem smul_expl (n : ℤ) (z : ℍ) : (tN n : Matrix.GLPos (Fin 2) ℝ) • z = n +ᵥ z :=
  by
  simp [coe_coe]
  have := UpperHalfPlane.coe_smul (TN n : Matrix.GLPos (Fin 2) ℝ) z
  have h1 := TN00 n
  have h2 := TN01 n
  have h3 := TN10 n
  have h4 := TN11 n
  ext
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, eq_self_iff_true, coe_coe,
    UpperHalfPlane.coe_smul, UpperHalfPlane.coe_re] at *
  simp_rw [h1, h2, h3, h4]
  simp [int_cast_re, one_mul, of_real_zero, MulZeroClass.zero_mul, add_re, of_real_int_cast,
    zero_add, of_real_one, div_one, UpperHalfPlane.coe_re]
  convert (my_add_re n z).symm
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, eq_self_iff_true, UpperHalfPlane.coe_im, coe_coe,
    UpperHalfPlane.coe_smul] at *
  simp_rw [h1, h2, h3, h4]
  simp [add_zero, one_mul, of_real_zero, int_cast_im, MulZeroClass.zero_mul, add_im,
    of_real_int_cast, zero_add, UpperHalfPlane.coe_im, of_real_one, div_one]
  convert (my_add_im n z).symm

theorem abs_floor_sub (r : ℝ) : |r - Int.floor r| < 1 :=
  by
  simp only [Int.self_sub_floor]
  rw [_root_.abs_of_nonneg (Int.fract_nonneg r)]
  apply Int.fract_lt_one r

theorem upp_half_translation (z : ℍ) :
    ∃ n : ℤ, (tN n : Matrix.GLPos (Fin 2) ℝ) • z ∈ upperHalfSpaceSlice 1 z.1.2 :=
  by
  let n := Int.floor z.1.1
  use-n
  have := smul_expl (-n) z
  simp_rw [this]
  simp only [abs_of_real, ge_iff_le, slice_mem, UpperHalfPlane.coe_im, Subtype.val_eq_coe,
    UpperHalfPlane.coe_re]
  have him := my_add_im (-n) z
  have hre := my_add_re (-n) z
  constructor
  have h1 : (-n +ᵥ z).re = (my_vadd (-n) z).re := by rfl
  rw [h1]
  rw [hre]
  simp
  apply (abs_floor_sub z.1.1).le
  have h2 : (-n +ᵥ z).im = (my_vadd (-n) z).im := by rfl
  rw [h2]
  rw [him]
  apply le_abs_self

theorem eis_bound_by_real_eis (k : ℕ) (z : ℍ) (hk : 3 ≤ k) :
    Complex.abs (eisensteinSeriesOfWeight_ k z) ≤ realEisensteinSeriesOfWeight_ k z :=
  by
  simp_rw [Eisenstein_series_of_weight_]
  simp_rw [real_Eisenstein_series_of_weight_]
  simp_rw [real_Eise]
  simp_rw [Eise]
  apply abs_tsum'
  have := real_eise_is_summable k z hk
  simp_rw [real_Eise] at this 
  simp only [one_div, Complex.abs_pow, abs_inv, norm_eq_abs, zpow_ofNat] at *
  apply this

theorem Eisenstein_is_bounded' (k : ℕ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty (eisensteinSeriesOfWeight_ k) :=
  by
  simp only [UpperHalfPlane.bounded_mem, Subtype.forall, UpperHalfPlane.coe_im]
  let M : ℝ := 8 / rfunct (lbpoint 1 2 <| by linarith) ^ k * rZ (k - 1)
  use M, 2
  intro z hz
  obtain ⟨n, hn⟩ := upp_half_translation z
  have := mod_form_periodic k (Eisenstein_is_slash_inv ⊤ k) z n
  have hf : (Eisenstein_is_slash_inv ⊤ k) z = Eisenstein_series_of_weight_ k z := by rfl
  rw [hf] at this 
  rw [← this]
  let Z := (TN n : Matrix.GLPos (Fin 2) ℝ) • z
  apply le_trans (eis_bound_by_real_eis k Z hk)
  have hZ : Z ∈ upper_half_space_slice 1 2 :=
    by
    simp_rw [Z, smul_expl n z] at *
    simp only [abs_of_real, slice_mem, UpperHalfPlane.coe_im, Subtype.val_eq_coe,
      UpperHalfPlane.coe_re] at hn ⊢
    refine' ⟨hn.1, _⟩
    have hadd : (n +ᵥ z).im = (my_vadd n z).im := by rfl
    rw [hadd, my_add_im n z]
    apply le_trans hz
    apply le_abs_self
  convert Real_Eisenstein_bound_unifomly_on_stip k hk 1 2 (by linarith) ⟨Z, hZ⟩

theorem Eisenstein_is_bounded (k : ℤ) (hk : 3 ≤ k) :
    UpperHalfPlane.IsBoundedAtImInfty (eisensteinSeriesOfWeight_ k) :=
  by
  have : ∃ n : ℕ, (n : ℤ) = k :=
    haveI hk' : 0 ≤ k := by linarith
    CanLift.prf k hk'
  obtain ⟨n, hn⟩ := this
  have hn3 : 3 ≤ n := by linarith
  have := Eisenstein_is_bounded' n hn3
  convert this
  apply hn.symm


example (k : ℤ) (hk : 0 ≤ k) : ∃ n : ℕ, (n : ℤ) = k :=
  CanLift.prf k hk

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

theorem Eisenstein_series_is_mdiff (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (↑ₕ (eisensteinIsSlashInv ⊤ ↑k)) :=
  by
  have := Eisenstein_is_holomorphic k hk
  have h2 := (mdiff_iff_holo (↑ₕ (Eisenstein_is_slash_inv ⊤ k).toFun)).2 this
  convert h2

theorem Eisenstein_series_is_bounded (k : ℤ) (hk : 3 ≤ k) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty (↑ₕ (eisensteinIsSlashInv ⊤ k)∣[k,A]) :=
  by
  rw [hol_extn]
  simp_rw [(Eisenstein_is_slash_inv ⊤ k).2]
  have := Eisenstein_is_bounded k hk
  convert this
  have hr := (Eisenstein_is_slash_inv ⊤ k).2 ⟨A, by tauto⟩
  have hr2 : (Eisenstein_is_slash_inv ⊤ k).toFun = Eisenstein_series_of_weight_ k := by rfl
  rw [hr2] at hr 
  convert hr

def eisensteinSeriesIsModularForm (k : ℤ) (hk : 3 ≤ k) : ModularForm ⊤ k
    where
  toFun := ↑ₕ (eisensteinIsSlashInv ⊤ k)
  slash_action_eq' := by convert (Eisenstein_is_slash_inv ⊤ k).2
  holo' := Eisenstein_series_is_mdiff k hk
  bdd_at_infty' A := Eisenstein_series_is_bounded k hk A

end EisensteinSeries

