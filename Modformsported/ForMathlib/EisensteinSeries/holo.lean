import Modformsported.ForMathlib.EisensteinSeries.boundingfunctions
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.LocallyUniformLimit
import LeanCopilot

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

namespace EisensteinSeries

local notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

theorem complex_denom_HasDerivAt(a : Fin 2 → ℤ) (k : ℤ) (z : ℂ) (h : (a 0 : ℂ) * z + a 1 ≠ 0) :
    HasDerivAt (fun z : ℂ => (a 0 * z + a 1) ^ k) (k * (a 0 * z + a 1) ^ (k - 1) * a 0) z := by
  rw [← Function.comp_def (fun x : ℂ => x ^ k) ((a 0) * · + (a 1))]
  apply HasDerivAt.comp
  · exact hasDerivAt_zpow k ((a 0 ) * z + a 1 ) (Or.inl h)
  · simpa using (hasDerivAt_id' z).const_mul (a 0 : ℂ) |>.add_const _

lemma comp_eq_const_iff {α β γ: Type*} (b : β) (f : α → β) (g : β → γ)
    (hg : Injective g) : g ∘ f = Function.const _ (g b) ↔ f = Function.const _ b :=
  hg.comp_left.eq_iff' rfl

lemma comp_eq_zero_iff {α β γ: Type*} [OfNat β 0] [ OfNat γ 0] (f : α → β) (g : β → γ)
    (hg : Injective g) (hg0 : g 0 = 0) : g ∘ f = 0 ↔ f = 0 := by
  convert (comp_eq_const_iff 0 f g hg)
  simp only [hg0, Pi.const_zero]

lemma comp_inj_ne_zero {α β γ: Type*} [OfNat β 0] [ OfNat γ 0] (f : α → β) (g : β → γ)
    (hg : Injective g) (hg0 : g 0 = 0) : (g ∘ f) ≠ 0 ↔ f ≠ 0 :=
  (Iff.ne (comp_eq_zero_iff f g hg hg0))

variable (k : ℤ) (a : Fin 2 → ℤ)

lemma UpperHalfPlane.coe_linear_ne_zero (a : Fin 2 → ℤ) (x : UpperHalfPlane.coe '' ⊤) (ha : a ≠ 0) :
    ((a 0 : ℂ) * x + a 1) ≠ 0 := by
  have hx := x.2
  simp only [ne_eq, top_eq_univ, image_univ, mem_range] at *
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  apply UpperHalfPlane.linear_ne_zero ((Int.cast (R := ℝ)) ∘ a) y
      ((comp_inj_ne_zero _ _ Int.cast_injective Int.cast_zero).mpr ha)

lemma complex_eisSummand_differentiableOn (hk : k ≠ 0) :
  DifferentiableOn ℂ (fun z : ℂ => 1/(a 0 * z + a 1) ^ k) (UpperHalfPlane.coe '' ⊤) := by
  by_cases ha : a ≠ 0
  · apply DifferentiableOn.div (differentiableOn_const 1)
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
      (complex_denom_HasDerivAt a k z ?_).differentiableAt
    apply UpperHalfPlane.coe_linear_ne_zero a ⟨z, hz⟩ ha
    intro z hz
    apply zpow_ne_zero k (UpperHalfPlane.coe_linear_ne_zero a ⟨z, hz⟩ ha)
  · simp only [ne_eq, not_not] at ha
    rw [ha]
    have : ((0 : ℂ) ^ k)⁻¹ = 0 := by
      simp only [inv_eq_zero]
      rw [zpow_eq_zero_iff hk]
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, one_div, this, uhc, top_eq_univ,
      image_univ]
    exact differentiableOn_const 0

lemma eisSummad_complex_extension_differentiableOn (hk : k ≠ 0) :
  DifferentiableOn ℂ (↑ₕ(eisSummand k a)) (UpperHalfPlane.coe '' ⊤) := by
  apply DifferentiableOn.congr (complex_eisSummand_differentiableOn k a hk)
  intro z hz
  simp only [eisSummand, one_div, comp_apply, inv_inj]
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp only [ne_eq, top_eq_univ, image_univ, mem_range, PartialHomeomorph.symm_symm,
    OpenEmbedding.toPartialHomeomorph_apply, UpperHalfPlane.coe] at *
  rw [this]

/- A version for the extension to maps `ℂ → ℂ` that is nice to have for holomorphicity later -/
lemma  eisensteinSeries_TendstoLocallyUniformlyOn3 {k : ℤ} (hk : 3 ≤ k) (N : ℕ)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ((eisensteinSeries_SIF a k).toFun ))
          Filter.atTop (UpperHalfPlane.coe '' ⊤) := by
  apply TendstoLocallyUniformlyOn.comp (s := ⊤)
  simp only [SlashInvariantForm.toFun_eq_coe, Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
  apply eisensteinSeries_TendstoLocallyUniformlyOn k hk
  simp only [Set.top_eq_univ, image_univ, mapsTo_range_iff, Set.mem_univ, forall_const]
  apply PartialHomeomorph.continuousOn_symm

lemma eisensteinSeries_SIF_complex_differentiableOn {N : ℕ} (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    DifferentiableOn ℂ (↑ₕ((eisensteinSeries_SIF a k).toFun )) (UpperHalfPlane.coe '' ⊤) := by
  convert @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a))) _ _ _
    (UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a )) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ((eisensteinSeries_SIF a k).toFun ))
        (by apply atTop_neBot) (eisensteinSeries_TendstoLocallyUniformlyOn3 hk N a)
          ((eventually_of_forall fun s => ?_)) ?_
  · apply DifferentiableOn.sum
    intro v _
    apply eisSummad_complex_extension_differentiableOn
    linarith
  · rw [← OpenEmbedding.open_iff_image_open]
    simp only [top_eq_univ, isOpen_univ]
    exact openEmbedding_coe

theorem eisensteinSeries_SIF_Mdifferentiable {N : ℕ} (a: Fin 2 → ZMod N) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinSeries_SIF a k).toFun := by
  simp only [MDifferentiable, MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  intro z
  have ha : UpperHalfPlane.coe '' ⊤ ∈ 𝓝 ↑z := by
    apply IsOpen.mem_nhds
    rw [← OpenEmbedding.open_iff_image_open]
    · simp only [top_eq_univ, isOpen_univ]
    · exact openEmbedding_coe
    · simp only [top_eq_univ, image_univ, mem_range, exists_apply_eq_apply]
  constructor
  rw [PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
    (e := (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph
    UpperHalfPlane.coe openEmbedding_coe)))]
  apply ContinuousOn.continuousAt
    ((eisensteinSeries_SIF_complex_differentiableOn k a hk).continuousOn)
      (s := (UpperHalfPlane.coe '' ⊤)) (x := z) ha
  · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
    OpenEmbedding.toPartialHomeomorph_source, mem_univ]
  · apply DifferentiableOn.differentiableAt (s := UpperHalfPlane.coe '' ⊤) _ ha
    apply eisensteinSeries_SIF_complex_differentiableOn k a hk
