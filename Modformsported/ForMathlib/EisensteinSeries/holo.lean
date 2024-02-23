import Modformsported.ForMathlib.EisensteinSeries.boundingfunctions
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex   Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


namespace EisensteinSeries

theorem complex_eisSummand_HasDerivAt(a : Fin 2 → ℤ) (k : ℤ) (z : ℂ) (h : (a 0 : ℂ) * z + a 1 ≠ 0) :
    HasDerivAt (fun z : ℂ => (a 0 * z + a 1) ^ k) (k * (a 0 * z + a 1) ^ (k - 1) * a 0) z := by
  rw [← Function.comp_def (fun x : ℂ => x ^ k) ((a 0) * · + (a 1))]
  apply HasDerivAt.comp
  · exact hasDerivAt_zpow k ((a 0 ) * z + a 1 ) (Or.inl h)
  · simpa using (hasDerivAt_id' z).const_mul (a 0 : ℂ) |>.add_const _

lemma fun_ne_zero_cases {G : Type*} [OfNat G 0] (x : Fin 2 → G) : x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  rw [Function.ne_iff]; exact Fin.exists_fin_two

lemma complex_eisSummand_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) (hk : k ≠ 0) :
  DifferentiableOn ℂ (fun z : ℂ => 1/(a 0 * z + a 1) ^ k) (UpperHalfPlane.coe '' ⊤) := by
  by_cases ha : a ≠ 0
  apply DifferentiableOn.div
  exact differentiableOn_const 1
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply (complex_eisSummand_HasDerivAt a k z ?_).differentiableAt
  have := UpperHalfPlane.linear_ne_zero ![a 0, a 1]
  have hz:= z.2
  simp only [Int.cast_eq_zero, Matrix.zero_empty, and_true, not_and,
    Matrix.cons_val_zero, ofReal_int_cast, uhc, Matrix.cons_val_one, Matrix.head_cons, top_eq_univ,
    image_univ, mem_range] at *
  obtain ⟨y, hy⟩ := hz
  have := this y
  rw [hy] at this
  apply this
  rw [fun_ne_zero_cases] at *
  simp [ha] at *
  simp
  intro z
  apply zpow_ne_zero
  have := UpperHalfPlane.linear_ne_zero ![a 0, a 1] z
  apply this
  rw [fun_ne_zero_cases] at *
  simp [ha] at *
  simp at ha
  rw [ha]
  have : ((0 : ℂ)^k)⁻¹ = 0 := by
    simp
    rw [zpow_eq_zero_iff hk]
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, one_div, this, uhc, top_eq_univ,
    image_univ]
  exact differentiableOn_const 0

lemma eisSummad_complex_extension_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) (hk : k ≠ 0) :
  DifferentiableOn ℂ ((fun (z : ℍ) =>  eisSummand k a z ) ∘
  (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
      (UpperHalfPlane.coe '' ⊤) := by
  apply DifferentiableOn.congr (complex_eisSummand_differentiableOn k a hk)
  intro z hz
  simp only [eisSummand, one_div, comp_apply, inv_inj]
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp only [ne_eq, top_eq_univ, image_univ, mem_range, PartialHomeomorph.symm_symm,
    OpenEmbedding.toPartialHomeomorph_apply, UpperHalfPlane.coe] at *
  rw [this]

lemma eisensteinSeries_SIF_complex_extension_differentiableOn (N : ℕ) (a: Fin 2 → ZMod N) (k : ℤ)
    (hk : 3 ≤ k) : DifferentiableOn ℂ
      ((fun z => SlashInvariantForm.toFun (eisensteinSeries_SIF a k) z) ∘
        ↑(PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
      (UpperHalfPlane.coe '' ⊤) := by
  have hc := eisensteinSeries_TendstoLocallyUniformlyOn2 hk N a
  let f := ((fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z)) ∘
  (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))
  have := @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a)) ) _ _ _
    (UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a )) =>
  (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) ∘
  (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
    f ?_ ?_ ((eventually_of_forall fun s => ?_)) ?_
  convert this
  · exact atTop_neBot
  · exact hc
  · apply DifferentiableOn.sum
    intro v _
    apply eisSummad_complex_extension_differentiableOn
    linarith
  · rw [← OpenEmbedding.open_iff_image_open]
    simp only [top_eq_univ, isOpen_univ]
    exact openEmbedding_coe

theorem Eisenstein_lvl_N_is_mdiff (N : ℕ) (a: Fin 2 → ZMod N)  (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) := by
  rw [MDifferentiable]
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
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
    ((eisensteinSeries_SIF_complex_extension_differentiableOn N a k hk).continuousOn)
      (s := (UpperHalfPlane.coe '' ⊤)) (x := z) ha
  · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
    OpenEmbedding.toPartialHomeomorph_source, mem_univ]
  · apply DifferentiableOn.differentiableAt (s :=  UpperHalfPlane.coe '' ⊤) _ ha
    apply eisensteinSeries_SIF_complex_extension_differentiableOn N a k hk
