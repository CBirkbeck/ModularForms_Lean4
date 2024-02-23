import Modformsported.ForMathlib.EisensteinSeries.boundingfunctions
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex   Manifold Pointwise

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


namespace EisensteinSeries

def UpperHalfPlane.upperHalfSpace :=
  {z : ℂ | 0 < z.im}

theorem upper_half_plane_isOpen : IsOpen UpperHalfPlane.upperHalfSpace :=
  IsOpen.preimage Complex.continuous_im isOpen_Ioi

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)


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
  simp [this]
  exact differentiableOn_const 0

lemma sdf2 (k : ℤ) (a : Fin 2 → ℤ) (hk : k ≠ 0) :
  DifferentiableOn ℂ ((fun (z : ℍ) =>  eisSummand k a z ) ∘
  (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
      (UpperHalfPlane.coe '' ⊤) := by
  apply DifferentiableOn.congr (complex_eisSummand_differentiableOn k a hk)
  intro z hz
  simp [eisSummand]
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp at *
  rw [this]


lemma diffat (N : ℕ) (a: Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) : DifferentiableOn ℂ
  ((fun z => SlashInvariantForm.toFun (eisensteinSeries_SIF a k) z) ∘
    ↑(PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
      (UpperHalfPlane.coe '' ⊤) := by
  simp
  have hc := eisensteinSeries_TendstoLocallyUniformlyOn2 k hk N a
  let f:=
  ((fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z)) ∘
    (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))
  have := @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a)) ) _ _ _
    (UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a )) =>
  (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) ∘
  (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
    f ?_ ?_ ((eventually_of_forall fun s => ?_)) ?_
  convert this
  simp
  exact atTop_neBot
  exact hc
  apply DifferentiableOn.sum
  intro v _
  apply sdf2
  linarith
  rw [← OpenEmbedding.open_iff_image_open]
  simp
  exact openEmbedding_coe


theorem Eisenstein_lvl_N_is_mdiff (N : ℕ) (a: Fin 2 → ZMod N)  (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) := by
  rw [MDifferentiable]
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  intro z
  constructor
  have := (diffat N a k hk).continuousOn
  have hh := ContinuousOn.continuousAt this (s := (UpperHalfPlane.coe '' ⊤)) (x := z) ?_
  rw [PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
    (e := (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph
    UpperHalfPlane.coe openEmbedding_coe)))]
  exact hh
  simp
  apply IsOpen.mem_nhds
  rw [← OpenEmbedding.open_iff_image_open]
  simp
  exact openEmbedding_coe
  simp
  apply DifferentiableOn.differentiableAt (s :=  UpperHalfPlane.coe '' ⊤) _ _
  apply diffat N a k hk
  apply IsOpen.mem_nhds
  rw [← OpenEmbedding.open_iff_image_open]
  simp
  exact openEmbedding_coe
  simp
