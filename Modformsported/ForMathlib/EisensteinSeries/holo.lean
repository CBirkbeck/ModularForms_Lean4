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

#check  UpperHalfPlane.coe '' ⊤

theorem Eisenstein_lvl_N_is_mdiff (N : ℕ) (a: Fin 2 → ZMod N)  (k : ℤ) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z) := by
  rw [MDifferentiable]
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  intro z
  constructor
  sorry
  apply DifferentiableOn.differentiableAt (s :=  UpperHalfPlane.coe '' ⊤) _ _
  simp
  have hc := eisensteinSeries_TendstoLocallyUniformlyOn k hk N a
  let f:=
  ((fun (z : ℍ) => (eisensteinSeries_SIF a k).1 z)) ∘
    (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))
  have hf : DifferentiableOn ℂ f (UpperHalfPlane.coe '' ⊤) := by sorry


  let t := (atTop : Filter (Finset ↑(gammaSet N a)))
  haveI : NeBot t := by sorry
  have := @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a)) ) _ _ _
    (UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a )) =>
  (fun (z : ℍ) => ∑ x in s, eisSummand k x z ) ∘ (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)))
    f ?_ ?_ ?_ ?_
  convert this
  simp

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
