/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Basic

section SLModularAction

open Matrix Matrix.SpecialLinearGroup

open scoped Classical BigOperators MatrixGroups UpperHalfPlane

attribute [local instance] Fintype.card_fin_even
attribute [-instance] Matrix.SpecialLinearGroup.instCoeFun
attribute [-instance] Matrix.GeneralLinearGroup.instCoeFun
variable (g : SL(2, ℤ)) (z : ℍ) (Γ : Subgroup SL(2, ℤ))
-- Matrix.GLPos (Fin 2) ℝ R
theorem sl_moeb (A : SL(2, ℤ)) (z : ℍ) :
    A • z = @SMul.smul _ _ MulAction.toSMul (A : Matrix.GLPos (Fin 2) ℝ) z :=
  rfl

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

theorem sl_moeb' (A : SL(2, ℤ)) (z : ℍ) :
    letI := @MulAction.toSMul { x // x ∈ GL(2, ℝ)⁺ } ℍ
  -- (Submonoid.toMonoid GL(2, ℝ)⁺.toSubmonoid)

    A • z = (A : Matrix.GLPos (Fin 2) ℝ) • z :=
  rfl

end SLModularAction

open scoped ComplexConjugate UpperHalfPlane

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

open ModularForm

open CuspForm

open SlashInvariantForm

open Complex

noncomputable section

/-- The upper half space as a subset of `ℂ` which is convenient sometimes.-/
def UpperHalfPlane.upperHalfSpace :=
  {z : ℂ | 0 < z.im}

theorem upper_half_plane_isOpen : IsOpen UpperHalfPlane.upperHalfSpace :=
  IsOpen.preimage Complex.continuous_im isOpen_Ioi

theorem UpperHalfPlane.upperHalfSpace.uniqueDiffOn : UniqueDiffOn ℂ UpperHalfPlane.upperHalfSpace :=
  upper_half_plane_isOpen.uniqueDiffOn

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

section GradedRing

namespace ModularForm

open ModularForm

open scoped Topology Manifold UpperHalfPlane

variable (F : Type _) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

instance : Coe  (CuspForm Γ k) (ModularForm Γ k) := by
  refine { coe := ?coe }
  intro h
  use h
  apply h.holo'
  intro A
  apply (h.zero_at_infty' A).boundedAtFilter


section PeterssonProduct

def pet (f g : ℍ → ℂ) (k : ℤ) : ℍ → ℂ := fun z => conj (f z) * (g z  : ℂ)* (UpperHalfPlane.im z : ℂ) ^ k

def petSelf (f : ℍ → ℂ) (k : ℤ) : ℍ → ℝ := fun z => Complex.abs (f z) ^ 2 * UpperHalfPlane.im z ^ k


theorem pet_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    (g : SlashInvariantForm Γ k) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    pet f g k (γ • z) = pet f g k z := by
  dsimp only [pet]
  let D := UpperHalfPlane.denom γ z
  have hD : D ≠ 0 := by apply UpperHalfPlane.denom_ne_zero
  have mod_g : g (γ • z) = D ^ k * g z :=
    by
    have tt := (slash_action_eqn' k Γ g) ⟨γ, hγ⟩ z
    dsimp only [UpperHalfPlane.denom] at *; exact tt
  have mod_f : conj (f (γ • z)) = conj D ^ k * conj (f z) :=
    by
    have tt : f (γ • z) = D ^ k * f z := by apply (slash_action_eqn' k Γ f) ⟨γ, hγ⟩ z
    rw [tt, starRingEnd_apply, starRingEnd_apply, star_mul', ← star_zpow₀]; rfl
  rw [mod_f, mod_g]--; ring_nf
  suffices ↑(γ • z).im = ↑(UpperHalfPlane.im z) / D / conj D
    by
    rw [this]; simp (config := { zeta := false }) only [UpperHalfPlane.coe_im, div_zpow]
    trans (z.im : ℂ) ^ k / D ^ k / conj D ^ k * D ^ k * conj D ^ k * g z * conj (f z)
    · ring
    -- have :
    --  (z.im : ℂ) ^ k / D ^ k / conj D ^ k * g z * D ^ k * conj (f z) * conj D ^ k =
    --     (z.im : ℂ) ^ k / D ^ k / conj D ^ k * D ^ k * conj D ^ k * g z * conj (f z) :=
    --   by ring

    -- rw [this]
    trans (UpperHalfPlane.im z : ℂ) ^ k * g z * conj (f z)
    swap
    · ring
    congr 2
    have h1 : D ^ k ≠ 0 := zpow_ne_zero _ hD
    have h2 : conj D ^ k ≠ 0 := by
      apply zpow_ne_zero; rw [starRingEnd_apply, star_ne_zero]; exact hD
    rw [div_div, mul_assoc]; apply div_mul_cancel; apply mul_ne_zero h1 h2
  have : ((γ • z : ℍ) : ℂ).im = UpperHalfPlane.im z / Complex.normSq D :=
    by
    rw [UpperHalfPlane.coe_im]
    rw [sl_moeb']
    simp only [SMul.smul]
    rw [UpperHalfPlane.im_smul_eq_div_normSq γ z]
    refine congr_arg (fun x => x / Complex.normSq D) ?_
    convert one_mul (UpperHalfPlane.im z)
    simp only [UpperHalfPlane.coe_im,
      Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
    have h4 := _root_.RingHom.map_det (Int.castRingHom ℝ) γ.1
    simp at h4
    exact h4.symm
  apply_fun ((↑) : ℝ → ℂ) at this
  convert this
  simp only [UpperHalfPlane.coe_im, Complex.ofReal_div]
  rw [div_div, mul_conj]


theorem petSelf_eq (f : ℍ → ℂ) (k : ℤ) (z : ℍ) : petSelf f k z = re (pet f f k z) :=
  by
  dsimp only [pet, petSelf]
  simp_rw [starRingEnd_apply]
  have : (star (f z) * f z * (z.im : ℂ) ^ k).re = (star (f z) * f z).re * ↑z.im ^ k :=
    by
    conv =>
      lhs
      congr
      rw [mul_comm]
    rw [← ofReal_zpow, re_ofReal_mul, mul_comm]
  rw [this]; congr
  rw [mul_comm, ← normSq_eq_abs, normSq]
  simp only [MonoidWithZeroHom.coe_mk, IsROrC.star_def, mul_re, conj_re, conj_im, mul_neg,
    sub_neg_eq_add]
  simp only [ZeroHom.coe_mk]


theorem petSelf_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : petSelf f k (γ • z) = petSelf f k z := by
  rw [petSelf_eq, petSelf_eq]; congr 1; exact pet_is_invariant f f hγ z


end PeterssonProduct
