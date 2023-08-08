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

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

section GradedRing

namespace ModularForm

open ModularForm

open scoped Topology Manifold UpperHalfPlane

variable (F : Type _) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

--cast for modular forms, which is useful for removing `heq`'s.
def mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) : ModularForm Γ b
    where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' := by intro A; have := f.slash_action_eq' A; convert this; exact h.symm
  holo' := f.holo'
  bdd_at_infty' := by intro A; convert f.bdd_at_infty' A <;> exact h.symm

#align modular_form.mcast ModularForm.mcast

theorem type_eq {a b : ℤ} (Γ : Subgroup SL(2, ℤ)) (h : a = b) : ModularForm Γ a = ModularForm Γ b := by
  induction h
  rfl

theorem cast_eq_mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) :
    cast (type_eq Γ h) f = mcast h f := by
  induction h
  ext1
  rfl

theorem hEq_one_mul (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq ((1 : ModularForm Γ 0).mul f) f := by
  apply heq_of_cast_eq (type_eq Γ (zero_add k).symm).symm
  funext
  rw [cast_eq_mcast, mcast]
  simp [one_coe_eq_one, one_mul]
  ext1
  rfl
  simp only [zero_add]

theorem hEq_mul_one (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq (f.mul (1 : ModularForm Γ 0)) f :=
  by
  apply heq_of_cast_eq (type_eq Γ (add_zero k).symm).symm
  funext
  rw [cast_eq_mcast, mcast]
  simp only [mul_coe, one_coe_eq_one, mul_one]
  ext1
  rfl
  simp only [add_zero]

theorem hEq_mul_assoc {a b c : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b)
    (h : ModularForm Γ c) : HEq ((f.mul g).mul h) (f.mul (g.mul h)) := by
  apply heq_of_cast_eq (type_eq Γ (add_assoc a b c))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, ← mul_assoc]
  rfl
  apply add_assoc

theorem hEq_mul_comm (a b : ℤ) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    HEq (f.mul g) (g.mul f) := by
  apply heq_of_cast_eq (type_eq Γ (add_comm a b))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, mul_comm]
  rfl
  apply add_comm

section
variable (ι : Type _) (A : ι → Type _)
variable [Zero ι]
variable [GradedMonoid.GOne A]
@[simp]
theorem one_fst : (1 : GradedMonoid A).fst = 0 :=
  rfl
@[simp]
theorem one_snd : (1 : GradedMonoid A).snd = 1 :=
  rfl
end

instance (Γ : Subgroup SL(2, ℤ)) : GradedMonoid.GOne fun k => ModularForm Γ k
    where
  one := 1

instance (Γ : Subgroup SL(2, ℤ)) : GradedMonoid.GMul fun k => ModularForm Γ k
    where
  mul f g := f.mul g

theorem GradedMonoid.mk_snd  {A : ι → Type _} (i : ι) (a : A i) :
  (GradedMonoid.mk i a).snd = a := rfl

instance gradedModRing (Γ : Subgroup SL(2, ℤ)) : DirectSum.GCommRing fun k => ModularForm Γ k
    where
  mul f g := f.mul g
  one := 1
  one_mul := by
    intro f
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [(· * ·), one_fst, zero_add]
    · simp only [(· * ·), one_fst, one_snd, Submodule.coe_mk, one_mul, hEq_one_mul]
  mul_one := by
    intro f
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [(· * ·), one_fst, add_zero]
    · simp only [(· * ·), one_fst, one_snd, Submodule.coe_mk, mul_one, hEq_mul_one]
  mul_assoc := by
    intro f g h
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_assoc
    · simp only [(· * ·), Submodule.coe_mk, hEq_mul_assoc]
  mul_zero := by intro i j f; ext1; simp
  zero_mul := by intro i j f; ext1; simp
  mul_add := by
    intro i j f g h
    ext1
    simp only [Pi.mul_apply, mul_add, mul_coe, add_apply]
  add_mul := by
    intro i j f g h
    ext1
    simp only [add_mul, mul_coe, Pi.mul_apply, add_apply]
  mul_comm := by
    intro f g
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_comm
    · apply hEq_mul_comm
  gnpow_zero' := by
    intro f
    apply Sigma.ext <;> rw [GradedMonoid.GMonoid.gnpowRec_zero]
  gnpow_succ' := by
    intro n f
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext <;> rw [GradedMonoid.GMonoid.gnpowRec_succ]
  natCast n := n • (1 : ModularForm Γ 0)
  natCast_zero := by simp
  natCast_succ := by intro n; simp only [add_smul, one_nsmul, add_right_inj]
  intCast n := n • (1 : ModularForm Γ 0)
  intCast_ofNat := by simp
  intCast_negSucc_ofNat := by intro; simp only [Int.negSucc_coe]; apply _root_.neg_smul
#align modular_form.graded_mod_ring ModularForm.gradedModRing


end ModularForm

end GradedRing

section PeterssonProduct

def pet (f g : ℍ → ℂ) (k : ℤ) : ℍ → ℂ := fun z => conj (f z) * (g z  : ℂ)* (UpperHalfPlane.im z : ℂ) ^ k

def petSelf (f : ℍ → ℂ) (k : ℤ) : ℍ → ℝ := fun z => Complex.abs (f z) ^ 2 * UpperHalfPlane.im z ^ k
#align pet_self petSelf


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

    --field_simp [h1, h2]; ring
  have : ((γ • z : ℍ) : ℂ).im = UpperHalfPlane.im z / Complex.normSq D :=
    by
    rw [UpperHalfPlane.coe_im]
    rw [sl_moeb']
    simp only [SMul.smul]
    rw [UpperHalfPlane.im_smul_eq_div_normSq γ z]
    refine congr_arg (fun x => x / Complex.normSq D) ?_
    convert one_mul (UpperHalfPlane.im z)
    -- congr
    -- convert UpperHalfPlane.im_smul_eq_div_normSq γ z
    -- stop
    simp only [UpperHalfPlane.coe_im,
      Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
    have h3 := γ.2
    

    -- suffices ((↑ₘγ).map ((↑) : ℤ → ℝ)).det = (1 : ℝ) by sorry; rw [this]; sorry; simp only [one_mul]
    trans Matrix.det ↑ₘγ
    -- have : (↑ₘ γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ℝ) = ↑ₘ(γ : SL(2, ℝ)) := by
    · rw [Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
    · apply Matrix.SpecialLinearGroup.det_coe
  apply_fun ((↑) : ℝ → ℂ) at this
  convert this
  simp only [UpperHalfPlane.coe_im, Complex.ofReal_div]
  rw [div_div, mul_conj]
#align pet_is_invariant pet_is_invariant

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
    rw [← ofReal_zpow, ofReal_mul_re, mul_comm]
  rw [this]; congr
  rw [mul_comm, ← normSq_eq_abs, normSq]
  simp only [MonoidWithZeroHom.coe_mk, IsROrC.star_def, mul_re, conj_re, conj_im, mul_neg,
    sub_neg_eq_add]
  simp only [ZeroHom.coe_mk]
#align pet_self_eq petSelf_eq

theorem petSelf_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : petSelf f k (γ • z) = petSelf f k z := by
  rw [petSelf_eq, petSelf_eq]; congr 1; exact pet_is_invariant f f hγ z
#align pet_self_is_invariant petSelf_is_invariant

end PeterssonProduct

