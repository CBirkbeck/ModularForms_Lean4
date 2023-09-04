import Modformsported.ForMathlib.ModForms2
import Mathlib.NumberTheory.Modular
import Modformsported.ModForms.GeneralQExpansions.QExpansion


/-! 

**Bounds for the integrand of the Petersson product**

The main result here is that if f is a cusp form of level 1, then
`abs (f z) ^ 2 * (im z) ^ k` is uniformly bounded on the upper half-plane.

FIXME : The code here depends on a couple of lemmas at the end of `mod_forms2.lean`, which ought
to be trivial but are gnarly because of the coercion issues around SL2Z actions. For some reason
that code stops working if I transplant it to this file. -/


open ModularForm Complex Filter Asymptotics

open scoped Real Topology Manifold Filter ModularForm

noncomputable section

local notation "ℍ" => UpperHalfPlane

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

/-- The Petersson function of a cuspform is continuous. -/
theorem pet_cts {k : ℤ} (f : CuspForm ⊤ k) : Continuous (petSelf f k) :=
  by
  apply Continuous.mul
  norm_cast
  simp
  · apply Continuous.pow 
    apply Complex.continuous_abs.comp (f.holo'.continuous)
  · apply Continuous.zpow₀ UpperHalfPlane.continuous_im k
    intro z
    left
    apply z.2.ne' 

/-- The image of a truncation of the fundamental domain, under the inclusion `ℍ → ℂ`, defined by `≤`
inequalities (so it will be a closed subset of `ℂ`). -/
theorem image_fd (A : ℝ) :
    (UpperHalfPlane.coe '' {x : ℍ | x ∈ ModularGroup.fd ∧ x.im ≤ A} : Set ℂ) =
      {x : ℂ | 0 ≤ x.im ∧ |x.re| ≤ 1 / 2 ∧ 1 ≤ abs x ∧ im x ≤ A} :=
  by
  ext1 z; rw [ModularGroup.fd]; dsimp
  constructor
  · intro hz
    obtain ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, hzx⟩ := hz
    rw [← hzx]
    
    refine' ⟨x.2.le, hx2, _, hx3⟩
    rw [← one_le_sq_iff, ←Complex.normSq_eq_abs]; exact hx1; apply Complex.abs.nonneg
  · intro hz; obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    have h := le_or_lt (im z) 0
    cases' h with h h
    -- This is a clumsy way of showing that im z = 0 leads to a contradiction.
    -- Todo: improve this by comparison with three_lt_four_mul_im_sq_of_mem_fdo in modular.lean.
    · have : im z = 0 := by linarith
      have t := (one_le_sq_iff (Complex.abs.nonneg _)).mpr hz3
      rw [←Complex.normSq_eq_abs] at t ; rw [normSq] at t ; simp only [MonoidWithZeroHom.coe_mk] at t 
      simp at t
      rw [this] at t ; simp only [MulZeroClass.mul_zero, add_zero] at t 
      rw [← abs_mul_self] at t ; rw [← pow_two] at t ; rw [_root_.abs_pow] at t 
      have tt : |re z| ^ 2 ≤ (1 / 2) ^ 2 := by
        norm_cast
        rw [sq_le_sq]; rw [_root_.abs_abs]
        have : 0 < (1 / 2 : ℝ) := by simp
        conv =>
          rhs
          rw [abs_of_pos this]
        exact hz2
      norm_cast at *  
      have t3 := le_trans t tt; exfalso; field_simp at t3 ; rw [le_one_div] at t3 
      · simp at t3 ; linarith; 
      · linarith; 
      · linarith
    -- Now the main argument.
    use ⟨z, h⟩;
    refine' ⟨⟨⟨_, hz2⟩, hz4⟩, by simp⟩
    rw [normSq_eq_abs]; rw [one_le_sq_iff (Complex.abs.nonneg _)]; exact hz3

/-- The standard fundamental domain, truncated at some finite height, is compact. -/
theorem compact_trunc_fd (A : ℝ) : IsCompact {x : ℍ | x ∈ ModularGroup.fd ∧ x.im ≤ A} :=
  by
  rw [UpperHalfPlane.embedding_coe.isCompact_iff_isCompact_image, image_fd  A]
  apply Metric.isCompact_of_isClosed_bounded
  · apply_rules [IsClosed.inter]
    · apply isClosed_Ici.preimage continuous_im
    · have : Continuous (fun u => |re u| : ℂ → ℝ) := by continuity
      refine' IsClosed.preimage this (@isClosed_Iic _ _ _ _ (1 / 2))
    · apply isClosed_Ici.preimage Complex.continuous_abs
    · apply isClosed_Iic.preimage continuous_im
  · rw [bounded_iff_forall_norm_le]; use Real.sqrt (A ^ 2 + (1 / 2) ^ 2)
    intro x hx; rw [Set.mem_setOf_eq] at hx 
    rw [norm_eq_abs]; rw [Complex.abs]; apply Real.le_sqrt_of_sq_le
    simp
    rw [Real.sq_sqrt (normSq_nonneg _)]
    rw [normSq]; dsimp; rw [add_comm]; apply add_le_add
    · rw [← pow_two]; rw [sq_le_sq]; apply abs_le_abs
      · exact hx.2.2.2;
      · exact le_trans (by linarith) (le_trans hx.1 hx.2.2.2)
    · rw [← pow_two]; rw [← inv_pow]; rw [sq_le_sq]; rw [inv_eq_one_div]; apply abs_le_abs
      · exact le_trans (le_abs_self (re x)) hx.2.1
      · exact le_trans (neg_le_abs_self (re x)) hx.2.1

/-- The Petersson function is bounded on the standard fundamental domain. -/
theorem pet_bound_on_fd {k : ℤ} (f : CuspForm ⊤ k) :
    ∃ C : ℝ, ∀ z : ℍ, z ∈ ModularGroup.fd → |petSelf f k z| ≤ C :=
  by
  obtain ⟨A, C1, H1⟩ := pet_bounded_large f
  have := (compact_trunc_fd A).exists_bound_of_continuousOn (pet_cts f).continuousOn
  cases' this with C2 H2; use max C1 C2; intro z hz
  have h:= le_or_lt (im z) A 
  cases' h with h h 
  · exact le_trans (H2 z ⟨hz, h⟩) (le_max_right _ _)
  · convert le_trans (H1 z h.le) (le_max_left C1 C2)
    apply _root_.abs_of_nonneg
    rw [petSelf]; apply mul_nonneg
    · apply pow_nonneg; apply AbsoluteValue.nonneg
    · apply zpow_nonneg; exact z.2.le

/-- The Petersson function is bounded everywhere. -/
theorem pet_bound {k : ℤ} (f : CuspForm ⊤ k) : ∃ C : ℝ, ∀ z : ℍ, |petSelf f k z| ≤ C :=
  by
  obtain ⟨C, HC⟩ := pet_bound_on_fd f; use C; intro z
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  replace HC := HC (g • z) hg
  have : petSelf f k (g • z) = petSelf f k z :=
    by
    apply petSelf_is_invariant f.toSlashInvariantForm
    simp [g.2]
  rwa [this] at HC 

