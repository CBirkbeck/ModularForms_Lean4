import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

open scoped Classical BigOperators Filter

open Filter Complex Asymptotics

section

variable {α : Type _} {β : Type _} {s : Set α}

def extendByZero [Zero β] (f : s → β) : α → β := fun z => if h : z ∈ s then f ⟨z, h⟩ else 0

theorem extendByZero_eq_of_mem [Zero β] (f : s → β) (x : α) (hx : x ∈ s) :
    (extendByZero f) x = f ⟨x, hx⟩ := by rw [extendByZero];  split_ifs; tauto

theorem extendByZero_zero [Zero β] : extendByZero (fun _ => 0 : s → β) = fun h => 0 := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

theorem extendByZero_zero' [Zero β] : extendByZero (0 : s → β) = 0 := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

theorem extendByZero_add [AddGroup β] (f g : s → β) :
    extendByZero (f + g) = extendByZero f + extendByZero g := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

theorem extendByZero_sum [AddCommMonoid β] (ι : Finset α) (F : ι → s → β) :
    (extendByZero fun x : s => ∑ i : ι, F i x) = ∑ i : ι, extendByZero (F i) :=
  by
  ext z
  by_cases h : z ∈ s
  simp only [extendByZero, h, Finset.sum_apply, dif_pos]
  simp only [extendByZero, h, Finset.sum_apply, dif_neg, not_false_iff, Finset.sum_const_zero]

theorem extendByZero_mul [Semiring β] (f g : s → β) :
    extendByZero (f * g) = extendByZero f * extendByZero g := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

theorem extendByZero_neg [AddGroup β] (f : s → β) : extendByZero (-f) = -extendByZero f := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

theorem extendByZero_smul [Ring β] (c : β) (f : s → β) :
    extendByZero (c • f) = c • extendByZero f := by
  ext z ; by_cases h : z ∈ s <;> simp [extendByZero, h]

end

def OpenSubs :=
  TopologicalSpace.Opens ℂ

/--
A function is Holomorphic on an open subset of the complex numbers, if for every point in the domain
there is a neibourhood around the point containing the derivative of the function. In order to make it work
with has_deriv_within_at, we first extend the function by zero to the entire complex plane. -/
def IsHolomorphicOn {D : OpenSubs} (f : D.1 → ℂ) : Prop :=
  ∀ z : D.1, ∃ f', HasDerivWithinAt (extendByZero f) f' D.1 z

theorem isHolomorphicOn_iff_differentiableOn (D : OpenSubs) (f : D.1 → ℂ) :
    DifferentiableOn ℂ (extendByZero f) D.1 ↔ IsHolomorphicOn f :=
  by
  classical!
  rw [IsHolomorphicOn]
  constructor
  · rw [DifferentiableOn]
    intro hd z
    have h1 := hd z.1 z.2
    have h2 := DifferentiableWithinAt.hasFDerivWithinAt h1
    simp_rw [HasDerivWithinAt]
    simp_rw [HasDerivAtFilter]
    simp_rw [HasFDerivWithinAt] at h2
    simp at *
    dsimp only [DifferentiableWithinAt] at h1
    use Classical.choose h1 1
    simp only [ContinuousLinearMap.smulRight_one_one]
    by_cases H : ((nhdsWithin (↑z) (D.1 \ {↑z})) = (⊥ : Filter ℂ))
    · apply HasFDerivWithinAt.of_nhdsWithin_eq_bot H
    · simp only [TopologicalSpace.Opens.carrier_eq_coe] at H
      rwa [fderivWithin, if_neg H, dif_pos h1] at h2
  intro hz
  rw [DifferentiableOn]
  intro x hx
  have h1 := hz ⟨x, hx⟩
  have h2 := Classical.choose_spec h1
  apply HasDerivWithinAt.differentiableWithinAt h2

variable {D : OpenSubs}

theorem const_hol (c : ℂ) : IsHolomorphicOn fun _ : D.1 => (c : ℂ) := by
  rw [IsHolomorphicOn]
  intro z
  use (0 : ℂ)
  have h1 := hasDerivWithinAt_const z.1 D.1 c
  apply HasDerivWithinAt.congr_of_eventuallyEq_of_mem h1 _ z.2
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨D.1, self_mem_nhdsWithin, extendByZero_eq_of_mem _⟩

theorem zero_hol (D : OpenSubs) : IsHolomorphicOn fun _ : D.1 => (0 : ℂ) := by
  apply const_hol (0 : ℂ)

theorem one_hol (D : OpenSubs) : IsHolomorphicOn fun _ : D.1 => (1 : ℂ) := by
  apply const_hol (1 : ℂ)

theorem add_hol (f g : D.1 → ℂ) (f_hol : IsHolomorphicOn f) (g_hol : IsHolomorphicOn g) :
    IsHolomorphicOn (f + g) := by
  intro z₀
  cases' f_hol z₀ with f'z₀ Hf
  cases' g_hol z₀ with g'z₀ Hg
  exists f'z₀ + g'z₀
  rw [extendByZero_add]
  have := HasDerivWithinAt.add Hf Hg
  exact this

theorem mul_hol (f g : D.1 → ℂ) (f_hol : IsHolomorphicOn f) (g_hol : IsHolomorphicOn g) :
    IsHolomorphicOn (f * g) := by
  intro z₀
  cases' f_hol z₀ with f'z₀ Hf
  cases' g_hol z₀ with g'z₀ Hg
  exists f'z₀ * extendByZero g z₀ + extendByZero f z₀ * g'z₀
  rw [extendByZero_mul]
  have := HasDerivWithinAt.mul Hf Hg
  exact this

theorem neg_hol (f : D.1 → ℂ) (f_hol : IsHolomorphicOn f) : IsHolomorphicOn (-f) :=
  by
  intro z₀
  cases' f_hol z₀ with f'z₀ H
  exists -f'z₀
  rw [extendByZero_neg]
  have h3 := HasDerivWithinAt.neg H
  exact h3

/-- The ring of holomorphic functions-/
def holRing (D : OpenSubs) : Subring (D.1 → ℂ)
    where
  carrier := {f : D.1 → ℂ | IsHolomorphicOn f}
  zero_mem' := zero_hol D
  add_mem' := add_hol _ _
  neg_mem' := neg_hol _
  mul_mem' := mul_hol _ _
  one_mem' := one_hol D

theorem smul_hol (c : ℂ) (f : D.1 → ℂ) (f_hol : IsHolomorphicOn f) : IsHolomorphicOn (c • f) := by
  intro z₀
  cases' f_hol z₀ with f'z₀ Hf
  exists c • f'z₀
  rw [extendByZero_smul]
  exact HasDerivWithinAt.const_smul c Hf

def holSubmodule (D : OpenSubs) : Submodule ℂ (D.1 → ℂ) where
  carrier := {f : D.1 → ℂ | IsHolomorphicOn f}
  zero_mem' := zero_hol D
  add_mem' := add_hol _ _
  smul_mem' := smul_hol

theorem diff_on_diff (f : D.1 → ℂ)
    (h :
      ∀ x : D.1,
        ∃ ε : ℝ,
          0 < ε ∧ Metric.ball x.1 ε ⊆ D.1 ∧ DifferentiableOn ℂ (extendByZero f) (Metric.ball x ε)) :
    DifferentiableOn ℂ (extendByZero f) D.1 :=
  by
  simp_rw [DifferentiableOn] at *
  simp_rw [DifferentiableWithinAt] at *
  intro x hx
  obtain ⟨ε, hε, _, H⟩ := h ⟨x, hx⟩
  have HH := H x
  simp only [Metric.mem_ball, dist_self, hε, TopologicalSpace.Opens.carrier_eq_coe,
    forall_true_left] at HH
  obtain ⟨f', hf'⟩ := HH
  use f'
  simp_rw [hasFDerivWithinAt_iff_tendsto] at *
  rw [Metric.tendsto_nhds] at *
  intro δ hδ
  have hf2 := hf' δ hδ
  rw [Filter.eventually_iff_exists_mem] at *
  simp only [exists_prop, Metric.mem_ball, gt_iff_lt, dist_zero_right, ContinuousLinearMap.map_sub,
    SetCoe.forall, Subtype.coe_mk, norm_eq_abs, norm_mul, norm_inv] at *
  simp_rw [Metric.mem_nhdsWithin_iff] at *
  obtain ⟨S, ⟨e, he, HE⟩, HD⟩ := hf2
  refine ⟨S, ⟨min e ε, lt_min he hε, ?_⟩, HD⟩
  calc
    Metric.ball x (min e ε) ∩ D.carrier
    _ ⊆ Metric.ball x (min e ε) := Set.inter_subset_left _ _
    _ = Metric.ball x e ∩ Metric.ball x ε := by ext; simp
    _ ⊆ S := HE

theorem tendsto_unif_extendByZero (F : ℕ → D.1 → ℂ) (f : D.1 → ℂ)
    (h : TendstoUniformly F f Filter.atTop) :
    TendstoUniformlyOn (fun n : ℕ => extendByZero (F n)) (extendByZero f) Filter.atTop D.1 :=
  by
  simp_rw [Metric.tendstoUniformlyOn_iff]
  rw [Metric.tendstoUniformly_iff] at h
  intro ε hε
  have h2 := h ε hε
  simp only [TopologicalSpace.Opens.carrier_eq_coe, SetLike.coe_sort_coe, Subtype.forall,
    eventually_atTop, SetLike.mem_coe] at *
  obtain ⟨a, ha⟩ := h2
  use a
  intro b hb x hx
  have hf := extendByZero_eq_of_mem f _ hx
  have hFb := extendByZero_eq_of_mem (F b) _ hx
  rw [hf, hFb]
  apply ha b hb x hx
