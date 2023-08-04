import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.Calculus.Series
import Mathbin.Analysis.Calculus.ParametricIntervalIntegral
import Mathbin.Data.Complex.Basic

#align_import mod_forms.Eisenstein_Series.tsum_lemmas

noncomputable section

open TopologicalSpace Set Metric Filter Function Complex MeasureTheory

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

theorem embedding_coer : Embedding (coe : ℝ → ℂ) :=
  by
  apply Isometry.embedding
  apply isometry_of_real

@[norm_cast]
theorem tendsto_coe {α : Type _} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : ℂ)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coer.tendsto_nhds_iff.symm

@[simp, norm_cast]
theorem coe_finset_sum {α : Type _} {s : Finset α} {f : α → ℝ} :
    ↑(∑ a in s, f a) = (∑ a in s, f a : ℂ) :=
  ofReal.map_sum f s

@[norm_cast]
protected theorem hasSum_coe {α : Type _} {f : α → ℝ} {r : ℝ} :
    HasSum (fun a => (f a : ℂ)) ↑r ↔ HasSum f r :=
  by
  have :
    (fun s : Finset α => ∑ a in s, ↑(f a)) = (coe : ℝ → ℂ) ∘ fun s : Finset α => ∑ a in s, f a :=
    funext fun s => coe_finset_sum.symm
  unfold HasSum <;> rw [this, tendsto_coe]

protected theorem tsum_coe_eq {α : Type _} {f : α → ℝ} {r : ℝ} (h : HasSum f r) :
    ∑' a, (f a : ℂ) = r :=
  (hasSum_coe.2 h).tsum_eq

protected theorem coe_tsum {α : Type _} {f : α → ℝ} : Summable f → ↑(tsum f) = ∑' a, (f a : ℂ)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, tsum_coe_eq hr]

theorem coe_summable {α : Type _} (f : α → ℝ) : Summable ((coe : ℝ → ℂ) ∘ f) ↔ Summable f :=
  by
  apply Summable.map_iff_of_leftInverse Complex.ofReal Complex.reAddGroupHom
  exact Complex.continuous_ofReal
  exact Complex.continuous_re
  intro; rfl

theorem tsum_coe {α : Type _} (f : α → ℝ) : ∑' i, (f i : ℂ) = (∑' i, f i : ℝ) :=
  by
  by_cases hf : Summable f
  apply (coe_tsum hf).symm
  have := tsum_eq_zero_of_not_summable hf
  rw [this]
  simp
  have h2 := coe_summable f
  apply tsum_eq_zero_of_not_summable
  rw [h2]
  apply hf

theorem nat_pos_tsum2 (f : ℕ → ℂ) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f :=
  by
  rw [Function.Injective.summable_iff]
  simp
  exact PNat.coe_injective
  intro x hx
  simp at hx 
  rw [hx]
  exact hf

theorem hasSum_pnat' (f : ℕ → ℂ) (hf2 : Summable f) :
    HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
  by
  have := _root_.equiv.pnat_equiv_nat.hasSum_iff
  simp_rw [Equiv.pnatEquivNat] at *
  simp at *
  rw [← this]
  have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
    by
    have hs : Summable fun n : ℕ+ => f n := by apply hf2.Subtype
    apply Summable.congr hs
    intro b; simp
  rw [Summable.hasSum_iff hf3]
  congr
  funext
  simp

theorem nat_pos_tsum2' {α : Type _} [TopologicalSpace α] [AddCommMonoid α] (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.summable_iff _root_.equiv.pnat_equiv_nat]
  constructor
  intro hf
  apply Summable.congr hf
  intro b
  simp
  intro hf
  apply Summable.congr hf
  intro b
  simp

theorem tsum_pNat (f : ℕ → ℂ) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n :=
  by
  by_cases hf2 : Summable f
  rw [tsum_eq_zero_add]
  rw [hf]
  simp
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    have := _root_.equiv.pnat_equiv_nat.hasSum_iff
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    rw [← this]
    have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply hf2.Subtype
      apply Summable.congr hs
      intro b; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
  apply symm
  apply hpos.tsum_eq
  apply hf2
  have h1 := tsum_eq_zero_of_not_summable hf2
  rw [← nat_pos_tsum2 f hf] at hf2 
  have h2 := tsum_eq_zero_of_not_summable hf2
  simp [h1, h2]

theorem tsum_pnat' (f : ℕ → ℂ) : ∑' n : ℕ+, f n = ∑' n, f (n + 1) :=
  by
  by_cases hf2 : Summable fun n : ℕ+ => f n
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    have := _root_.equiv.pnat_equiv_nat.hasSum_iff
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    rw [← this]
    have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
      by
      apply Summable.congr hf2
      intro b; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
  apply symm
  apply hpos.tsum_eq
  have h1 := tsum_eq_zero_of_not_summable hf2
  rw [nat_pos_tsum2'] at hf2 
  have h2 := tsum_eq_zero_of_not_summable hf2
  simp [h1, h2]

theorem prod_sum (f : ℤ × ℤ → ℂ) (hf : Summable f) : Summable fun a => ∑' b, f ⟨a, b⟩ :=
  by
  have := Equiv.summable_iff (Equiv.sigmaEquivProd ℤ ℤ)
  rw [← this] at hf 
  have H := Summable.sigma hf
  simp at H 
  apply Summable.congr H
  intro b
  simp

def mapdiv (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ :=
  by
  intro x
  have h1 := x.1.1
  have h11 := Nat.fst_mem_divisors_of_mem_antidiagonal x.2
  have h111 := Nat.pos_of_mem_divisors h11
  have h2 := x.1.2
  have h22 := Nat.snd_mem_divisors_of_mem_antidiagonal x.2
  have h222 := Nat.pos_of_mem_divisors h22
  set n1 : ℕ+ := ⟨x.1.1, h111⟩
  set n2 : ℕ+ := ⟨x.1.2, h222⟩
  use⟨n1, n2⟩

variable (f : Σ n : ℕ+, Nat.divisorsAntidiagonal n)

def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+
    where
  toFun x := mapdiv x.1 x.2
  invFun x :=
    ⟨⟨x.1.1 * x.2.1, by apply mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by
      rw [Nat.mem_divisorsAntidiagonal]; simp⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h 
    simp_rw [mapdiv]
    simp only [h, PNat.mk_coe, eq_self_iff_true, Subtype.coe_eta, true_and_iff]
    cases h; cases n; dsimp at *; induction h_left; rfl
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    simp_rw [mapdiv]
    exfalso
    simp only [not_lt_zero'] at h 
    exact h
    simp_rw [mapdiv]
    simp only [eq_self_iff_true, Subtype.coe_eta]

theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonall {f : ℕ+ × ℕ+ → ℂ} :
    (Summable fun x : ℕ+ × ℕ+ => f x) ↔
      Summable fun x : Σ n : ℕ+, Nat.divisorsAntidiagonal n =>
        f ⟨(mapdiv x.1 x.2).1, (mapdiv x.1 x.2).2⟩ :=
  by
  simp_rw [mapdiv]
  apply sigma_antidiagonal_equiv_prod.summable_iff.symm

theorem nat_pos_tsum (f : ℕ → ℝ) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f :=
  by
  rw [Function.Injective.summable_iff]
  simp
  exact PNat.coe_injective
  intro x hx
  simp at hx 
  rw [hx]
  exact hf

theorem nat_pos_tsum' (ξ : ℂ) :
    (Summable fun n : ℕ => ξ ^ n) → Summable fun n : ℕ+ => ξ ^ (n : ℕ) :=
  by
  intro h
  apply h.subtype

theorem sumaux (f : ℕ × ℕ → ℂ) (e : ℕ+) :
    ∑ x : Nat.divisorsAntidiagonal e, f x = ∑ x : ℕ × ℕ in Nat.divisorsAntidiagonal e, f x :=
  by
  simp only [Finset.univ_eq_attach]
  apply Finset.sum_finset_coe

theorem int_nat_sum (f : ℤ → ℂ) : Summable f → Summable fun x : ℕ => f x :=
  by
  have : IsCompl (Set.range (coe : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) h
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  intro h
  rw [← @summable_subtype_and_compl _ _ _ _ _ f _ (Set.range (coe : ℕ → ℤ))] at h 
  cases h
  rw [← (Equiv.ofInjective (coe : ℕ → ℤ) Nat.cast_injective).symm.summable_iff]
  apply Summable.congr h_left
  intro b
  funext
  simp_rw [Equiv.apply_ofInjective_symm]
  simp
  apply congr_arg
  cases b; cases h_right; cases h_left; cases b_property; induction b_property_h; dsimp at *
  simp at *

theorem sum_int_even (f : ℤ → ℂ) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n :=
  by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    have := _root_.equiv.pnat_equiv_nat.hasSum_iff
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    rw [← this]
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).Subtype
      apply Summable.congr hs
      intro b; simp; congr; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
    congr
    norm_cast
    simp
  have hneg : HasSum (fun n : ℕ => f (-n.succ)) (∑' n : ℕ+, f n) :=
    by
    have h1 : (fun n : ℕ => f (-↑n.succ)) = fun n : ℕ => f ↑n.succ :=
      by
      funext
      apply hf
    rw [h1]
    convert hpos
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring

def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := by apply neg_neg
  right_inv := by apply neg_neg

def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := by apply Int.pred_succ
  right_inv := by apply Int.succ_pred

theorem summable_neg (f : ℤ → ℂ) (hf : Summable f) : Summable fun d => f (-d) :=
  by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ neg_equiv.to_fun :=
    by
    funext
    simp
    rfl
  rw [h]
  have := neg_equiv.summable_iff.mpr hf
  apply this

theorem int_sum_neg (f : ℤ → ℂ) (hf : Summable f) : ∑' d : ℤ, f d = ∑' d, f (-d) :=
  by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ neg_equiv.to_fun :=
    by
    funext
    simp
    rfl
  rw [h]
  apply symm
  apply neg_equiv.tsum_eq
  exact T25Space.t2Space

theorem int_tsum_pNat (f : ℤ → ℂ) (hf2 : Summable f) :
    ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) :=
  by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    have := _root_.equiv.pnat_equiv_nat.hasSum_iff
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    rw [← this]
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).Subtype
      apply Summable.congr hs
      intro b; simp; congr; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
    congr
    norm_cast
    simp
  have hneg : HasSum (fun n : ℕ => f (-n.succ)) (∑' n : ℕ+, f (-n)) :=
    by
    have := _root_.equiv.pnat_equiv_nat.hasSum_iff
    simp_rw [Equiv.pnatEquivNat] at *
    rw [← this]
    rw [Summable.hasSum_iff _]
    congr
    funext
    simp
    congr
    simp_rw [PNat.natPred]
    simp
    ring
    exact T25Space.t2Space
    rw [Equiv.summable_iff]
    have H : Summable fun d : ℤ => f d.pred :=
      by
      have := succ_equiv.symm.summable_iff.2 hf2
      apply this
    have H2 := summable_neg _ H
    have := int_nat_sum _ H2
    apply Summable.congr this
    intro b
    simp
    congr
    simp_rw [Int.pred]
    ring
    exact AddCommGroup.toAddCommMonoid ℂ
    exact UniformSpace.toTopologicalSpace
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring_nf

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivAt_tsum_fun {α : Type _} [NeBot (atTop : Filter (Finset α))] (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) x :=
  by
  have A :
    ∀ x : ℂ,
      x ∈ s →
        tendsto (fun t : Finset α => ∑ n in t, (fun z => f n z) x) at_top
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A
  exact hx
  use fun n : Finset α => fun a => ∑ i in n, deriv (fun z => f i z) a
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK1 hK2
  have HU := hu K hK1 hK2
  obtain ⟨u, hu1, hu2⟩ := HU
  apply tendstoUniformlyOn_tsum hu1
  intro n x hx
  simp
  apply hu2 n ⟨x, hx⟩
  exact complete_of_proper
  apply eventually_of_forall
  intro t r hr
  apply HasDerivAt.sum
  intro q w
  rw [hasDerivAt_deriv_iff]
  simp
  apply hf2 q ⟨r, hr⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivWithinAt_tsum_fun {α : Type _} [NeBot (atTop : Filter (Finset α))] (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).HasDerivWithinAt

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivWithinAt_tsum_fun' {α : Type _} [NeBot (atTop : Filter (Finset α))] (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  by
  have := hasDerivWithinAt_tsum_fun f hs x hx hf hu hf2
  convert this
  simp
  ext1 n
  apply DifferentiableAt.derivWithin
  apply hf2 n ⟨x, hx⟩
  apply IsOpen.uniqueDiffWithinAt hs hx

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem deriv_tsum_fun' {α : Type _} [NeBot (atTop : Filter (Finset α))] (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply
    HasDerivWithinAt.derivWithin (hasDerivWithinAt_tsum_fun' f hs x hx hf hu hf2)
      (IsOpen.uniqueDiffWithinAt hs hx)

