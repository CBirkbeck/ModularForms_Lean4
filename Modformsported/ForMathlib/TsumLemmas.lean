import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Series
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Data.Complex.Basic

noncomputable section

open TopologicalSpace Set Metric Filter Function Complex MeasureTheory

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

section coe_lems

theorem embedding_coer : Embedding (Complex.ofReal' : ℝ → ℂ) :=
  by
  apply Isometry.embedding
  have := isometry_ofReal
  convert this


@[norm_cast]
theorem tendsto_coe {α : Type _} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : ℂ)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coer.tendsto_nhds_iff.symm

@[simp, norm_cast]
theorem coe_finset_sum' {α : Type _} {s : Finset α} {f : α → ℝ} :
    ↑(∑ a in s, f a) = (∑ a in s, f a : ℂ) :=
  ofReal.map_sum f s

@[norm_cast]
theorem hasSum_coe {α : Type _} {f : α → ℝ} {r : ℝ} :
    HasSum (fun a => (f a : ℂ)) ↑r ↔ HasSum f r :=
  by
  have :
    (fun s : Finset α => ∑ a in s, ↑(f a)) =
      (Complex.ofReal' : ℝ → ℂ) ∘ fun s : Finset α => ∑ a in s, f a :=
    funext fun s => coe_finset_sum'.symm
  unfold HasSum
  rw [this]
  apply tendsto_coe

theorem tsum_coe_eq {α : Type _} {f : α → ℝ} {r : ℝ} (h : HasSum f r) :
    ∑' a, (f a : ℂ) = r :=
  (hasSum_coe.2 h).tsum_eq

theorem coe_tsum {α : Type _} {f : α → ℝ} : Summable f → ↑(tsum f) = ∑' a, (f a : ℂ)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, tsum_coe_eq hr]

theorem coe_summable {α : Type _} (f : α → ℝ) :
  Summable ((Complex.ofReal' : ℝ → ℂ) ∘ f) ↔ Summable f :=
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
  apply tsum_eq_zero_of_not_summable
  simp at *
  apply hf

section pnat_tsums

theorem nat_pos_tsum2   {α : Type _} [TopologicalSpace α] [AddCommMonoid α]
  (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f :=
  by
  apply Function.Injective.summable_iff
  exact PNat.coe_injective
  intro x hx
  simp at *
  by_cases h : 0 < x
  have := hx ⟨x,h⟩
  simp at this
  simp at *
  rw [h]
  exact hf

variable {α : Type _}

theorem hasSum_pnat' (f : ℕ → ℂ) (hf2 : Summable f) :
    HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
  by
  rw  [← _root_.Equiv.pnatEquivNat.hasSum_iff]
  simp_rw [Equiv.pnatEquivNat] at *
  simp at *
  have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
    by
    have hs : Summable fun n : ℕ+ => f n := by
      apply hf2.subtype
    apply Summable.congr hs
    intro b; simp
  rw [Summable.hasSum_iff hf3]
  congr
  funext
  simp

theorem nat_pos_tsum2' [TopologicalSpace α] [AddCommMonoid α]  (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.summable_iff _root_.Equiv.pnatEquivNat]
  constructor
  intro hf
  apply Summable.congr hf
  intro b
  simp
  intro hf
  apply Summable.congr hf
  intro b
  simp



theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [UniformAddGroup α] [T2Space α]
  [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n :=
  by
  by_cases hf2 : Summable f
  rw [tsum_eq_zero_add]
  rw [hf]
  simp
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw  [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by
        apply hf2.subtype
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

theorem tsum_pnat' [TopologicalSpace α] [AddCommMonoid α]  [T2Space α] (f : ℕ → α) :
  ∑' n : ℕ+, f n = ∑' n, f (n + 1) :=
  by
  by_cases hf2 : Summable fun n : ℕ+ => f n
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw  [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
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





section prod_lems


variable {α : Type u} {β : Type v} {γ : Type w} {i : α → Set β}

def unionEquiv (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ ι i) :
    (⋃ s : ℕ, ((ι s) : Set (ℤ × ℤ))) ≃ ℤ × ℤ where
  toFun x := x.1
  invFun x := by
    use x
    simp
    obtain ⟨i, hi1,_⟩:= HI x
    refine ⟨i,hi1⟩
  left_inv := by  intro x; cases x; rfl
  right_inv := by intro x; rfl

theorem summable_disjoint_union_of_nonneg {i : α → Set β} {f : (⋃ x, i x) → ℝ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔
      (∀ x, Summable fun y : i x => f ⟨y,  Set.mem_iUnion_of_mem (x) y.2 ⟩) ∧
        Summable fun x => ∑' y : i x, f ⟨y, Set.mem_iUnion_of_mem (x) y.2 ⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h01 : Summable f ↔ Summable (f ∘ h0) := by
   rw [Equiv.summable_iff]
  have h22 : ∀ y : Σ s : α, i s, 0 ≤ (f ∘ h0) y :=
    by
    intro y
    simp
    apply hf
  have h1 := summable_sigma_of_nonneg h22
  rw [←h01] at h1;
  convert h1

theorem tsum_disjoint_union_of_nonneg' {γ : Type} [AddCommGroup γ]  [ UniformSpace γ]
    [UniformAddGroup γ] [CompleteSpace γ] [T0Space γ] [T2Space γ]
    {i : α → Set β} {f : (⋃ x, i x) → γ}
    (h : ∀ a b, a ≠ b → Disjoint (i a) (i b)) (h1 : Summable f) :
    ∑' x, f x = ∑' x, ∑' y : i x, f ⟨y, Set.mem_iUnion_of_mem (x) y.2⟩ :=
  by
  let h0 := (Set.unionEqSigmaOfDisjoint h).symm
  have h11 : ∑' x, f x = ∑' y, f (h0 y) := by have := Equiv.tsum_eq h0 f; rw [← this]
  rw [h11]
  rw [tsum_sigma]
  rfl
  have h01 : Summable f ↔ Summable (f ∘ h0) := by rw [Equiv.summable_iff]
  convert (h01.1 h1)

theorem disjoint_aux (In : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ In i) :
    ∀ i j : ℕ, i ≠ j → Disjoint (In i) (In j) :=
  by
  intro i j h
  intro x h1 h2 a h3
  cases' a with a_fst a_snd
  dsimp at *
  simp at *
  have HI0 := HI a_fst a_snd
  have := ExistsUnique.unique HI0 (h1 h3) (h2 h3)
  rw [this] at h
  simp at *

theorem sum_lemma (f : ℤ × ℤ → ℝ) (h : ∀ y : ℤ × ℤ, 0 ≤ f y) (ι : ℕ → Finset (ℤ × ℤ))
    (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ ι i) : Summable f ↔ Summable fun n : ℕ => ∑ x in ι n, f x :=
  by
  let h2 := unionEquiv ι HI
  have h22 : ∀ y : ⋃ s : ℕ, (ι s), 0 ≤ (f ∘ h2) y :=
    by
    intro y
    apply h
  have hdis' := disjoint_aux ι HI
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint ((ι a)) ((ι b)) :=
    by
    intro a b hab;
    apply hdis'; exact hab
  have h3 := summable_disjoint_union_of_nonneg ?_ h22
  have h4 : Summable f ↔ Summable (f ∘ h2) := by rw [Equiv.summable_iff]
  rw [h4]
  rw [h3]
  constructor
  intro H
  convert H.2
  rw [←Finset.tsum_subtype]
  rfl
  intro H
  constructor
  intro x
  simp
  rw [unionEquiv]
  simp
  apply Finset.summable
  convert H
  rw [←Finset.tsum_subtype]
  rfl
  norm_cast

theorem tsum_lemma {γ : Type} [AddCommGroup γ]  [ UniformSpace γ]
    [UniformAddGroup γ] [CompleteSpace γ] [T0Space γ] [T2Space γ]
    (f : ℤ × ℤ → γ) (ι : ℕ → Finset (ℤ × ℤ)) (HI : ∀ y : ℤ × ℤ, ∃! i : ℕ, y ∈ ι i)
    (hs : Summable f) : ∑' x, f x = ∑' n : ℕ, ∑ x in ι n, f x :=
  by
  let h2 := unionEquiv ι HI
  have hdis' := disjoint_aux ι HI
  have hdis : ∀ a b : ℕ, a ≠ b → Disjoint ( (ι a)) ((ι b)) :=
    by
    intro a b hab;
    apply hdis'; exact hab
  have HS : Summable (f ∘ h2) := by rw [Equiv.summable_iff h2]; exact hs
  have HH := tsum_disjoint_union_of_nonneg' ?_ HS
  simp at HH
  have := Equiv.tsum_eq h2 f
  rw [← this]
  rw [HH]
  rw [unionEquiv]
  simp
  norm_cast





theorem prod_sum
  (f : ℤ × ℤ → ℂ) (hf : Summable f) : Summable fun a => ∑' b, f ⟨a, b⟩ :=
  by
  rw [← Equiv.summable_iff (Equiv.sigmaEquivProd ℤ ℤ)] at hf
  have H := Summable.sigma hf
  simp at H
  apply Summable.congr H
  intro b
  simp

def mapdiv (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ :=
  by
  intro x
  have h11 := Nat.fst_mem_divisors_of_mem_antidiagonal x.2
  have h111 := Nat.pos_of_mem_divisors h11
  have h22 := Nat.snd_mem_divisors_of_mem_antidiagonal x.2
  have h222 := Nat.pos_of_mem_divisors h22
  set n1 : ℕ+ := ⟨x.1.1, h111⟩
  set n2 : ℕ+ := ⟨x.1.2, h222⟩
  use n1
  use n2
  exact h222

variable (f : Σ n : ℕ+, Nat.divisorsAntidiagonal n)

def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+
    where
  toFun x := mapdiv x.1 x.2
  invFun x :=
    ⟨⟨x.1.1 * x.2.1, by apply mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by
      rw [Nat.mem_divisorsAntidiagonal]; simp; constructor; rfl; rw [not_or]; constructor;
        linarith [x.1.2]; linarith [x.2.2] ⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    simp_rw [mapdiv]
    simp only [h, PNat.mk_coe, eq_self_iff_true, Subtype.coe_eta, true_and_iff]
    ext
    simp at *
    simp_rw [h]
    norm_cast
    simp only
    simp only
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    simp_rw [mapdiv]
    exfalso

    simp at *
    simp_rw [mapdiv]
    simp [eq_self_iff_true, Subtype.coe_eta]
    norm_cast

theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonall {α : Type _} [TopologicalSpace α]
  [AddCommMonoid α] {f : ℕ+ × ℕ+ → α} :
    (Summable fun x : ℕ+ × ℕ+ => f x) ↔
      Summable fun x : Σ n : ℕ+, Nat.divisorsAntidiagonal n =>
        f ⟨(mapdiv x.1 x.2).1, (mapdiv x.1 x.2).2⟩ :=
  by
  simp_rw [mapdiv]
  apply sigmaAntidiagonalEquivProd.summable_iff.symm

/-
theorem nat_pos_tsum' (ξ : ℂ) :
    (Summable fun n : ℕ => ξ ^ n) → Summable fun n : ℕ+ => ξ ^ (n : ℕ) :=
  by
  intro h
  apply h.subtype
 -/

theorem sumaux [TopologicalSpace α] [AddCommMonoid α]  (f : ℕ × ℕ → α) (e : ℕ+) :
    ∑ x : Nat.divisorsAntidiagonal e, f x = ∑ x : ℕ × ℕ in Nat.divisorsAntidiagonal e, f x :=
  by
  simp only [Finset.univ_eq_attach]
  apply Finset.sum_finset_coe

theorem int_nat_sum [AddCommGroup α] [UniformSpace α] [ UniformAddGroup α]  [CompleteSpace α]
  (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x :=
  by
  have : IsCompl (Set.range (Int.ofNat : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) _
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  intro h
  have H:= @summable_subtype_and_compl _ _ _ _ _ f _ (Set.range (Int.ofNat : ℕ → ℤ))
  simp at H
  rw [← H] at h
  cases' h with h_left h_right
  rw [← (Equiv.ofInjective (Int.ofNat : ℕ → ℤ) Nat.cast_injective).symm.summable_iff]
  apply Summable.congr h_left
  intro b
  funext
  simp
  apply congr_arg
  exact Eq.symm (Equiv.apply_ofInjective_symm Nat.cast_injective b)

theorem int_pnat_sum [AddCommGroup α] [UniformSpace α] [ UniformAddGroup α]  [CompleteSpace α]
  (f : ℤ → α) : Summable f → Summable fun x : ℕ+ => f x := by
  intro h
  have :=int_nat_sum f h
  apply this.subtype

theorem sum_int_even  [UniformSpace α] [CommRing α]  [ UniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n :=
  by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).subtype
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

theorem summable_neg  [TopologicalSpace α] [AddCommMonoid α] (f : ℤ → α) (hf : Summable f) :
  Summable fun d => f (-d) :=
  by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ negEquiv.toFun :=
    by
    funext
    simp
    rfl
  rw [h]
  have := negEquiv.summable_iff.mpr hf
  apply this

theorem int_sum_neg [AddCommMonoid α] [TopologicalSpace α] [T2Space α] (f : ℤ → α) :
  ∑' d : ℤ, f d = ∑' d, f (-d) :=
  by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ negEquiv.toFun :=
    by
    funext
    simp
    rfl
  rw [h]
  apply symm
  apply negEquiv.tsum_eq


theorem int_tsum_pNat [UniformSpace α] [CommRing α]  [ UniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) :=
  by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw [←_root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).subtype
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
    rw [←_root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    rw [Summable.hasSum_iff _]
    congr
    funext
    simp
    congr
    simp_rw [PNat.natPred]
    simp
    ring
    rw [Equiv.summable_iff]
    have H : Summable fun d : ℤ => f d.pred :=
      by
      have := succEquiv.symm.summable_iff.2 hf2
      apply this
    have H2 := summable_neg _ H
    have := int_nat_sum _ H2
    apply Summable.congr this
    intro b
    simp
    congr
    simp_rw [Int.pred]
    ring
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring_nf

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ (K) (_ : K ⊆ s), IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) x :=
  by
  have A :
    ∀ x : ℂ,
      x ∈ s →
        Tendsto (fun t : Finset α => ∑ n in t, (fun z => f n z) x) atTop
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy

  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  use fun n : Finset α => fun a => ∑ i in n, deriv (fun z => f i z) a
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK1 hK2
  have HU := hu K hK1 hK2
  obtain ⟨u, hu1, hu2⟩ := HU
  apply tendstoUniformlyOn_tsum hu1
  intro n x hx
  simp
  apply hu2 n ⟨x, hx⟩
  apply eventually_of_forall
  intro t r hr
  apply HasDerivAt.sum
  intro q _
  rw [hasDerivAt_deriv_iff]
  simp
  apply hf2 q ⟨r, hr⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), Complex.abs (deriv (f n) k) ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) s x := by
  apply (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivWithinAt_tsum_fun' {α : Type _} (f : α → ℂ → ℂ)
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
  have Hd : (∑' (n : α), deriv (fun z => f n z) x) = (∑' n : α, derivWithin (fun z => f n z) s x) :=
    by
    apply tsum_congr
    intro n
    apply symm
    apply DifferentiableAt.derivWithin
    apply hf2 n ⟨x, hx⟩
    apply IsOpen.uniqueDiffWithinAt hs hx
  rw [Hd] at this
  convert this

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem deriv_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
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
