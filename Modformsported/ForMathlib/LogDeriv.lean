import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic


noncomputable section

open UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
  Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ" => UpperHalfPlane

def logDeriv (f : ℂ → ℂ) :=
  deriv f / f

theorem logDeriv_one : logDeriv 1 = 0 := by
  rw [logDeriv]
  simp
  ext1 x
  simp
  apply deriv_const x (1 : ℂ)

theorem log_derv_mul (f g : ℂ → ℂ) (x : ℂ) (hfg : f x * g x ≠ 0) (hdf : DifferentiableAt ℂ f x)
    (hdg : DifferentiableAt ℂ g x) :
    logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x :=
  by
  simp_rw [logDeriv]
  simp
  rw [deriv_mul hdf hdg]
  have h1 := (mul_ne_zero_iff.1 hfg).1
  have h2 := (mul_ne_zero_iff.1 hfg).2
  field_simp
  apply mul_comm

theorem DifferentiableAt.product {α : Type _} {ι : Finset α} (F : α → ℂ → ℂ) (s : ℂ)
    (hd : ∀ i : ι, DifferentiableAt ℂ (fun z => F i z) s) :
    DifferentiableAt ℂ (fun z => ∏ i in ι, F i z) s :=
  by
  induction' ι using Finset.cons_induction_on with a s ha ih
  simp only [Finset.prod_empty, differentiableAt_const]
  simp only [Finset.cons_eq_insert]
  rw [← Finset.prod_fn]
  rw [Finset.prod_insert]
  apply DifferentiableAt.mul
  simp only [Finset.forall_coe, Subtype.coe_mk, Finset.mem_cons, forall_eq_or_imp] at *
  apply hd.1
  rw [← Finset.prod_fn] at ih 
  apply ih
  intro r
  simp at *
  apply hd.2
  exact r.2
  exact ha

theorem logDeriv_prod {α : Type _} (s : Finset α) (f : α → ℂ → ℂ) (t : ℂ) (hf : ∀ x ∈ s, f x t ≠ 0)
    (hd : ∀ x ∈ s, DifferentiableAt ℂ (f x) t) :
    logDeriv (∏ i in s, f i) t = ∑ i in s, logDeriv (f i) t :=
  by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp [logDeriv_one]
  · rw [Finset.forall_mem_cons] at hf 
    simp [ih hf.2]; rw [Finset.prod_insert]; rw [Finset.sum_insert]
    have := log_derv_mul (f a) (∏ i in s, f i) t ?_ ?_ ?_
    simp at *
    rw [ih hf.2] at this 
    simp at *
    rw [←this]
    simp
    congr
    ext1 r
    simp
    intro x hx
    apply hd.2
    simp only [hx, Finset.cons_eq_insert, Finset.mem_insert, or_true_iff]
    apply mul_ne_zero hf.1
    simp only [Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    exact hf.2
    apply hd
    simp only [Finset.cons_eq_insert, Finset.mem_insert, eq_self_iff_true, true_or_iff]
    rw [Finset.prod_fn]
    apply DifferentiableAt.product
    intro r
    apply hd
    simp [r.2]
    repeat' exact ha

theorem logDeriv_congr (f g : ℂ → ℂ) (hfg : f = g) : logDeriv f = logDeriv g :=
  by
  apply congr
  rfl
  exact hfg

theorem logDeriv_comp (f g : ℂ → ℂ) (x : ℂ) (hf : DifferentiableAt ℂ f (g x))
    (hg : DifferentiableAt ℂ g x) : logDeriv (f ∘ g) x = (logDeriv f) (g x) * deriv g x :=
  by
  simp_rw [logDeriv]
  simp
  rw [deriv.comp _ hf hg]
  simp_rw [mul_comm]
  ring

theorem logDeriv_pi_z (x : ℂ) : logDeriv (fun z : ℂ => π * z) x = 1 / x :=
  by
  rw [logDeriv]
  simp
  rw [deriv_const_mul]
  field_simp
  apply div_mul_right
  norm_cast
  apply Real.pi_ne_zero
  exact differentiableAt_id'

theorem logDeriv_tendsto (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (x : s)
    (hF : TendstoLocallyUniformlyOn f g atTop s)
    (hf : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (f n) s) (hg : g x ≠ 0) :
    Tendsto (fun n : ℕ => logDeriv (f n) x) atTop (𝓝 ((logDeriv g) x)) :=
  by
  simp_rw [logDeriv]
  apply Tendsto.div
  swap
  apply hF.tendsto_at
  apply x.2
  have := hF.deriv ?_ ?_
  apply this.tendsto_at
  apply x.2
  apply hf
  apply hs
  apply hg

