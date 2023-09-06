/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Complex.Exponential 
import Modformsported.ForMathlib.ExpSummableLemmas
import Modformsported.ForMathlib.AuxpLemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Modformsported.ForMathlib.LogDeriv
import Modformsported.ForMathlib.Cotangent.basic 


noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

--local notation "ℍ" => UpperHalfPlane

theorem logDeriv_sine (z : ℍ) : logDeriv (Complex.sin ∘ fun t => π * t) z = π * cot (π * z) :=
  by
  rw [logDeriv_comp]
  simp
  rw [logDeriv]
  simp
  rw [deriv_const_mul]
  rw [deriv_id'']
  simp
  rw [cot]
  apply mul_comm
  apply differentiable_id.differentiableAt
  apply differentiable_sin.differentiableAt
  apply Differentiable.differentiableAt
  apply Differentiable.const_mul
  apply differentiable_id
  

theorem logDeriv_eq_1 (x : ℍ) (n : ℕ) :
    logDeriv (fun z => 1 - z ^ 2 / (n + 1) ^ 2) x = 1 / (x - (n + 1)) + 1 / (x + (n + 1)) :=
  by
  have h1 : logDeriv (fun z => 1 - z ^ 2 / (n + 1) ^ 2) x = -2 * x / ((n + 1) ^ 2 - x ^ 2) :=
    by
    rw [logDeriv]
    simp 
    rw [deriv_sub]
    simp  
    field_simp
    congr
    rw [mul_one_sub]
    simp only [sub_right_inj]
    apply mul_div_cancel'
    apply pow_ne_zero
    norm_cast
    linarith
    apply differentiableAt_const
    apply DifferentiableAt.div_const
    apply DifferentiableAt.pow
    apply differentiable_id.differentiableAt
  rw [h1]
  rw [one_div_add_one_div]
  simp only [neg_mul, sub_add_add_cancel]
  rw [← neg_div_neg_eq]
  simp only [neg_neg, neg_sub]
  congr
  ring
  norm_cast
  simp
  ring
  have := upper_ne_nat x (n + 1)
  rw [sub_ne_zero]
  simpa using this
  have := upper_ne_int x (n + 1)
  norm_cast at *

theorem upper_half_ne_nat_pow_two (z : ℍ) : ∀ n : ℕ, (z : ℂ) ^ 2 ≠ n ^ 2 :=
  by
  intro n
  have := upper_half_plane_ne_int_pow_two z n
  simp at this
  norm_cast at *
  rw [sub_eq_zero] at this
  norm_cast 


theorem factor_ne_zero (x : ℍ) (n : ℕ) : (1 : ℂ) - x ^ 2 / (n + 1) ^ 2 ≠ 0 :=
  by
  by_contra h
  rw [sub_eq_zero] at h 
  have hs := h.symm
  rw [div_eq_one_iff_eq] at hs 
  have hr := upper_half_ne_nat_pow_two x (n + 1)
  simp only [Nat.cast_add, algebraMap.coe_one, Ne.def] at *
  norm_cast at *
  norm_cast
  apply pow_ne_zero
  norm_cast
  linarith

theorem DifferentiableOn.product (F : ℕ → ℂ → ℂ) (n : ℕ) (s : Set ℂ)
    (hd : ∀ i : Finset.range n, DifferentiableOn ℂ (fun z => F i z) s) :
    DifferentiableOn ℂ (fun z => ∏ i in Finset.range n, F i z) s :=
  by
  induction' n with n n_ih
  simp
  apply differentiableOn_const
  simp_rw [Finset.prod_range_succ]
  apply DifferentiableOn.mul
  apply n_ih
  intro i
  simp at *
  apply hd
  norm_cast
  have hi := i.2
  norm_cast at hi
  rw [Finset.mem_range] at hi
  apply lt_trans hi
  apply Nat.lt_succ_self
  simp at *
  apply hd
  apply Nat.lt_succ_self

theorem prod_diff_on' (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) ℍ' :=
  by
  apply DifferentiableOn.product
  intro i
  apply DifferentiableOn.sub
  apply differentiableOn_const
  apply DifferentiableOn.div_const
  norm_cast
  apply DifferentiableOn.pow
  apply differentiable_id.differentiableOn

theorem product_diff_on_H (n : ℕ) :
    DifferentiableOn ℂ (fun z => ↑π * (z : ℂ) * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))
      ℍ' :=
  by
  apply DifferentiableOn.mul
  apply DifferentiableOn.const_mul
  apply differentiable_id.differentiableOn
  apply prod_diff_on'

theorem logDeriv_of_prod (x : ℍ) (n : ℕ) :
    logDeriv (fun z => ↑π * z * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) x =
      1 / x + ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))) :=
  by
  rw [log_derv_mul]
  rw [logDeriv_pi_z]
  simp only [one_div, add_right_inj]
  have := logDeriv_prod (Finset.range n) fun n : ℕ => fun z : ℂ => 1 - z ^ 2 / (n + 1) ^ 2
  simp at this 
  rw [← Finset.prod_fn]
  norm_cast at *
  rw [this]
  have :=logDeriv_eq_1 x n
  norm_cast at *
  simp at *
  congr
  ext1 y
  have :=logDeriv_eq_1 x y
  simp at this
  norm_cast at *
  intro m _
  have := factor_ne_zero x m
  norm_cast at *
  swap
  apply mul_ne_zero
  apply mul_ne_zero
  norm_cast
  apply Real.pi_ne_zero
  apply UpperHalfPlane.ne_zero x
  rw [Finset.prod_ne_zero_iff]
  intro a _
  apply factor_ne_zero x a
  intro m _
  apply DifferentiableAt.div_const
  apply DifferentiableAt.pow
  apply differentiable_id.differentiableAt
  apply DifferentiableAt.const_mul
  apply differentiable_id.differentiableAt
  apply DifferentiableOn.differentiableAt
  apply (prod_diff_on' n)
  apply isOpen_iff_mem_nhds.1
  apply upper_half_plane_isOpen
  apply x.2

theorem prod_be_exp (f : ℕ → ℂ) (s : Finset ℕ) :
    ∏ i in s, (1 + Complex.abs (f i)) ≤ Real.exp (∑ i in s, Complex.abs (f i)) :=
  by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  intro i _
  apply add_nonneg
  linarith
  apply Complex.abs.nonneg
  intro i _
  rw [add_comm]
  apply Real.add_one_le_exp_of_nonneg (Complex.abs.nonneg _)

theorem prod_le_prod_abs (f : ℕ → ℂ) (n : ℕ) :
    Complex.abs (∏ i in Finset.range n, (f i + 1) - 1) ≤
      ∏ i in Finset.range n, (Complex.abs (f i) + 1) - 1 :=
  by
  induction' n with h n_ih
  simp  [Finset.range_zero, Finset.prod_empty, sub_self, AbsoluteValue.map_zero]
  have HH :
    ∏ i in Finset.range (h + 1 ), (f i + 1) - 1 =
      (∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1) + f h :=
    by
    simp_rw [Finset.prod_range_succ]
    ring
  rw [HH]
  have H3 :
    Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1) + f h) ≤
      Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1)) + Complex.abs (f h) :=
    by
    apply le_trans (Complex.abs.add_le _ _)
    simp 
  apply le_trans H3
  have H4 :
    Complex.abs ((∏ i in Finset.range h, (f i + 1) - 1) * (f h + 1)) + Complex.abs (f h) ≤
      (∏ i in Finset.range h, (Complex.abs (f i) + 1) - 1) * (Complex.abs (f h) + 1) +
        Complex.abs (f h) :=
    by
    simp only [AbsoluteValue.map_mul, add_le_add_iff_right]
    have h1 :
      Complex.abs (∏ i in Finset.range h, (f i + 1) - 1) ≤
        ∏ i in Finset.range h, (Complex.abs (f i) + 1) - 1 :=
      by apply n_ih
    have h2 : Complex.abs (f h + 1) ≤ Complex.abs (f h) + 1 :=
      by
      apply le_trans (Complex.abs.add_le _ _)
      simp [AbsoluteValue.map_one]
    apply mul_le_mul h1 h2
    apply Complex.abs.nonneg
    apply le_trans _ n_ih
    apply Complex.abs.nonneg
  apply le_trans H4
  ring_nf
  rw [Finset.prod_range_succ]
  rw [mul_comm]
  simp
  norm_cast
  simp
  linarith


--rw ←finset.prod_range_mul_prod_Ico
theorem prod_le_prod_abs_Ico (f : ℕ → ℂ) (n m : ℕ) :
    Complex.abs (∏ i in Finset.Ico m n, (f i + 1) - 1) ≤
      ∏ i in Finset.Ico m n, (Complex.abs (f i) + 1) - 1 :=
  by
  simp_rw [Finset.prod_Ico_eq_prod_range]
  apply prod_le_prod_abs

theorem prod_le_prod_abs_Ico_ond_add (f : ℕ → ℂ) (n m : ℕ) :
    Complex.abs (∏ i in Finset.Ico m n, (1 + f i) - 1) ≤
      ∏ i in Finset.Ico m n, (1 + Complex.abs (f i)) - 1 :=
  by
  have := prod_le_prod_abs_Ico f n m
  norm_cast at *
  simp at *
  have h:(∏ i in Finset.Ico m n, (1 + f i) - 1) =(∏ i in Finset.Ico m n, (f i+ 1) - 1) := by 
    congr
    ext1
    ring
  rw [h]
  have h2 : ∏ x in Finset.Ico m n, (1 + Complex.abs (f x)) - 1 = ∏ x in Finset.Ico m n, 
    (Complex.abs (f x)+1) - 1 := by 
    congr
    ext1
    ring
  rw [h2]
  apply this

theorem unif_prod_bound (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (x : ℂ), x ∈ K → ∏ i in s, (1 + Complex.abs (F i x)) ≤ C :=
  by
  obtain ⟨T, ht⟩ := hb
  have HB :
    ∀ (s : Finset ℕ) (a : ℂ), ∑ i in s, Complex.abs (F i a) ≤ ∑' n : ℕ, Complex.abs (F n a) :=
    by
    intro n a
    apply sum_le_tsum
    intro b _
    apply Complex.abs.nonneg
    apply hs a
  have hexp : 0 < Real.exp T := by have := Real.exp_pos T; apply this
  refine' ⟨Real.exp T, _⟩
  simp [hexp]
  intro n x hx
  apply le_trans (prod_be_exp _ _)
  simp
  apply le_trans (HB n x)
  exact ht x hx

theorem fin_prod_le_exp_sum (F : ℕ → ℂ → ℂ)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∀ (s : Finset ℕ) (x : ℂ),
      ∏ i in s, (1 + Complex.abs (F i x)) ≤ Real.exp (∑' i : ℕ, Complex.abs (F i x)) :=
  by
  have HB :
    ∀ (s : Finset ℕ) (a : ℂ), ∑ i in s, Complex.abs (F i a) ≤ ∑' n : ℕ, Complex.abs (F n a) :=
    by
    intro n a
    apply sum_le_tsum
    intro b _
    apply Complex.abs.nonneg
    apply hs a
  intro s x
  apply le_trans (prod_be_exp _ _)
  simp
  apply HB s x

theorem tsum_unif (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N : ℕ,
          ∀ (n : ℕ) (x : ℂ),
            x ∈ K → N ≤ n → Complex.abs (∑' i : ℕ, Complex.abs (F (i + N) x)) < ε :=
  by
  rw [Metric.tendstoUniformlyOn_iff] at hf 
  simp at hf 
  intro ε hε
  have HF := hf ε hε
  obtain ⟨N, hN⟩ := HF
  refine' ⟨N, _⟩
  intro n x hx _
  have hnn : N ≤ N := by rfl
  have HN2 := hN N hnn x hx
  simp_rw [dist_eq_norm] at *
  convert HN2
  rw [tsum_coe]
  rw [← norm_eq_abs]
  rw [Complex.norm_real]
  congr
  have hy := sum_add_tsum_nat_add N (hs x)
  simp at hy 
  rw [← hy]
  ring

theorem abs_tsum_of_poss (F : ℕ → ℂ → ℝ) (h : ∀ (n : ℕ) (c : ℂ), 0 ≤ F n c) :
    ∀ x : ℂ, |∑' i : ℕ, F i x| = ∑' i : ℕ, F i x :=
  by
  intro x
  simp only [abs_eq_self]
  apply tsum_nonneg
  intro b
  apply h b x

theorem abs_tsum_of_pos (F : ℕ → ℂ → ℂ) :
    ∀ (x : ℂ) (N : ℕ),
      Complex.abs (∑' i : ℕ, Complex.abs (F (i + N) x) : ℂ) = ∑' i : ℕ, Complex.abs (F (i + N) x) :=
  by
  intro x N
  have := abs_tsum_of_poss (fun n : ℕ => fun x : ℂ => Complex.abs (F (n + N) x)) ?_ x
  rw [← this]
  simp
  rw [←Complex.abs_ofReal _]
  congr
  rw [tsum_coe]
  intro n c
  apply Complex.abs.nonneg

theorem add_eq_sub_add (a b c d : ℝ) : b = c - a + d ↔ a + b = c + d :=
  by
  constructor
  repeat'
    intro h
    linarith [h]

theorem sum_subtype_le_tsum (f : ℕ → ℝ) (m n N : ℕ) (hmn : m ≤ n ∧ N ≤ m) (hg : ∀ b, 0 ≤ f b)
    (hf : Summable f) : ∑ i : ℕ in Finset.Ico m n, f i ≤ ∑' i : ℕ, f (i + N) :=
  by
  have h1 : ∑ i : ℕ in Finset.Ico m n, f i ≤ ∑ i : ℕ in Finset.Ico N n, f i :=
    by
    have := Finset.Ico_union_Ico_eq_Ico hmn.2 hmn.1
    rw [← this]
    rw [Finset.sum_union]
    simp
    apply Finset.sum_nonneg
    intro i _
    apply hg i
    exact Finset.Ico_disjoint_Ico_consecutive N m n
  apply le_trans h1
  have h2 : ∑' i : ℕ, f (i + N) = ∑ i : ℕ in Finset.Ico N n, f i + ∑' i : ℕ, f (i + n) :=
    by
    have hh1 := sum_add_tsum_nat_add N hf
    have hh2 := sum_add_tsum_nat_add n hf
    rw [← hh2] at hh1 
    rw [← add_eq_sub_add] at hh1 
    rw [hh1]
    simp
    have hNn : N ≤ n := le_trans hmn.2 hmn.1
    have := Finset.sum_range_add_sum_Ico f hNn
    rw [← this]
    simp
  rw [h2]
  simp
  apply tsum_nonneg
  intro b
  apply hg (b + n)

theorem tsum_unifo (F : ℕ → ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x)) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N : ℕ,
          ∀ (n m : ℕ) (x : ℂ),
            x ∈ K →
              N ≤ n ∧ N ≤ m ∧ m ≤ n → ∏ i in Finset.Ico m n, (1 + Complex.abs (F i x)) - 1 ≤ ε :=
  by
  intro ε hε
  have hl : 0 < Real.log (1 + ε) := by apply Real.log_pos; linarith
  have H2 := tsum_unif F K hf hs (Real.log (1 + ε)) hl
  obtain ⟨N, hN⟩ := H2
  use N
  intro n m x hK h
  have HN2 := hN n x hK h.1
  apply le_trans (sub_le_sub_right (prod_be_exp _ _) 1)
  rw [← Real.exp_lt_exp] at HN2 
  have hll : 0 < 1 + ε := by linarith
  rw [Real.exp_log hll] at HN2 
  rw [tsub_le_iff_left]
  apply le_trans _ HN2.le
  simp
  have hss : Summable fun n : ℕ => Complex.abs (F (n + N) x) :=
    by
    have := hs x
    rw [← summable_nat_add_iff N] at this 
    apply this
  have := abs_tsum _ hss
  rw [abs_tsum_of_pos F x N]
  have := sum_add_tsum_nat_add N (hs x)
  apply sum_subtype_le_tsum
  constructor
  apply h.2.2
  apply h.2.1
  intro b
  apply Complex.abs.nonneg
  exact hs x

theorem auxreal (e : ℂ) : Complex.abs (1 - e) = Complex.abs (e - 1) :=
  map_sub_rev Complex.abs 1 e

theorem sum_prod_unif_conv (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : Set ℂ)
    (hf :
      TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∑ i in Finset.range n, Complex.abs (F i a))
        (fun a : ℂ => ∑' n : ℕ, Complex.abs (F n a)) Filter.atTop K)
    (hb : ∃ T : ℝ, ∀ x : ℂ, x ∈ K → ∑' n : ℕ, Complex.abs (F n x) ≤ T)
    (hs : ∀ x : ℂ, Summable fun n : ℕ => Complex.abs (F n x))
    (hp :
      ∀ x : ℂ, x ∈ K → Tendsto (fun n : ℕ => ∏ i in Finset.range n, (1 + F i x)) atTop (𝓝 (g x))) :
    TendstoUniformlyOn (fun n : ℕ => fun a : ℂ => ∏ i in Finset.range n, (1 + F i a)) g Filter.atTop
      K :=
  by
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have H := tsum_unifo F K hf hs
  have H2 := unif_prod_bound F K hb hs
  obtain ⟨C, hCp, hC⟩ := H2
  have hdelta := exists_pos_mul_lt hε C
  obtain ⟨δ, hδ⟩ := hdelta
  have HH := H δ hδ.1
  obtain ⟨N, HN⟩ := HH
  refine' ⟨N, _⟩
  intro n hn m hm x hx
  have hCm := hC (Finset.range m) x
  have hCn := hC (Finset.range n) x
  rw [dist_eq_norm]
  simp only [norm_eq_abs]
  by_cases hmn : m ≤ n
  rw [← Finset.prod_range_mul_prod_Ico _ hmn]
  rw [← mul_sub_one]
  simp only [AbsoluteValue.map_mul, abs_prod]
  have A : ∏ i : ℕ in Finset.range m, Complex.abs (1 + F i x) ≤ C :=
    by
    apply le_trans _ (hCm hx)
    apply Finset.prod_le_prod
    intro i _
    apply Complex.abs.nonneg
    intro i _
    apply le_trans (Complex.abs.add_le _ _)
    simp 
  have B : Complex.abs (∏ i : ℕ in Finset.Ico m n, (1 + F i x) - 1) ≤ δ :=
    by
    have HI := HN n m x hx
    simp only [and_imp] at HI 
    have HI2 := HI hn hm hmn
    have := prod_le_prod_abs_Ico_ond_add (fun i : ℕ => F i x) n m
    simp at this 
    apply le_trans this
    exact HI2
  have AB := mul_le_mul A B ?_ hCp.le
  apply lt_of_le_of_lt AB
  apply hδ.2
  apply Complex.abs.nonneg
  simp at hmn 
  rw [← Finset.prod_range_mul_prod_Ico _ hmn.le]
  rw [← mul_one_sub]
  simp 
  have A : ∏ i : ℕ in Finset.range n, Complex.abs (1 + F i x) ≤ C :=
    by
    apply le_trans _ (hCn hx)
    apply Finset.prod_le_prod
    intro i _
    apply Complex.abs.nonneg
    intro i _
    apply le_trans (Complex.abs.add_le _ _)
    simp 
  have B : Complex.abs (∏ i : ℕ in Finset.Ico n m, (1 + F i x) - 1) ≤ δ :=
    by
    have HI := HN m n x hx
    simp only [and_imp] at HI 
    have HI2 := HI hm hn hmn.le
    have := prod_le_prod_abs_Ico_ond_add (fun i : ℕ => F i x) m n
    simp at this 
    apply le_trans this
    exact HI2
  have AB := mul_le_mul A B ?_ hCp.le
  rw [auxreal _]
  apply lt_of_le_of_lt AB
  apply hδ.2
  apply Complex.abs.nonneg
  exact hp

theorem tendsto_unif_on_restrict (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (K : Set ℂ) :
    TendstoUniformlyOn f g atTop K ↔
      TendstoUniformly (fun n : ℕ => fun k : K => f n k) (fun k : K => g k) atTop :=
  by
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformlyOn_iff]
  simp

theorem tendst_unif_coe (K : Set ℂ) (f : ℕ → K → ℝ) (g : K → ℝ) :
    TendstoUniformly (fun n : ℕ => fun k : K => (f n k : ℂ)) (fun n : K => (g n : ℂ)) atTop ↔
      TendstoUniformly (fun n : ℕ => fun k : K => f n k) (fun k : K => g k) atTop :=
  by
  simp_rw [Metric.tendstoUniformly_iff]
  simp_rw [dist_eq_norm] at *
  simp
  constructor
  repeat'
  intro h
  intro e he
  have hh := h e he
  obtain ⟨a, ha⟩ := hh
  refine' ⟨a, _⟩
  intro b hb x hx
  have H := ha b hb x hx
  convert H
  simp
  rw [← Complex.abs_ofReal _]
  congr
  simp only [Complex.ofReal_sub]

    
--was called assa
theorem ball_abs_le_center_add_rad (r : ℝ) (z : ℂ) (x : ball z r) : Complex.abs x < Complex.abs z + r :=
  by
  have hx : (x : ℂ) = x - z + z := by ring
  rw [hx]
  apply lt_of_le_of_lt (Complex.abs.add_le (x - z) z)
  norm_cast
  simp
  rw [add_comm]
  simp only [add_lt_add_iff_left]
  have hxx := x.2
  simp  at hxx 
  rw [dist_eq_norm] at hxx 
  norm_cast at *
  

theorem summable_rie_twist (x : ℂ) : Summable fun n : ℕ => Complex.abs (x ^ 2 / (↑n + 1) ^ 2) :=
  by
  simp
  simp_rw [div_eq_mul_inv]
  apply Summable.mul_left
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2)⁻¹ :=
    by
    norm_cast
    simp
    have h2 : (1 : ℤ) < 2 := by linarith
    have := int_RZ_is_summmable 2 h2
    simp_rw [rie] at this 
    rw [← summable_nat_add_iff 1] at this 
    norm_cast at this 
    simpa using this
  apply Summable.congr hs
  intro b
  simp
  rw [← Complex.abs_pow]
  have := Complex.abs_of_nat ((b+1)^2)
  symm
  simp at *
  norm_cast at *

theorem rie_twist_bounded_on_ball (z : ℂ) (r : ℝ) :
    ∃ T : ℝ, ∀ x : ℂ, x ∈ ball z r → ∑' n : ℕ, Complex.abs (-x ^ 2 / (↑n + 1) ^ 2) ≤ T :=
  by
  refine' ⟨∑' n : ℕ, (Complex.abs z + r) ^ 2 / Complex.abs ((n + 1) ^ 2), _⟩
  intro x hx
  simp only [map_div₀, AbsoluteValue.map_neg, Complex.abs_pow]
  have := summable_rie_twist x
  apply tsum_le_tsum
  intro b
  simp only
  apply div_le_div_of_le
  norm_cast
  apply Complex.abs.nonneg 
  simp
  apply pow_le_pow_of_le_left
  apply Complex.abs.nonneg
  apply (ball_abs_le_center_add_rad r z ⟨x, hx⟩).le
  convert this
  field_simp
  simp_rw [div_eq_mul_inv]
  apply Summable.mul_left
  convert summable_rie_twist (1 : ℂ)
  field_simp

theorem euler_sin_prod' (x : ℂ) (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) atTop
      (𝓝 ((fun t : ℂ => sin (↑π * t) / (↑π * t)) x)) :=
  by
  have := tendsto_euler_sin_prod x
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  have hh : ↑π * x ≠ 0 := by apply mul_ne_zero; norm_cast; apply Real.pi_ne_zero; apply h0
  have hex : 0 < ε * Complex.abs (π * x) := by 
    apply mul_pos; apply hε; apply Complex.abs.pos;
    apply hh
  have h1 := this (ε * Complex.abs (π * x)) hex
  obtain ⟨N, hN⟩ := h1
  refine' ⟨N, _⟩
  intro n hn
  have h2 := hN n hn
  simp
  rw [dist_eq_norm] at *
  have :
    ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x) / (↑π * x) =
      (↑π * x * ∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x)) / (↑π * x) :=
    by
    have :=
      sub_div' (sin (↑π * x)) (∏ i : ℕ in Finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) (↑π * x) hh
    simp at *
    rw [this]
    ring
  norm_cast at *  
  rw [this]
  field_simp
  rw [div_lt_iff]
  simp at * 
  norm_cast at *
  have hr : Complex.abs ((↑π * x * ∏ x_1 in Finset.range n, (1 + -x ^ 2 / (((x_1 + 1) : ℕ) ^ 2))) 
    - sin (↑π * x)) =
    Complex.abs ((↑π * x * ∏ x_1 in Finset.range n, (1 -x ^ 2 / ((x_1 + 1) ^ 2)) - sin (↑π * x)) ):= 
    by 
      congr
      ext1
      norm_cast
      ring
  norm_cast at *
  simp at *
  rw [hr] 
  convert h2
  apply mul_pos
  simpa using Real.pi_ne_zero
  apply Complex.abs.pos
  exact h0

theorem tendsto_locally_uniformly_euler_sin_prod' (z : ℍ') (r : ℝ) (hr : 0 < r) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℂ => ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2))
      (fun t => Complex.sin (π * t) / (↑π * t)) atTop (ball z r ∩ ℍ') :=
  by
  apply sum_prod_unif_conv _ (fun t => Complex.sin (π * t) / (↑π * t)) (ball z r ∩ ℍ')
  rw [tendsto_unif_on_restrict _ _ (ball z r ∩ ℍ')]
  simp only [map_div₀, AbsoluteValue.map_neg, Complex.abs_pow]
  set s : ℝ := Complex.abs z + r
  have HH :=
    M_test_uniform ?_ (fun (n : ℕ) (x : ((ball z r ∩ ℍ'): Set ℂ)) => Complex.abs (x ^ 2 / (n + 1) ^ 2))
      (fun n : ℕ => Complex.abs (s ^ 2 / (n + 1) ^ 2)) ?_ ?_
  rw [← tendst_unif_coe _ _ _]
  convert HH
  simp only [coe_finset_sum', map_div₀, Complex.abs_pow]
  funext
  rw [tsum_coe]
  congr
  simp only [map_div₀, Complex.abs_pow]
  simp [hr, nonempty_coe_sort, nonempty_ball]
  refine' ⟨z, _⟩
  simp [hr, z.2]
  intro n x
  simp only [map_div₀, Complex.abs_pow, ofReal_div, ofReal_pow, abs_ofReal, Complex.abs_abs,
    ofReal_add]
  apply div_le_div_of_le
  apply Complex.abs.nonneg
  norm_cast
  rw [ Complex.abs_pow]
  simp
  apply pow_le_pow_of_le_left (Complex.abs.nonneg _)
  have hxx : (x : ℂ) ∈ ball (z : ℂ) r := by have := x.2; rw [mem_inter_iff] at this ; apply this.1
  have A := ball_abs_le_center_add_rad r z (⟨x, hxx⟩ : ball (z : ℂ) r)
  simp at *
  apply le_trans A.le
  norm_cast
  apply summable_rie_twist s
  have B := rie_twist_bounded_on_ball z.1 r 
  obtain ⟨T, hT⟩ := B
  refine' ⟨T, _⟩
  intro x hx
  apply hT x
  rw [mem_inter_iff] at hx 
  apply hx.1
  intro x
  have HH := summable_rie_twist x
  apply HH.congr
  intro b
  norm_cast
  norm_num
  intro x hx
  have := euler_sin_prod' x
  apply this
  rw [mem_inter_iff] at hx 
  apply UpperHalfPlane.ne_zero (⟨x, hx.2⟩ : ℍ)

theorem sub_add_prod_aux (n : ℕ) (z : ℂ) :
    ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2) =
      ∏ j in Finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2) :=
  by
  congr
  ext1
  ring

theorem aux_ineq (ε : ℝ) (hε : 0 < ε) (x y : ℍ) (hxy : Complex.abs (y - x) < ε) :
    ε / (|π| * Complex.abs x + |π| * ε) * (|π| * Complex.abs y) < ε :=
  by
  have :
    ε / (|π| * Complex.abs x + |π| * ε) * (|π| * Complex.abs y) =
      ε * (|π| * Complex.abs y / (|π| * Complex.abs x + |π| * ε)) :=
    by field_simp
  rw [this]
  have hp : 0 < |π| := by rw [abs_pos]; exact Real.pi_ne_zero
  have h1 : |π| * Complex.abs y / (|π| * Complex.abs x + |π| * ε) < 1 :=
    by
    rw [div_lt_one]
    rw [← mul_add]
    have hh : Complex.abs ↑y < Complex.abs ↑x + ε :=
      by
      have := ball_abs_le_center_add_rad ε (x : ℂ)
      simp at this 
      apply this y
      simpa using hxy
    nlinarith
    rw [← mul_add]
    apply mul_pos
    exact hp
    exact lt_add_of_le_of_pos (Complex.abs.nonneg x) hε
  apply mul_lt_of_lt_one_right hε h1

theorem sin_pi_z_ne_zero (z : ℍ) : Complex.sin (π * z) ≠ 0 :=
  by
  apply Complex.sin_ne_zero_iff.2
  intro k
  rw [mul_comm]
  by_contra h
  simp at h 
  cases' h with h h
  have hk : (k : ℂ).im = 0 := by simp
  have hz : 0 < (z : ℂ).im := by simpa using z.2
  simp only [uhc] at hz
  rw [h, hk] at hz 
  simp at hz
  have := Real.pi_ne_zero
  exact this h

theorem tendsto_euler_log_derv_sin_prodd (x : ℍ) :
    Tendsto
      (fun n : ℕ =>
        logDeriv (fun z => ↑π * (z : ℂ) * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) x)
      atTop (𝓝 <| logDeriv (Complex.sin ∘ fun t => π * t) x) :=
  by
  have :=
    logDeriv_tendsto
      (fun n : ℕ => fun z => ↑π * (z : ℂ) * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))
      (Complex.sin ∘ fun t => π * t) ℍ' upper_half_plane_isOpen x
  apply this
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have H := tendsto_locally_uniformly_euler_sin_prod' ⟨x, hx⟩ ε hε
  rw [Metric.tendstoUniformlyOn_iff] at H 
  have hxe : 0 < ε / (Complex.abs (π * x) + |π| * ε) :=
    by
    apply div_pos hε
    simp
    rw [← mul_add]
    apply mul_pos
    · rw [abs_pos]; exact Real.pi_ne_zero
    exact lt_add_of_le_of_pos (Complex.abs.nonneg x) hε
  have HH := H (ε / (Complex.abs (π * x) + |π| * ε)) hxe
  refine' ⟨ball x ε ∩ ℍ', _⟩
  simp  [Subtype.coe_mk ge_iff_le, mem_inter_iff, mem_ball,
    and_imp, exists_prop, Ne.def, forall_exists_index, gt_iff_lt] at *
  constructor
  rw [Metric.mem_nhdsWithin_iff]
  constructor
  norm_cast 
  simp
  use ε
  simp [hε]
  exact self_mem_nhdsWithin  
  obtain ⟨N, hN⟩ := HH
  refine' ⟨N, _⟩
  intro b hb y hy hyy
  have := hN b hb y hy hyy
  rw [dist_eq_norm] at *
  rw [div_sub'] at this 
  simp only [norm_eq_abs, Subtype.coe_mk, AbsoluteValue.map_mul, abs_ofReal, map_div₀] at *
  rw [div_lt_iff] at this 
  have htest := sub_add_prod_aux b y
  norm_cast at *
  rw [htest]
  apply lt_trans this
  apply aux_ineq ε hε ⟨x, hx⟩ ⟨y, hyy⟩ hy
  apply mul_pos
  · rw [abs_pos]; exact Real.pi_ne_zero
  · apply Complex.abs.pos; apply UpperHalfPlane.ne_zero ⟨y, hyy⟩
  apply mul_ne_zero
  norm_cast
  apply Real.pi_ne_zero
  apply UpperHalfPlane.ne_zero ⟨y, hyy⟩
  simp  
  refine' ⟨1, _⟩
  intro b _
  have := product_diff_on_H b
  norm_cast at *
  simp 
  exact sin_pi_z_ne_zero x

theorem tendsto_euler_log_derv_sin_prodd' (x : ℍ) :
    Tendsto
      (fun n : ℕ => 1 / (x : ℂ) + ∑ j in Finset.range n, (1 / ((x : ℂ) - (j + 1)) + 1 / (x + (j + 1))))
      atTop (𝓝 <| π * cot (π * x)) :=
  by
  have := tendsto_euler_log_derv_sin_prodd x
  have h1 := logDeriv_of_prod x
  have h2 := logDeriv_sine x
  rw [← h2]
  simp_rw [← h1]
  simp at *
  exact this

theorem cot_series_rep' (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ, (1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1))) :=
  by
  rw [HasSum.tsum_eq _]
  rw [Summable.hasSum_iff_tendsto_nat]
  have h := tendsto_euler_log_derv_sin_prodd' z
  have := Tendsto.sub_const h (1 / (z : ℂ))
  simp at *
  apply this
  have H := lhs_summable z
  have HH := nat_pos_tsum2' fun n => 1 / ((z : ℂ) - n) + 1 / (z + n)
  simp at *
  rw [← HH]
  exact H

theorem cot_series_rep (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) :=
  by
  have := tsum_pnat' fun n => 1 / ((z: ℂ) - n) + 1 / (z + n)
  have h1 := cot_series_rep' z
  simp [one_div, Nat.cast_add, algebraMap.coe_one] at *
  rw [this]
  apply h1

