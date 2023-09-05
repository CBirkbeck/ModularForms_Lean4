import Modformsported.ForMathlib.ModForms2  
import Modformsported.ModForms.HolomorphicFunctions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.NumberTheory.Modular
import Mathlib.GroupTheory.Index
import Modformsported.ForMathlib.EisensteinSeries.ModularForm
import Mathlib.Analysis.Calculus.Inverse



/-!
# q-expansions of periodic functions

We show that if `f : ℂ → ℂ` satisfies `f(z + h) = f(z)`, for some nonzero real `h`, then
there is a well-defined `F` such that `f(z) = F(exp(2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `q = exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero.
-/


open ModularForm Complex Filter Asymptotics

open scoped Real Topology Manifold Filter

noncomputable section

abbrev ℝPos :=
  { u : ℝ // 0 < u }

instance : One ℝPos := by 
  use 1
  linarith

/-- Function-theoretic lemma, maybe move this elsewhere? -/
theorem bound_holo_fcn (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) (hg' : g 0 = 0) :
    IsBigO (𝓝 0) g id := by 
    replace hg := hg.hasDerivAt.isBigO_sub
    simp_rw [hg', sub_zero] at hg ;
    exact hg

section QAndZ

variable (h : ℝPos)

def Q (z : ℂ) : ℂ :=
  exp (2 * π * I * z / h)

def Z (q : ℂ) : ℂ :=
  h / (2 * π * I) * log q

theorem log_exp' (z : ℂ) : ∃ n : ℤ, log (exp z) = z + n * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_log]; exact exp_ne_zero z



theorem QZ_eq_id (e : ℂ) (hq : e ≠ 0) : Q h (Z h e) = e :=
  by
  dsimp only [Q, Z]
  suffices 2 * ↑π * I * (↑h / (2 * ↑π * I) * log e) / ↑h = log e by rw [this]; exact exp_log hq
  have : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr h.2.ne'
  field_simp [two_pi_I_ne_zero, this]; ring

theorem abs_q_eq (z : ℂ) : abs (Q h z) = Real.exp (-2 * π * im z / h) :=
  by
  dsimp only [Q]; rw [abs_exp]; congr
  rw [div_eq_mul_inv, mul_comm]
  have : (↑h)⁻¹ = (↑(h : ℝ)⁻¹ : ℂ) := by simp; 
  rw [this]
  rw [ofReal_mul_re]
  have : 2 * ↑π * I * z = ↑(2 * π) * z * I := by simp; ring
  rw [this, mul_I_re, ofReal_mul_im]; field_simp [h.2.ne']

theorem im_z_eq (q : ℂ) : im (Z h q) = -h / (2 * π) * Real.log (abs q) :=
  by
  dsimp only [Z]
  have : ↑h / (2 * ↑π * I) * log q = -↑h / (2 * ↑π) * log q * I := by
    field_simp [ofReal_ne_zero.mpr Real.pi_pos.ne', two_pi_I_ne_zero]; ring_nf; simp
  rw [this, mul_I_im]
  have : -↑h / (2 * ↑π) * log q = ↑(-↑h / (2 * π)) * log q := by simp
  rw [this, ofReal_mul_re, log_re]

theorem ZQ_eq_mod_period (s : ℂ) : ∃ m : ℤ, Z h (Q h s) = s + m * h :=
  by
  dsimp only [Q, Z]
  have t := log_exp' (2 * ↑π * I * s / ↑h)
  cases' t with m t; use m; rw [t]
  have : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr h.2.ne'
  field_simp [two_pi_I_ne_zero]; ring

theorem abs_q_lt_iff (A : ℝ) (z : ℂ) : abs (Q h z) < Real.exp (-2 * π * A / h) ↔ A < im z :=
  by
  rw [abs_q_eq, Real.exp_lt_exp]
  constructor
  · intro hz; rw [div_lt_div_right] at hz ; swap; exact h.2
    have : -2 * π < 0 := by simpa using Real.pi_pos
    rwa [mul_lt_mul_left_of_neg this] at hz 
  · intro hz; rw [div_lt_div_right]; swap; exact h.2
    have : -2 * π < 0 := by simpa using Real.pi_pos
    rwa [mul_lt_mul_left_of_neg this]

-- Filter stuff
def atIInf' : Filter ℂ :=
  atTop.comap im

theorem atIInf'_mem (S : Set ℂ) : S ∈ atIInf' ↔ ∃ A : ℝ, ∀ z : ℂ, A < im z → z ∈ S :=
  by
  rw [atIInf', mem_comap', Filter.mem_atTop_sets]
  simp; constructor
  · intro h; cases' h with a h; use a
    intro z hz; specialize h (im z) hz.le; apply h; rfl
  · intro h; cases' h with A h; use A + 1
    intro b hb x hx; apply h x; rw [hx]; linarith

theorem z_tendsto : Tendsto (Z h) (𝓝[{0}ᶜ] 0) atIInf' :=
  by
  rw [Tendsto, map_le_iff_le_comap, comap]
  intro S h; simp_rw [atIInf'_mem] at h ; obtain ⟨T, ⟨A, hA⟩, hT⟩ := h
  simp_rw [Metric.mem_nhdsWithin_iff, Metric.ball, dist_eq, sub_zero]
  use Real.exp (-2 * π * A / h); constructor; apply Real.exp_pos
  intro q; dsimp; rintro ⟨u1, u2⟩
  rw [← QZ_eq_id h _ u2] at u1 ; 
  have := abs_q_lt_iff h A (Z h q)
  simp at *
  rw [this] at u1
  simp at u1
  specialize hA (Z h q) u1
  apply hT; exact hA

theorem q_tendsto : Tendsto (Q h) atIInf' (𝓝 0) :=
  by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_eq_abs, abs_q_eq]
  have : Set.range im ∈ atTop :=
    by
    suffices Set.range im = ⊤ by rw [this]; apply univ_mem
    ext1 x; simp only [Set.mem_range, Set.top_eq_univ, Set.mem_univ, iff_true_iff]
    use I * x; simp
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (fun y => Real.exp (-2 * π * y / ↑h)) atTop (𝓝 0) im this).mpr
  apply this; refine' Real.tendsto_exp_atBot.comp _
  apply Filter.Tendsto.atBot_div_const h.2
  apply Filter.Tendsto.neg_const_mul_atTop; · simpa using Real.pi_pos; 
  apply tendsto_id

end QAndZ

section PeriodicOnC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

def cuspFcn0 : ℂ → ℂ := fun q => f (Z h q)

def cuspFcn : ℂ → ℂ :=
  Function.update (cuspFcn0 h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn0 h f))

theorem cuspFcn_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) : (cuspFcn h f) q = (cuspFcn0 h f) q :=
  by
  rw [cuspFcn, Function.update]; split_ifs 
  · exfalso; norm_cast at *
  · rfl

theorem update_twice :
    cuspFcn h f = Function.update (cuspFcn h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn h f)) :=
  by
  ext1 q; rw [Function.update]; split_ifs
  · rw [cuspFcn, Function.update]; split_ifs
    rw [limUnder, limUnder]
    simp
    congr 1
    apply Filter.map_congr; apply eventuallyEq_nhdsWithin_of_eqOn
    intro r hr; simp at hr 
    rw [Function.update]; split_ifs; rfl
    norm_cast at *
  · rfl

private theorem is_periodic_aux (z : ℂ) (m : ℕ) : f (z + m * h) = f z :=
  by
  induction' m with m hm generalizing z; simp
  rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul, ← add_assoc, one_mul]
  rw [hf (z + m * h)]; exact hm z

theorem is_periodic (z : ℂ) (m : ℤ) : f (z + m * h) = f z :=
  by
  cases' m with m m; · exact is_periodic_aux h f hf z m
  simp only [neg_add_rev, Int.cast_negSucc]
  norm_cast at *
  simp at *
  have :=(is_periodic_aux h f hf (z - (m + 1) * h) (m + 1)).symm
  norm_cast at *
  simp at *
  rw [←this]
  apply congr_arg
  ring

theorem eq_cuspFcn (z : ℂ) : f z = (cuspFcn h f) (Q h z) :=
  by
  have : (cuspFcn h f) (Q h z) = (cuspFcn0 h f) (Q h z) :=
    by
    rw [cuspFcn]; rw [Function.update]; split_ifs
    · exfalso; have : Q h z ≠ 0 := by apply exp_ne_zero;
      norm_cast at *
    · rfl
  rw [this]
  dsimp only [cuspFcn0]
  obtain ⟨m, hm⟩ := ZQ_eq_mod_period h z
  rw [hm]; exact (is_periodic h f hf z m).symm

end PeriodicOnC

section HoloOnC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

theorem cuspFcn_diff_at (z : ℂ) (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (cuspFcn h f) (Q h z) :=
  by
  let q := Q h z
  have qdiff : HasStrictDerivAt (Q h) (q * (2 * π * I / h) ) z :=
    by
    simp_rw [Q]
    apply HasStrictDerivAt.cexp
    apply HasStrictDerivAt.div_const
    have := HasStrictDerivAt.const_mul  (2 * π * I) (hasStrictDerivAt_id z)
    simp at *
    apply this
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : q * (2 * π * I / h) ≠ 0 :=
    by
    apply mul_ne_zero; apply exp_ne_zero; apply div_ne_zero
    exact two_pi_I_ne_zero; simpa using h.2.ne'
  let L := (qdiff.localInverse (Q h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q := (qdiff.to_localInverse diff_ne).differentiableAt
  have hL : Q h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := EventuallyEq.fun_comp hL (cuspFcn h f);
  dsimp at hF 
  have : cuspFcn h f ∘ Q h ∘ L = f ∘ L := by ext1 z; exact (eq_cuspFcn h f hf (L z)).symm
  rw [this] at hF 
  have : z = L q :=
    by
    have hL2 : L ∘ Q h =ᶠ[𝓝 z] (id : ℂ → ℂ) :=
      (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse
    replace hL2 := EventuallyEq.eq_of_nhds hL2;
    rw [ id_eq] at hL2
    rw [←hL2]
    simp
  rw [this] at hol_z 
  exact (DifferentiableAt.comp q hol_z diff_L).congr_of_eventuallyEq hF.symm

theorem F_diff_near_zero (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    ∀ᶠ q : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFcn h f) q :=
  by
  refine' ((z_tendsto h).eventually h_hol).mp _
  apply eventually_nhdsWithin_of_forall; intro q hq h_diff
  rw [← QZ_eq_id _ _ hq]; exact cuspFcn_diff_at _ _ hf _ h_diff

end HoloOnC

section HoloAtInfC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

theorem F_bound (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ)) :
    IsBigO (𝓝[≠] (0 : ℂ)) (cuspFcn h f) (1 : ℂ → ℂ) :=
  by
  refine' IsBigO.congr' (h_bd.comp_tendsto <| z_tendsto h) _ (by rfl)
  apply eventually_nhdsWithin_of_forall; intro q hq
  rw [cuspFcn_eq_of_nonzero _ _ _ hq]; rfl

theorem F_diff_at_zero (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) : DifferentiableAt ℂ (cuspFcn h f) 0 :=
  by
  obtain ⟨c, t⟩ := (F_bound _ _  h_bd).bound
  have T:= (F_diff_near_zero h f hf h_hol)
  replace t := T.and t 
  simp only [norm_eq_abs, Pi.one_apply, AbsoluteValue.map_one, mul_one] at t 
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFcn h f) (S \ {0}) :=
    by
    intro x hx; apply DifferentiableAt.differentiableWithinAt
    exact (hS1 x ((Set.mem_diff _).mp hx).1 ((Set.mem_diff _).mp hx).2).1
  have hF_bd : BddAbove (norm ∘ cuspFcn h f '' (S \ {0})) := by 
    use c; rw [mem_upperBounds]; simp;
    intro y q hq hq2 hy; rw [← hy]; exact (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← update_twice] at this 
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/-- If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0. -/
theorem tendsto_at_I_inf (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    Tendsto f atIInf' (𝓝 <| cuspFcn h f 0) :=
  by
  suffices Tendsto (cuspFcn h f) (𝓝[≠] 0) (𝓝 <| cuspFcn h f 0)
    by
    have t2 : f = cuspFcn h f ∘ Q h := by ext1; apply eq_cuspFcn h f hf
    conv =>
      congr
      rw [t2]
    apply Tendsto.comp; exact this
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    exact q_tendsto h; apply eventually_of_forall; intro q; apply exp_ne_zero
  exact tendsto_nhdsWithin_of_tendsto_nhds (F_diff_at_zero _ _ hf h_bd h_hol).continuousAt.tendsto

theorem cuspFcn_zero_of_zero_at_inf (h_bd : IsLittleO atIInf' f (1 : ℂ → ℂ)) : cuspFcn h f 0 = 0 :=
  by
  rw [cuspFcn, Function.update]; split_ifs; swap; tauto
  suffices Tendsto (cuspFcn0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0 : ℂ)) by exact Tendsto.limUnder_eq this
  have :IsLittleO (𝓝[≠] (0 : ℂ)) (cuspFcn h f) 1 :=
    by
    refine' IsLittleO.congr' (h_bd.comp_tendsto <| z_tendsto h) _ (by rfl)
    apply eventually_nhdsWithin_of_forall; intro q hq; rw [cuspFcn_eq_of_nonzero _ _ _ hq]; rfl
  have : IsLittleO (𝓝[≠] (0 : ℂ)) (cuspFcn0 h f) 1 :=
    by
    refine' IsLittleO.congr' this _ (by rfl); apply eventually_nhdsWithin_of_forall
    apply cuspFcn_eq_of_nonzero
  simpa using this.tendsto_div_nhds_zero

/-- Main theorem of this file: if `f` is periodic, holomorphic near `I∞`, and tends to zero
at `I∞`, then in fact it tends to zero exponentially fast. -/
theorem exp_decay_of_zero_at_inf (h_bd : IsLittleO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    IsBigO atIInf' f fun z : ℂ => Real.exp (-2 * π * im z / h) :=
  by
  have F0 := cuspFcn_zero_of_zero_at_inf ?_ _ h_bd 
  have : f = fun z : ℂ => (cuspFcn h f) (Q h z) := by ext1 z; apply eq_cuspFcn _ _ hf
  --rw [this]
  --simp
  --rw [← abs_q_eq h, ← norm_eq_abs]
  rw [this]
  simp_rw [← abs_q_eq h, ← norm_eq_abs]
  apply IsBigO.norm_right
  apply (bound_holo_fcn (cuspFcn h f) ?_ ?_).comp_tendsto (q_tendsto h)
  apply  (F_diff_at_zero _ _ hf h_bd.isBigO h_hol)
  convert F0

end HoloAtInfC

/-! Now we prove corresponding results about modular forms. -/


local notation "ℍ" => UpperHalfPlane

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

instance : VAdd ℝ ℍ := by
  constructor; intro h z; refine' ⟨z + h, _⟩; dsimp at *
  suffices 0 < Complex.im (z + h) by exact this
  rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact z.2

/-! Tedious checks that notions of holomorphic, bounded, etc are compatible with extension-by-0--/


section ModformEquivs

variable {f : ℍ → ℂ} {k : ℤ}

theorem modform_bound_aux (C : ℝ) (g : ℂ → ℂ) (hc : 0 ≤ C)
    (h_bd : IsBigOWith C UpperHalfPlane.atImInfty f fun z : ℍ => g z) :
    IsBigOWith C atIInf' (extendByZero f) g :=
  by
  rw [isBigOWith_iff] at h_bd ⊢
  apply eventually_of_mem
  show {z : ℂ | Complex.abs (extendByZero f z) ≤ C * Complex.abs (g z)} ∈ atIInf'
  · rw [atIInf'_mem]
    rw [UpperHalfPlane.atImInfty, eventually_iff_exists_mem] at h_bd ; obtain ⟨v, hv, h_bd⟩ := h_bd
    rw [mem_comap', mem_atTop_sets] at hv ; cases' hv with a hv; use a
    intro z hz; specialize hv (im z) hz.le; dsimp at hv 
    simp_rw [extendByZero]; dsimp; split_ifs with h  
    swap; · rw [AbsoluteValue.map_zero]; refine' mul_nonneg hc _; apply AbsoluteValue.nonneg
    specialize h_bd ⟨z, h⟩
    specialize h_bd (hv _); rfl; exact h_bd
  · dsimp; intro x hx; linarith

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

theorem modform_bounded (f : ModularForm ⊤ k) : IsBigO atIInf' (extendByZero f) (1 : ℂ → ℂ) :=
  by
  have bd := f.bdd_at_infty' (1 : SL(2, ℤ))
  have : f.toFun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  simp at bd
  rw [ UpperHalfPlane.IsBoundedAtImInfty] at bd 
  rw [BoundedAtFilter] at bd 
  obtain ⟨c, c_pos, bd⟩ := bd.exists_nonneg
  rw [atIInf']
  apply (modform_bound_aux c 1 c_pos _).isBigO
  simp
  simp_rw [IsBigOWith] at *
  simp at *
  exact bd

theorem cuspform_vanish_infty (f : CuspForm ⊤ k) : IsLittleO atIInf' (extendByZero f) (1 : ℂ → ℂ) :=
  by
  have bd := f.zero_at_infty' (1 : SL(2, ℤ))
  have : f.toFun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  simp at bd
  rw [UpperHalfPlane.IsZeroAtImInfty] at bd 
  have : IsLittleO UpperHalfPlane.atImInfty f (1 : ℍ → ℂ) := by 
    apply isLittleO_of_tendsto; simp;
    simpa using bd
  rw [IsLittleO] at *; exact fun c hc => modform_bound_aux c 1 hc.le (this hc)

@[simp]
lemma uhc2 (z : ℍ) : (z : ℂ) = z.1 := by rfl


theorem modform_periodic (f : ModularForm ⊤ k) (w : ℂ) :
    (extendByZero f) (w + 1) = (extendByZero f) w :=
  by
  by_cases hw : 0 < im w
  · rw [extendByZero_eq_of_mem f w hw]
    have : 0 < im (w + 1) := by rw [add_im, one_im, add_zero]; exact hw
    rw [extendByZero_eq_of_mem f _ this]
    have t := EisensteinSeries.mod_form_periodic k f ⟨w, hw⟩ 1
    rw [UpperHalfPlane.modular_T_zpow_smul] at t
    convert t; simp
    simp
    rw [←UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd]
    simp
    apply add_comm
  · have : extendByZero f w = 0 := by 
      rw [extendByZero]; 
      simp; 
      split_ifs with h
      exfalso; 
      swap
      rfl
      exact  hw h 
    rw [this]
    have : extendByZero f (w + 1) = 0 := by
      rw [extendByZero]; simp;
      split_ifs with h
      simp
      exfalso
      have : 0 < im (w + 1) := by tauto
      rw [add_im, one_im, add_zero] at this 
      exact hw this
      rfl
    exact this

theorem modform_hol (f : ModularForm ⊤ k) (z : ℂ) (hz : 0 < im z) :
    DifferentiableAt ℂ (extendByZero f) z :=
  by
  have hf_hol := EisensteinSeries.mdiff_to_holo (EisensteinSeries.holExtn f) f.holo'
  rw [← isHolomorphicOn_iff_differentiableOn] at hf_hol 
  simp at hf_hol
  exact (hf_hol z hz).differentiableAt ((isOpen_iff_mem_nhds.mp upper_half_plane_isOpen) z hz)

theorem modform_hol_infty (f : ModularForm ⊤ k) :
    ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ (extendByZero f) z :=
  by
  refine' eventually_of_mem (_ : UpperHalfPlane.upperHalfSpace ∈ atIInf') _
  · rw [atIInf'_mem]; use 0; tauto
  · intro x hx; exact modform_hol f x hx

end ModformEquivs

section Modforms

def unitDiscSset :=
  {z : ℂ | Complex.abs z< 1}

theorem unit_disc_isOpen : IsOpen unitDiscSset :=
  isOpen_Iio.preimage Complex.continuous_abs

local notation "𝔻" =>  (TopologicalSpace.Opens.mk unitDiscSset unit_disc_isOpen)

variable (f : ℍ → ℂ) (k : ℤ)

--lemma q_in_D (z : ℍ) : abs (Q 1 z) < 1 := by { convert (abs_q_lt_iff 1 0 z).mpr z.2, simp }
theorem z_in_H (q : 𝔻) (hq : (q : ℂ) ≠ 0) : 0 < im (Z 1 q) :=
  by
  rw [im_z_eq 1 q]
  apply mul_pos_of_neg_of_neg
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) Real.two_pi_pos
  rw [Real.log_neg_iff]; exact q.2
  apply AbsoluteValue.pos; exact hq

def cuspFcnH : ℂ → ℂ :=
  cuspFcn 1 <| extendByZero f

theorem eq_cuspFcnH (z : ℍ) (f : ModularForm ⊤ k) : f z = (cuspFcnH f) (Q 1 z) :=
  by
  have t := eq_cuspFcn 1 (extendByZero f) (modform_periodic f) z
  rw [cuspFcnH]; convert t
  rw [extendByZero_eq_of_mem f _ _]; · simp; 
  · cases z; tauto

theorem cusp_fcn_diff (f : ModularForm ⊤ k) (q : 𝔻) : DifferentiableAt ℂ (cuspFcnH f) q :=
  by
  by_cases hq : (q : ℂ) = 0
  · rw [hq];
    exact
      F_diff_at_zero 1 (extendByZero f) (modform_periodic f) (modform_bounded f)
        (modform_hol_infty f)
  · have t :=
      cuspFcn_diff_at 1 (extendByZero f) (modform_periodic f) _ (modform_hol f _ <| z_in_H q hq)
    rw [QZ_eq_id 1 q hq] at t ; rw [cuspFcnH]; exact t

/-
def cuspFormToModForm (f : CuspForm ⊤ k) : ModularForm ⊤ k
    where
  toFun := f.toFun
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' := by 
    intro A; 
    simp
    have := (f.zero_at_infty' A).BoundedAtFilter; convert this

  instance : Coe (CuspForm ⊤ k) (ModularForm ⊤ k) :=   
-/



theorem cusp_fcn_vanish (f : CuspForm ⊤ k) : cuspFcnH f 0 = 0 := by
  have :=cuspFcn_zero_of_zero_at_inf 1 (extendByZero f) ?_
  apply this
  apply cuspform_vanish_infty


theorem exp_decay_of_cuspform (f : CuspForm ⊤ k) :
    IsBigO UpperHalfPlane.atImInfty f fun z : ℍ => Real.exp (-2 * π * im z) :=
  by
  have := exp_decay_of_zero_at_inf 1 (extendByZero f) (modform_periodic (f : ModularForm ⊤ k))  (cuspform_vanish_infty f)
    (modform_hol_infty (f : ModularForm ⊤ k))
  simp at *
  have h2 := this.isBigOWith
  obtain ⟨C, hC⟩ := h2
  rw [IsBigO]; use C
  rw [isBigOWith_iff, eventually_iff] at hC ⊢
  rw [atIInf'_mem] at hC ; rw [UpperHalfPlane.atImInfty_mem]
  obtain ⟨A, hC⟩ := hC; use A + 1; intro z hz; specialize hC z
  have h : A < im z := by 
    simp at *
    rw [UpperHalfPlane.im] at hz
    norm_cast at *
    simp at *
    linarith; 
  simp at hC
  rw [extendByZero_eq_of_mem] at hC ; 
  swap; exact z.2
  have : ((1 : ℝPos) : ℝ) = (1 : ℝ) := by rfl
  simp  [Subtype.coe_eta, div_one] at hC ; 
  have HC := hC h
  simp
  exact HC

end Modforms

section Petersson

open scoped ModularForm

@[simp]
lemma uhc (z : ℍ) : (z : ℂ) = z.1 := by rfl

-- Bound on abs(f z) for large values of z
theorem pet_bounded_large {k : ℤ} (f : CuspForm ⊤ k) :
    ∃ A C : ℝ, ∀ z : ℍ, A ≤ im z → (petSelf f k) z ≤ C :=
  by
  -- first get bound for large values of im z
  have h1 := exp_decay_of_cuspform _ f
  have :
    IsBigO UpperHalfPlane.atImInfty (fun z : ℍ => Real.exp (-2 * π * z.im)) fun z : ℍ =>
      1 / z.im ^ ((k : ℝ) / 2) :=
    by
    apply IsLittleO.isBigO; 
    apply isLittleO_of_tendsto
    · intro x hx; exfalso
      contrapose! hx; apply one_div_ne_zero
      refine' (Real.rpow_pos_of_pos x.2 _).ne'
    rw [UpperHalfPlane.atImInfty]
    let F := fun y : ℝ => Real.exp (-2 * π * y) / (1 / y ^ ((k : ℝ) / 2))
    apply (@tendsto_comap'_iff _ _ _ F _ _ _ _).mpr
    · have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 ((k : ℝ) / 2) (2 * π) Real.two_pi_pos
      refine' Tendsto.congr' _ this; apply eventually_of_mem (Ioi_mem_atTop (0 : ℝ))
      intro y _;  simp; apply mul_comm; 
    · convert Ioi_mem_atTop (0 : ℝ); ext1 x; rw [Set.mem_range]
      constructor; · rintro ⟨y, hy⟩; rw [← hy]; exact y.2
      · intro h; 
        use ⟨x * I, ?_⟩
        swap
        · rw [mul_I_im]; exact h
        · rw [UpperHalfPlane.im]
          simp  [Subtype.coe_mk, mul_im, ofReal_re, I_im, mul_one, I_re, MulZeroClass.mul_zero,
            add_zero]
  obtain ⟨C1, h1'⟩ := (h1.trans this).bound
  rw [eventually_iff, UpperHalfPlane.atImInfty_mem] at h1' ; cases' h1' with A h1'
  dsimp at h1' ; refine' ⟨A, C1 ^ 2, _⟩
  intro z hz; specialize h1' z hz; rw [petSelf]; dsimp
  have : im z ^ k = (im z ^ ((k : ℝ) / 2)) ^ 2 :=
    by
    norm_cast
    rw [← Real.rpow_int_cast, ← Real.rpow_nat_cast, ← Real.rpow_mul]
    swap; exact z.2.le; congr 1; norm_cast; simp
    rw [Rat.divInt_eq_div]
    field_simp
    left
    norm_num
  norm_cast at *  
  rw [← UpperHalfPlane.coe_im, this, ← mul_pow]
  rw [sq_le_sq]
  have e : 0 < z.im ^ ((k : ℝ) / 2) := by apply Real.rpow_pos_of_pos; exact z.2
  have : abs (f z) * im z ^ ((k : ℝ) / 2) ≤ C1 :=
    by
    rw [div_eq_inv_mul, mul_one, _root_.abs_inv, mul_comm] at h1' 
    simp at *
    norm_cast at h1'
    have h2 : 0 ≤ (z.1).im ^ ((k : ℝ) / 2) := by 
      norm_cast
      simp
      apply Real.rpow_nonneg_of_nonneg
      exact z.2.le
    have h1'' := mul_le_mul_of_nonneg_right h1' h2 
    refine' le_trans h1'' _
    simp
    · rw [_root_.abs_of_nonneg]
      swap;
      norm_cast at *
      conv =>
        lhs
        congr
        rw [mul_comm];
      rw [mul_assoc]
      suffices th : (z.im ^ ((k : ℝ) / 2))⁻¹ * z.im ^ ((k : ℝ) / 2) = 1 by 
        simp_rw [← UpperHalfPlane.coe_im] at *
        norm_cast at *
        simp only [uhc2] at *
        rw [th]; 
        simp
      apply inv_mul_cancel; exact e.ne'
  apply abs_le_abs; 
  norm_cast at *
  have aux : -(Complex.abs (f z) * (z.1).im ^ ((k : ℝ) / 2)) ≤ Complex.abs (f z) * z.1.im ^ ((k : ℝ) / 2) := by 
    simp
    apply mul_nonneg; apply AbsoluteValue.nonneg; exact e.le
  norm_cast at *
  apply le_trans aux this
 

end Petersson

