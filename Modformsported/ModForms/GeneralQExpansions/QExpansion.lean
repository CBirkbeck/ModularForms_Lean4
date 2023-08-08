import Project.ForMathlib.ModForms2
import Project.ModForms.HolomorphicFunctions
import Mathbin.Analysis.Complex.RemovableSingularity
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.Analysis.Complex.UpperHalfPlane.Topology
import Mathbin.NumberTheory.Modular
import Mathbin.GroupTheory.Index
import Project.ModForms.EisensteinSeries.EisenIsHolo
import Mathbin.Analysis.Calculus.Inverse

#align_import mod_forms.general_q_expansions.q_expansion

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

instance : One ℝPos := by use 1

/-- Function-theoretic lemma, maybe move this elsewhere? -/
theorem bound_holo_fcn (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) (hg' : g 0 = 0) :
    IsBigO (𝓝 0) g id := by replace hg := hg.has_deriv_at.is_O_sub; simp_rw [hg', sub_zero] at hg ;
  exact hg

section QAndZ

variable (h : ℝPos)

def q (z : ℂ) : ℂ :=
  exp (2 * π * I * z / h)

def z (q : ℂ) : ℂ :=
  h / (2 * π * I) * log q

theorem log_exp' (z : ℂ) : ∃ n : ℤ, log (exp z) = z + n * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_log]; exact exp_ne_zero z

theorem QZ_eq_id (q : ℂ) (hq : q ≠ 0) : q h (z h q) = q :=
  by
  dsimp only [q, z]
  suffices 2 * ↑π * I * (↑h / (2 * ↑π * I) * log q) / ↑h = log q by rw [this]; exact exp_log hq
  have : (h : ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne'
  field_simp [two_pi_I_ne_zero, this]; ring

theorem abs_q_eq (z : ℂ) : abs (q h z) = Real.exp (-2 * π * im z / h) :=
  by
  dsimp only [q]; rw [abs_exp]; congr
  rw [div_eq_mul_inv, mul_comm]
  have : (↑h)⁻¹ = (↑(h : ℝ)⁻¹ : ℂ) := by simp; rw [this]
  rw [of_real_mul_re]
  have : 2 * ↑π * I * z = ↑(2 * π) * z * I := by simp; ring
  rw [this, mul_I_re, of_real_mul_im]; field_simp [h.2.ne']

theorem im_z_eq (q : ℂ) (hq : q ≠ 0) : im (z h q) = -h / (2 * π) * Real.log (abs q) :=
  by
  dsimp only [z]
  have : ↑h / (2 * ↑π * I) * log q = -↑h / (2 * ↑π) * log q * I := by
    field_simp [of_real_ne_zero.mpr real.pi_pos.ne', two_pi_I_ne_zero]; ring_nf; simp
  rw [this, mul_I_im]
  have : -↑h / (2 * ↑π) * log q = ↑(-↑h / (2 * π)) * log q := by simp
  rw [this, of_real_mul_re, log_re]

theorem ZQ_eq_mod_period (z : ℂ) : ∃ m : ℤ, z h (q h z) = z + m * h :=
  by
  dsimp only [q, z]
  have t := log_exp' (2 * ↑π * I * z / ↑h)
  cases' t with m t; use m; rw [t]
  have : (h : ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne'
  field_simp [two_pi_I_ne_zero]; ring

theorem abs_q_lt_iff (A : ℝ) (z : ℂ) : abs (q h z) < Real.exp (-2 * π * A / h) ↔ A < im z :=
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
  rw [atIInf', mem_comap', mem_at_top_sets]
  simp; constructor
  · intro h; cases' h with a h; use a
    intro z hz; specialize h (im z) hz.le; apply h; rfl
  · intro h; cases' h with A h; use A + 1
    intro b hb x hx; apply h x; rw [hx]; linarith

theorem z_tendsto : Tendsto (z h) (𝓝[{0}ᶜ] 0) atIInf' :=
  by
  rw [tendsto, map_le_iff_le_comap, comap]
  intro S h; simp_rw [atIInf'_mem] at h ; obtain ⟨T, ⟨A, hA⟩, hT⟩ := h
  simp_rw [Metric.mem_nhdsWithin_iff, Metric.ball, dist_eq, sub_zero]
  use Real.exp (-2 * π * A / h); constructor; apply Real.exp_pos
  intro q; dsimp; rintro ⟨u1, u2⟩
  rw [← QZ_eq_id h _ u2, abs_q_lt_iff] at u1 ; specialize hA (z h q) u1
  apply hT; exact hA

theorem q_tendsto : Tendsto (q h) atIInf' (𝓝 0) :=
  by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_eq_abs, abs_q_eq]
  have : Set.range im ∈ at_top :=
    by
    suffices Set.range im = ⊤ by rw [this]; apply univ_mem
    ext1; simp only [Set.mem_range, Set.top_eq_univ, Set.mem_univ, iff_true_iff]
    use I * x; simp
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (fun y => Real.exp (-2 * π * y / ↑h)) at_top (𝓝 0) im this).mpr
  apply this; refine' real.tendsto_exp_at_bot.comp _
  apply tendsto.at_bot_div_const h.2
  apply tendsto.neg_const_mul_at_top; · simpa using Real.pi_pos; exact tendsto_id

end QAndZ

section PeriodicOnC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

def cuspFcn0 : ℂ → ℂ := fun q => f (z h q)

def cuspFcn : ℂ → ℂ :=
  Function.update (cuspFcn0 h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn0 h f))

theorem cuspFcn_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) : (cuspFcn h f) q = (cuspFcn0 h f) q :=
  by
  rw [cuspFcn, Function.update]; split_ifs
  · exfalso; exact hq h_1
  · rfl

theorem update_twice :
    cuspFcn h f = Function.update (cuspFcn h f) 0 (limUnder (𝓝[≠] (0 : ℂ)) (cuspFcn h f)) :=
  by
  ext1 q; rw [Function.update]; split_ifs
  · rw [cuspFcn, Function.update]; split_ifs
    congr 1; rw [limUnder, limUnder]; congr 1
    apply map_congr; apply eventuallyEq_nhdsWithin_of_eqOn
    intro r hr; simp at hr 
    rw [Function.update]; split_ifs; rfl
  · rfl

private theorem is_periodic_aux (z : ℂ) (m : ℕ) : f (z + m * h) = f z :=
  by
  induction' m with m hm generalizing z; simp
  rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul, ← add_assoc, one_mul]
  rw [hf (z + m * h)]; exact hm z

theorem is_periodic (z : ℂ) (m : ℤ) : f (z + m * h) = f z :=
  by
  cases m; · exact is_periodic_aux h f hf z m
  simp only [neg_add_rev, Int.cast_negSucc]
  convert (is_periodic_aux h f hf (z - (m + 1) * h) (m + 1)).symm
  · simp; ring; · simp

theorem eq_cuspFcn (z : ℂ) : f z = (cuspFcn h f) (q h z) :=
  by
  have : (cuspFcn h f) (q h z) = (cuspFcn0 h f) (q h z) :=
    by
    rw [cuspFcn]; rw [Function.update]; split_ifs
    · exfalso; have : q h z ≠ 0 := by apply exp_ne_zero; exact this h_1
    · rfl
  rw [this]
  dsimp only [cuspFcn0]
  obtain ⟨m, hm⟩ := ZQ_eq_mod_period h z
  rw [hm]; exact (is_periodic h f hf z m).symm

end PeriodicOnC

section HoloOnC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

theorem cuspFcn_diff_at (z : ℂ) (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (cuspFcn h f) (q h z) :=
  by
  let q := q h z
  have qdiff : HasStrictDerivAt (q h) (q * (2 * π * I / h)) z :=
    by
    apply HasStrictDerivAt.cexp
    apply HasStrictDerivAt.div_const
    have : 2 * ↑π * I = 2 * ↑π * I * 1 := by ring
    conv =>
      congr
      skip
      rw [this]
    exact HasStrictDerivAt.const_mul _ (hasStrictDerivAt_id _)
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : q * (2 * π * I / h) ≠ 0 :=
    by
    apply mul_ne_zero; apply exp_ne_zero; apply div_ne_zero
    exact two_pi_I_ne_zero; simpa using h.2.ne'
  let L := (qdiff.local_inverse (q h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q := (qdiff.to_local_inverse diff_ne).DifferentiableAt
  have hL : q h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_right_inverse
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := eventually_eq.fun_comp hL (cuspFcn h f);
  dsimp at hF 
  have : cuspFcn h f ∘ q h ∘ L = f ∘ L := by ext1 z; exact (eq_cuspFcn h f hf (L z)).symm
  rw [this] at hF 
  have : z = L q :=
    by
    have hL2 : L ∘ q h =ᶠ[𝓝 z] (id : ℂ → ℂ) :=
      (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_left_inverse
    replace hL2 := eventually_eq.eq_of_nhds hL2; dsimp at hL2 ; rw [hL2]
  rw [this] at hol_z 
  exact (DifferentiableAt.comp q hol_z diff_L).congr_of_eventuallyEq hF.symm

theorem F_diff_near_zero (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    ∀ᶠ q : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFcn h f) q :=
  by
  refine' ((z_tendsto h).Eventually h_hol).mp _
  apply eventually_nhdsWithin_of_forall; intro q hq h_diff
  rw [← QZ_eq_id _ _ hq]; exact cuspFcn_diff_at _ _ hf _ h_diff

end HoloOnC

section HoloAtInfC

variable (h : ℝPos) (f : ℂ → ℂ) (hf : ∀ w : ℂ, f (w + h) = f w)

theorem F_bound (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ)) :
    IsBigO (𝓝[≠] (0 : ℂ)) (cuspFcn h f) (1 : ℂ → ℂ) :=
  by
  refine' is_O.congr' (h_bd.comp_tendsto <| z_tendsto h) _ (by rfl)
  apply eventually_nhdsWithin_of_forall; intro q hq
  rw [cuspFcn_eq_of_nonzero _ _ _ hq]; rfl

theorem F_diff_at_zero (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) : DifferentiableAt ℂ (cuspFcn h f) 0 :=
  by
  obtain ⟨c, t⟩ := (F_bound _ _ hf h_bd).bound
  replace t := (F_diff_near_zero h f hf h_hol).And t
  simp only [norm_eq_abs, Pi.one_apply, AbsoluteValue.map_one, mul_one] at t 
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhds_within_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFcn h f) (S \ {0}) :=
    by
    intro x hx; apply DifferentiableAt.differentiableWithinAt
    exact (hS1 x ((Set.mem_diff _).mp hx).1 ((Set.mem_diff _).mp hx).2).1
  have hF_bd : BddAbove (norm ∘ cuspFcn h f '' (S \ {0})) := by use c; rw [mem_upperBounds]; simp;
    intro y q hq hq2 hy; rw [← hy]; exact (hS1 q hq hq2).2
  have := differentiable_on_update_lim_of_bdd_above (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← update_twice] at this 
  exact this.differentiable_at (IsOpen.mem_nhds hS2 hS3)

/-- If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0. -/
theorem tendsto_at_I_inf (h_bd : IsBigO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    Tendsto f atIInf' (𝓝 <| cuspFcn h f 0) :=
  by
  suffices tendsto (cuspFcn h f) (𝓝[≠] 0) (𝓝 <| cuspFcn h f 0)
    by
    have t2 : f = cuspFcn h f ∘ q h := by ext1; apply eq_cuspFcn h f hf
    conv =>
      congr
      rw [t2]
    apply tendsto.comp; exact this
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    exact q_tendsto h; apply eventually_of_forall; intro q; apply exp_ne_zero
  exact tendsto_nhdsWithin_of_tendsto_nhds (F_diff_at_zero _ _ hf h_bd h_hol).ContinuousAt.Tendsto

theorem cuspFcn_zero_of_zero_at_inf (h_bd : IsLittleO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) : cuspFcn h f 0 = 0 :=
  by
  rw [cuspFcn, Function.update]; split_ifs; swap; tauto
  suffices tendsto (cuspFcn0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0 : ℂ)) by exact tendsto.lim_eq this
  have : is_o (𝓝[≠] (0 : ℂ)) (cuspFcn h f) 1 :=
    by
    refine' is_o.congr' (h_bd.comp_tendsto <| z_tendsto h) _ (by rfl)
    apply eventually_nhdsWithin_of_forall; intro q hq; rw [cuspFcn_eq_of_nonzero _ _ _ hq]; rfl
  have : is_o (𝓝[≠] (0 : ℂ)) (cuspFcn0 h f) 1 :=
    by
    refine' is_o.congr' this _ (by rfl); apply eventually_nhdsWithin_of_forall
    apply cuspFcn_eq_of_nonzero
  simpa using this.tendsto_div_nhds_zero

/-- Main theorem of this file: if `f` is periodic, holomorphic near `I∞`, and tends to zero
at `I∞`, then in fact it tends to zero exponentially fast. -/
theorem exp_decay_of_zero_at_inf (h_bd : IsLittleO atIInf' f (1 : ℂ → ℂ))
    (h_hol : ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ f z) :
    IsBigO atIInf' f fun z : ℂ => Real.exp (-2 * π * im z / h) :=
  by
  have F0 := cuspFcn_zero_of_zero_at_inf _ _ hf h_bd h_hol
  have : f = fun z : ℂ => (cuspFcn h f) (q h z) := by ext1 z; apply eq_cuspFcn _ _ hf
  conv =>
    congr
    skip
    rw [this]
    skip
    ext
    rw [← abs_q_eq h, ← norm_eq_abs]
  apply is_O.norm_right
  exact (bound_holo_fcn _ (F_diff_at_zero _ _ hf h_bd.is_O h_hol) F0).comp_tendsto (q_tendsto h)

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
  rw [is_O_with_iff] at h_bd ⊢
  apply eventually_of_mem
  show {z : ℂ | Complex.abs (extendByZero f z) ≤ C * Complex.abs (g z)} ∈ atIInf'
  · rw [atIInf'_mem]
    rw [UpperHalfPlane.atImInfty, eventually_iff_exists_mem] at h_bd ; obtain ⟨v, hv, h_bd⟩ := h_bd
    rw [mem_comap', mem_at_top_sets] at hv ; cases' hv with a hv; use a
    intro z hz; specialize hv (im z) hz.le; dsimp at hv 
    rw [extendByZero]; dsimp; split_ifs
    swap; · rw [AbsoluteValue.map_zero]; refine' mul_nonneg hc _; apply AbsoluteValue.nonneg
    specialize h_bd ⟨z, h⟩
    specialize h_bd (hv _); rfl; exact h_bd
  · dsimp; intro x hx; linarith

local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

theorem modform_bounded (f : ModularForm ⊤ k) : IsBigO atIInf' (extendByZero f) (1 : ℂ → ℂ) :=
  by
  have bd := f.bdd_at_infty' (1 : SL(2, ℤ))
  have : f.to_fun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  rw [this, UpperHalfPlane.IsBoundedAtImInfty] at bd 
  rw [bounded_at_filter] at bd 
  obtain ⟨c, c_pos, bd⟩ := bd.exists_nonneg
  rw [atIInf']
  apply (modform_bound_aux c 1 c_pos _).IsBigO
  simp
  rw [is_O_with] at *
  simp at *
  exact bd

theorem cuspform_vanish_infty (f : CuspForm ⊤ k) : IsLittleO atIInf' (extendByZero f) (1 : ℂ → ℂ) :=
  by
  have bd := f.zero_at_infty' (1 : SL(2, ℤ))
  have : f.to_fun∣[k,(1 : SL(2, ℤ))] = f := by apply SlashAction.slash_one
  rw [this, UpperHalfPlane.IsZeroAtImInfty] at bd 
  have : is_o UpperHalfPlane.atImInfty f (1 : ℍ → ℂ) := by apply is_o_of_tendsto; simp;
    simpa using bd
  rw [is_o] at *; exact fun c hc => modform_bound_aux c 1 hc.le (this hc)

theorem modform_periodic (f : ModularForm ⊤ k) (w : ℂ) :
    (extendByZero f) (w + 1) = (extendByZero f) w :=
  by
  by_cases hw : 0 < im w
  · rw [extendByZero_eq_of_mem f w hw]
    have : 0 < im (w + 1) := by rw [add_im, one_im, add_zero]; exact hw
    rw [extendByZero_eq_of_mem f _ this]
    have t := EisensteinSeries.mod_form_periodic k f ⟨w, hw⟩ 1
    rw [EisensteinSeries.smul_expl] at t ; convert t; simp
  · have : extendByZero f w = 0 := by rw [extendByZero]; simp; intro bad; exfalso; exact hw bad
    rw [this]
    have : extendByZero f (w + 1) = 0 := by
      rw [extendByZero]; simp; intro bad; exfalso
      have : 0 < im (w + 1) := by tauto
      rw [add_im, one_im, add_zero] at this 
      exact hw this
    exact this

theorem modform_hol (f : ModularForm ⊤ k) (z : ℂ) (hz : 0 < im z) :
    DifferentiableAt ℂ (extendByZero f) z :=
  by
  have hf_hol := EisensteinSeries.mdiff_to_holo (EisensteinSeries.holExtn f) f.holo'
  rw [← isHolomorphicOn_iff_differentiableOn] at hf_hol 
  exact (hf_hol z hz).DifferentiableAt ((is_open_iff_mem_nhds.mp upper_half_plane_isOpen) z hz)

theorem modform_hol_infty (f : ModularForm ⊤ k) :
    ∀ᶠ z : ℂ in atIInf', DifferentiableAt ℂ (extendByZero f) z :=
  by
  refine' eventually_of_mem (_ : UpperHalfPlane.upperHalfSpace ∈ atIInf') _
  · rw [atIInf'_mem]; use 0; tauto
  · intro x hx; exact modform_hol f x hx

end ModformEquivs

section Modforms

def unitDiscSset :=
  {z : ℂ | z.abs < 1}

theorem unit_disc_isOpen : IsOpen unitDiscSset :=
  isOpen_Iio.Preimage Complex.continuous_abs

local notation "𝔻" => (⟨unitDiscSset, unit_disc_isOpen⟩ : TopologicalSpace.Opens ℂ)

variable (f : ℍ → ℂ) (k : ℤ)

--lemma q_in_D (z : ℍ) : abs (Q 1 z) < 1 := by { convert (abs_q_lt_iff 1 0 z).mpr z.2, simp }
theorem z_in_H (q : 𝔻) (hq : (q : ℂ) ≠ 0) : 0 < im (z 1 q) :=
  by
  rw [im_z_eq 1 q hq]
  apply mul_pos_of_neg_of_neg
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) Real.two_pi_pos
  rw [Real.log_neg_iff]; exact q.2
  apply AbsoluteValue.pos; exact hq

def cuspFcnH : ℂ → ℂ :=
  cuspFcn 1 <| extendByZero f

theorem eq_cuspFcnH (z : ℍ) (f : ModularForm ⊤ k) : f z = (cuspFcnH f) (q 1 z) :=
  by
  have t := eq_cuspFcn 1 (extendByZero f) (modform_periodic f) z
  rw [cuspFcnH]; convert t
  rw [extendByZero_eq_of_mem f _ _]; · simp; · cases z; tauto

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

def cuspFormToModForm (f : CuspForm ⊤ k) : ModularForm ⊤ k
    where
  toFun := f.toFun
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' := by intro A; have := (f.zero_at_infty' A).BoundedAtFilter; convert this

instance : Coe (CuspForm ⊤ k) (ModularForm ⊤ k) where coe := cuspFormToModForm _

theorem cusp_fcn_vanish (f : CuspForm ⊤ k) : cuspFcnH f 0 = 0 :=
  cuspFcn_zero_of_zero_at_inf 1 (extendByZero f) (modform_periodic (f : ModularForm ⊤ k))
    (cuspform_vanish_infty f) (modform_hol_infty (f : ModularForm ⊤ k))

theorem exp_decay_of_cuspform (f : CuspForm ⊤ k) :
    IsBigO UpperHalfPlane.atImInfty f fun z : ℍ => Real.exp (-2 * π * im z) :=
  by
  obtain ⟨C, hC⟩ :=
    (exp_decay_of_zero_at_inf 1 (extendByZero f) (modform_periodic (f : ModularForm ⊤ k))
        (cuspform_vanish_infty f) (modform_hol_infty (f : ModularForm ⊤ k))).IsBigOWith
  rw [is_O]; use C
  rw [is_O_with_iff, eventually_iff] at hC ⊢
  rw [atIInf'_mem] at hC ; rw [UpperHalfPlane.atImInfty_mem]
  obtain ⟨A, hC⟩ := hC; use A + 1; intro z hz; specialize hC z
  have : A < im z := by simp; linarith; specialize hC this; dsimp at hC ⊢
  rw [extendByZero_eq_of_mem] at hC ; swap; exact z.2
  have : ((1 : ℝPos) : ℝ) = (1 : ℝ) := by rfl
  simp only [Subtype.coe_eta, div_one] at hC ; exact hC

end Modforms

section Petersson

open scoped ModularForm

-- Bound on abs(f z) for large values of z
theorem pet_bounded_large {k : ℤ} (f : CuspForm ⊤ k) :
    ∃ A C : ℝ, ∀ z : ℍ, A ≤ im z → (petSelf f k) z ≤ C :=
  by
  -- first get bound for large values of im z
  have h1 := exp_decay_of_cuspform _ f
  have :
    is_O UpperHalfPlane.atImInfty (fun z : ℍ => Real.exp (-2 * π * z.im)) fun z : ℍ =>
      1 / z.im ^ ((k : ℝ) / 2) :=
    by
    apply is_o.is_O; apply is_o_of_tendsto
    · intro x hx; exfalso
      contrapose! hx; apply one_div_ne_zero
      refine' (Real.rpow_pos_of_pos x.2 _).ne'
    rw [UpperHalfPlane.atImInfty]
    let F := fun y : ℝ => Real.exp (-2 * π * y) / (1 / y ^ ((k : ℝ) / 2))
    apply (@tendsto_comap'_iff _ _ _ F _ _ _ _).mpr
    · have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 ((k : ℝ) / 2) (2 * π) Real.two_pi_pos
      refine' tendsto.congr' _ this; apply eventually_of_mem (Ioi_mem_at_top (0 : ℝ))
      intro y hy; dsimp [F]; rw [div_div_eq_mul_div, div_one, mul_comm]; congr 1
      simp only [neg_mul]
    · convert Ioi_mem_at_top (0 : ℝ); ext1; rw [Set.mem_range]
      constructor; · rintro ⟨y, hy⟩; rw [← hy]; exact y.2
      · intro h; use x * I
        · rw [mul_I_im]; exact h
        · rw [UpperHalfPlane.im]
          simp only [Subtype.coe_mk, mul_im, of_real_re, I_im, mul_one, I_re, MulZeroClass.mul_zero,
            add_zero]
  obtain ⟨C1, h1'⟩ := (h1.trans this).bound
  rw [eventually_iff, UpperHalfPlane.atImInfty_mem] at h1' ; cases' h1' with A h1'
  dsimp at h1' ; refine' ⟨A, C1 ^ 2, _⟩
  intro z hz; specialize h1' z hz; rw [petSelf]; dsimp
  have : im z ^ k = (im z ^ ((k : ℝ) / 2)) ^ 2 :=
    by
    rw [← Real.rpow_int_cast, ← Real.rpow_nat_cast, ← Real.rpow_mul]
    swap; exact z.2.le; congr 1; simp
  rw [← UpperHalfPlane.coe_im, this, ← mul_pow]
  rw [sq_le_sq]
  have e : 0 < z.im ^ ((k : ℝ) / 2) := by apply Real.rpow_pos_of_pos; exact z.2
  have : abs (f z) * im z ^ ((k : ℝ) / 2) ≤ C1 :=
    by
    rw [div_eq_inv_mul, mul_one, _root_.abs_inv, mul_comm] at h1' 
    have h1'' := mul_le_mul_of_nonneg_right h1' _; refine' le_trans h1'' _
    simp
    · rw [_root_.abs_of_nonneg]
      swap; apply Real.rpow_nonneg_of_nonneg; exact z.2.le
      conv =>
        lhs
        congr
        rw [mul_comm];
      rw [mul_assoc]
      suffices (z.im ^ ((k : ℝ) / 2))⁻¹ * z.im ^ ((k : ℝ) / 2) = 1 by rw [this]; simp
      apply inv_mul_cancel; exact e.ne'
    exact e.le
  apply abs_le_abs; · exact this
  have aux : -(abs (f z) * ↑z.im ^ ((k : ℝ) / 2)) ≤ abs (f z) * ↑z.im ^ ((k : ℝ) / 2) := by simp;
    apply mul_nonneg; apply AbsoluteValue.nonneg; exact e.le
  exact le_trans aux this

end Petersson

