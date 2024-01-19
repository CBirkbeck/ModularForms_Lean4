import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Series
import Modformsported.ForMathlib.TsumLemmas
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Modformsported.ForMathlib.IteratedDerivLemmas
import Modformsported.ForMathlib.EisensteinSeries.bounds
import Modformsported.ForMathlib.EisensteinSeries.summable
import Modformsported.ForMathlib.EisensteinSeries.partial_sum_tendsto_uniformly
import Modformsported.ModForms.Riemzeta


noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

--local notation "ℍ" => UpperHalfPlane

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

theorem upper_ne_int (x : ℍ') (d : ℤ) : (x : ℂ) + d ≠ 0 :=
  by
  by_contra h
  rw [add_eq_zero_iff_eq_neg] at h
  have h1 : 0 < (x : ℂ).im := by simp [x.2]; exact im_pos x
  rw [h] at h1
  simp only [neg_im, int_cast_im, neg_zero, lt_self_iff_false] at h1

theorem upper_ne_nat (x : ℍ') (d : ℕ) : (x : ℂ) ≠ d :=
  by
  by_contra h
  have h1 : 0 < (x : ℂ).im := by simp [x.2]; exact im_pos x
  rw [h] at h1
  simp only [nat_cast_im, lt_self_iff_false] at h1


theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) ℍ')
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) ℍ' :=
  by
  intro x hx
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero, pow_zero, Nat.factorial_zero, algebraMap.coe_one, pow_one,
    one_mul]
  norm_cast at *
  simp  at *
  rw [iteratedDerivWithin_succ]
  simp only [one_div, Opens.coe_mk, Nat.cast_succ, Nat.factorial, Nat.cast_mul]
  have := (IH hx)
  have H : derivWithin (fun (z : ℂ) => (-1: ℂ) ^ k * ↑k ! * ((z + ↑d) ^ (k + 1))⁻¹) ℍ' x =
   (-1) ^ (↑k + 1) * ((↑k + 1) * ↑k !) * ((x + ↑d) ^ (↑k + 1 + 1))⁻¹ := by
    simp only [cpow_nat_cast, Opens.coe_mk]
    rw [DifferentiableAt.derivWithin]
    simp only [deriv_const_mul_field']
    rw [deriv_inv'']
    norm_cast
    rw [deriv_pow'']
    rw [deriv_add_const']
    rw  [deriv_id'']
    simp [deriv_pow'', differentiableAt_add_const_iff, differentiableAt_id', Nat.cast_add,
    algebraMap.coe_one, Nat.add_succ_sub_one, add_zero, deriv_add_const', deriv_id'', mul_one]
    rw [← pow_mul]
    norm_cast
    rw [pow_add]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_negSucc, zero_add, Nat.cast_one,
      Int.cast_ofNat, Nat.cast_add,pow_one, Nat.cast_mul, mul_neg, mul_one, Int.cast_add,
        Int.cast_one, neg_mul]
    have Hw : -(((k: ℂ) + 1) * (x + ↑d) ^ k) / (x + ↑d) ^ ((k + 1) * 2) = -(↑k + 1) / (x + ↑d) ^ (k + 2) :=
      by
      rw [div_eq_div_iff]
      norm_cast
      simp
      ring
      norm_cast
      apply pow_ne_zero ((k + 1) * 2) (upper_ne_int ⟨x, hx⟩ d)
      norm_cast
      apply pow_ne_zero (k + 2) (upper_ne_int ⟨x, hx⟩ d)
    norm_cast at *
    simp at *
    rw [Hw]
    ring
    rw [differentiableAt_add_const_iff]
    apply differentiableAt_id'
    norm_cast
    apply DifferentiableAt.pow
    rw [differentiableAt_add_const_iff]
    apply differentiableAt_id'
    norm_cast
    apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.inv
    norm_cast
    apply DifferentiableAt.pow
    rw [differentiableAt_add_const_iff]
    apply differentiableAt_id'
    norm_cast
    apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen hx
  rw [←H]
  apply derivWithin_congr
  norm_cast at *
  simp at *
  intro r hr
  apply IH hr
  norm_cast at *
  simp at *
  apply this
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen hx

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) ℍ')
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) ℍ' :=
  by
  intro x hx
  have h1 : (fun z : ℂ => 1 / (z - d)) = fun z : ℂ => 1 / (z + -d) := by rfl
  rw [h1]
  have h2 : x - d = x + -d := by rfl
  simp_rw [h2]
  simpa using aut_iter_deriv (-d : ℤ) k hx

theorem ineq11 (x y d : ℝ) :
    0 ≤ d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 - 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 :=
  by
  have h1 :
    d ^ 2 * (x ^ 2 + y ^ 2) ^ 2 - 2 * d * x * (x ^ 2 + y ^ 2) + x ^ 2 =
      (d * (x ^ 2 + y ^ 2) - x) ^ 2 :=by
        norm_cast
        ring
  rw [h1]
  have := pow_two_nonneg  (d * (x ^ 2 + y ^ 2) - x)
  simp at *
  norm_cast at *

theorem lowboundd (z : ℍ) (δ : ℝ) :
    (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) / (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 ≤
      (δ * z.1.1 - 1) ^ 2 + (δ * z.1.2) ^ 2 :=
  by
  have H1 :
    (δ * z.1.1 - 1) ^ 2 + (δ * z.1.2) ^ 2 = δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) - 2 * δ * z.1.1 + 1 :=
    by
    norm_cast
    ring
  simp only [UpperHalfPlane.coe_im,  UpperHalfPlane.coe_re] at H1
  rw [H1]
  rw [div_le_iff]
  have H2 :
     (δ ^ 2 * ((z.1.1) ^ 2 + z.1.2 ^ 2) - 2 * δ * z.1.1 + 1) *
        (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 =
      δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 -
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
        (z.1.1^ 2 + z.1.2 ^ 2) ^ 2:=
    by
    norm_cast
    ring
  norm_cast at H2
  simp at *
  rw [H2]
  rw [← sub_nonneg]
  have H4 :
    δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 3 -
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 +
          (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 -
        (z.1.2 ^ 4 + (z.1.1 * z.1.2) ^ 2) =
      (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 -
            2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
          z.1.1 ^ 2)   :=by
          norm_cast
          ring
  norm_cast at *
  rw [H4]
  have H5 :
    0 ≤
        δ ^ 2 * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ 2 -
          2 * δ * z.1.1 * (z.1.1 ^ 2 + z.1.2 ^ 2) +
        z.1.1 ^ 2  :=
    by apply ineq11
  have H6 : 0 ≤ z.1.1 ^ 2 + z.1.2 ^ 2 := by
    norm_cast
    nlinarith
  norm_cast
  have HH :=mul_nonneg H6 H5
  simp at *
  norm_cast at *
  have H8 : 0 < z.1.2 ^ 2 := by
    have := upper_half_im_pow_pos z 2
    norm_cast at *
  have H9 : 0 < z.1.2 ^ 2 + z.1.1 ^ 2 := by
    norm_cast
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos
    apply pow_two_nonneg
    norm_cast at *
  norm_cast
  apply sq_pos_of_ne_zero
  simp at H9
  norm_cast at H9
  linarith

theorem rfunt_bnd (z : ℍ) (δ : ℝ) : rfunct z ≤ Complex.abs (δ * (z : ℂ) - 1) :=
  by
  rw [rfunct]
  rw [Complex.abs]
  simp
  have H1 :
    Real.sqrt (lb z) ≤
      Real.sqrt ((δ * (z : ℂ).re - 1) * (δ * (z : ℂ).re - 1) + δ * (z : ℂ).im * (δ * (z : ℂ).im)) :=
    by
    rw [lb]
    rw [Real.sqrt_le_sqrt_iff]
    have := lowboundd z δ
    rw [← pow_two]
    rw [← pow_two]
    norm_cast at *
    nlinarith
  right
  rw [Complex.normSq_apply]
  simpa using H1

theorem upbnd (z : ℍ) (d : ℤ) : (d ^ 2 : ℝ) * rfunct z ^ 2 ≤ Complex.abs (z ^ 2 - d ^ 2) :=
  by
  by_cases hd : d ≠ 0
  have h1 : (z ^ 2 : ℂ) - d ^ 2 = d ^ 2 * (1 / d ^ 2 * z ^ 2 - 1) := by ring_nf; simp [hd]
  rw [h1]
  simp only [one_div, AbsoluteValue.map_mul, Complex.abs_pow]
  have h2 := rfunt_bnd z (1 / d)
  have h3 := (EisensteinSeries.auxlem z (1 / d)).2
  have h4 := mul_le_mul h2 h3 (rfunct_pos z).le (Complex.abs.nonneg _)
  rw [← AbsoluteValue.map_mul] at h4
  rw [← pow_two] at h4
  have h5 : Complex.abs (d: ℂ)^ 2 = d ^ 2 := by
    have := Complex.int_cast_abs (d^2)
    simp only [Int.cast_pow, _root_.abs_pow, map_pow] at this
    apply symm
    rw [← this]
    norm_cast
    rw [←   _root_.abs_pow]
    symm
    rw [abs_eq_self]
    apply pow_two_nonneg


  simp at *
  rw [h5]
  refine' mul_le_mul _ _ _ _
  simp
  convert h4
  norm_cast
  rw [← map_mul]
  congr
  norm_cast
  ring_nf
  simp
  apply mul_comm
  apply pow_nonneg
  apply (rfunct_pos z).le
  nlinarith
  simp at hd
  rw [hd]
  simp [Complex.abs.nonneg]

theorem upp_half_not_ints (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n :=
  by
  simp
  intro h
  have h1 := UpperHalfPlane.im_pos z
  have h2 : Complex.im n = 0 := int_cast_im n
  rw [UpperHalfPlane.im] at h1
  simp only [uhc] at *
  rw [h] at h1
  rw [h2] at h1
  simp at *

lemma upper_half_plane_ne_int_pow_two (z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0 := by
  intro h
  have h1 : (z : ℂ) ^ 2 - n ^ 2 = (z - n) * (z + n) := by
    norm_cast
    simp
    ring
  norm_cast at *
  rw [h1] at h
  simp at h
  cases' h with h h
  have := upp_half_not_ints z n
  rw [sub_eq_zero] at h
  apply absurd h this
  have := upp_half_not_ints z (-n)
  rw [add_eq_zero_iff_eq_neg] at h
  simp at *
  apply absurd h this

/-
theorem abs_pow_two_upp_half (z : ℍ) (n : ℤ) : 0 < Complex.abs ((z : ℂ) ^ 2 - n ^ 2) :=
  by
  simp
  intro h
  have h1 : (z : ℂ) ^ 2 - n ^ 2 = (z - n) * (z + n) := by
    norm_cast
    simp
    ring
  norm_cast at *
  simp
  rw [h1] at h
  simp at h
  cases' h with h h
  have := upp_half_not_ints z n
  rw [sub_eq_zero] at h
  apply absurd h this
  have := upp_half_not_ints z (-n)
  rw [add_eq_zero_iff_eq_neg] at h
  simp at *
  apply absurd h this
-/

lemma pnat_inv_sub_squares (z : ℍ) :
  (fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)) = fun n : ℕ+ => 2 * z.1 * (1 / (z ^ 2 - n ^ 2)):=
  by
  funext n
  field_simp
  rw [one_div_add_one_div]
  norm_cast
  ring_nf
  have h2 := upp_half_not_ints z n
  simp [h2, uhc] at *
  have h1 := upp_half_not_ints z (n)
  norm_cast at *
  rw [sub_eq_zero]
  exact h1
  have h1 := upp_half_not_ints z (-n)
  norm_cast at *
  rw [add_eq_zero_iff_eq_neg]
  simpa using h1

theorem aux_rie_sum (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
    Summable fun n : ℕ+ => Complex.abs (rfunct z ^ k * n ^ k)⁻¹ :=
  by
  simp
  rw [summable_mul_right_iff]
  have hkk : 1 < (k : ℝ):= by norm_cast at *
  have H := Real.summable_nat_rpow_inv.2 hkk
  norm_cast at *
  apply H.subtype
  simp
  intro H
  exfalso
  have := rfunct_ne_zero z
  exact this H


lemma summable_iff_abs_summable  {α : Type} (f : α → ℂ) :
Summable f ↔ Summable (fun (n: α) => Complex.abs (f n)) :=
 by
  apply summable_norm_iff.symm

theorem aux_rie_int_sum (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
    Summable fun n : ℤ => Complex.abs (rfunct z ^ k * n ^ k)⁻¹ :=
  by
  simp
  rw [summable_mul_right_iff]
  have hkk : 1 < (k : ℝ) := by
    norm_cast
  have :=  Real.summable_abs_int_rpow hkk
  simp at this
  norm_cast at this
  convert this
  simp
  norm_num
  intro H
  exfalso
  have := rfunct_ne_zero z
  exact this H




theorem lhs_summable (z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) :=
  by
  have h1 := pnat_inv_sub_squares z
  rw [h1]
  apply Summable.mul_left
  apply (summable_iff_abs_summable _).2
  simp
  have hs : Summable fun n : ℕ+ => (rfunct z ^ 2 * n ^ 2)⁻¹ :=
    by
    have := aux_rie_sum z 2 ?_
    simp at this
    norm_cast at *
    simp at *
    apply this
    rfl
  apply Summable.of_nonneg_of_le _ _ hs
  intro b
  rw [inv_nonneg]
  apply Complex.abs.nonneg
  intro b
  rw [inv_le_inv]
  rw [mul_comm]
  have := upbnd z b
  norm_cast at *
  simp at *
  simpa using  (upper_half_plane_ne_int_pow_two z b)
  apply mul_pos
  norm_cast
  apply pow_pos
  apply rfunct_pos
  have hb := b.2
  norm_cast
  apply pow_pos
  simpa using hb

/-
theorem lhs_summable_int (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
    Summable fun n : ℤ => 1 / ((z : ℂ) - n) ^ k := by
  have := Eise_on_square_is_bounded k z
  have h1 := aux_rie_int_sum z k hk
  apply summable_of_norm_bounded _ h1
  intro i
  simp
  have h2 := this (Int.natAbs (i)) (⟨1, -i⟩ : ℤ × ℤ)
  simp only [square_mem, Int.natAbs_one, Int.natAbs_neg, Int.natAbs_ofNat, ge_iff_le,
    max_eq_right_iff, Int.cast_one, one_mul, Int.cast_neg, Int.cast_ofNat, cpow_nat_cast, map_pow,
      map_mul, abs_ofReal, abs_cast_nat, mul_inv_rev] at h2
  sorry
-/

theorem lhs_summable_2 (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
    Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) ^ k :=
  by
  --have HT := int_pnat_sum _ (lhs_summable_int z k hk)
  --norm_cast at *
  have hk0 : 0 ≤ (k : ℤ) := by linarith
  have := Eise_on_square_is_bounded k hk0 z
  have h1 := aux_rie_sum z k hk
  apply Summable.of_norm_bounded _ h1
  intro i
  simp only [cpow_nat_cast, one_div, norm_inv, norm_pow, norm_eq_abs, mul_inv_rev, map_mul,
    map_inv₀, map_pow, abs_natCast, abs_ofReal]
  have h2 := this (i : ℕ) (⟨1, -i⟩ : ℤ × ℤ)
  simp only [square_mem, Int.natAbs_one, Int.natAbs_neg, Int.natAbs_ofNat, max_eq_right_iff,
    Int.cast_one, uhc, one_mul, Int.cast_neg, Int.cast_ofNat, zpow_coe_nat, map_pow, map_mul,
    abs_ofReal, abs_natCast, mul_inv_rev] at h2
  apply h2
  exact PNat.one_le i
  exact PNat.one_le i


theorem lhs_summable_2' (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
    Summable fun n : ℕ+ => 1 / ((z : ℂ) + n) ^ k :=
  by
  have hk0 : 0 ≤ (k : ℤ) := by linarith
  have := Eise_on_square_is_bounded k hk0 z
  have h1 := aux_rie_sum z k hk
  apply Summable.of_norm_bounded _ h1
  intro i
  simp only [cpow_nat_cast, one_div, norm_inv, norm_pow, norm_eq_abs, mul_inv_rev, map_mul,
    map_inv₀, map_pow, abs_natCast, abs_ofReal]
  have h2 := this (i : ℕ) (⟨1, i⟩ : ℤ × ℤ)
  simp only [square_mem, Int.natAbs_one, Int.natAbs_ofNat, max_eq_right_iff, Int.cast_one, uhc,
    one_mul, Int.cast_ofNat, zpow_coe_nat, map_pow, map_mul, abs_ofReal, abs_natCast,
    mul_inv_rev] at h2
  apply h2
  exact PNat.one_le i
  exact PNat.one_le i


/-
lemma tsums_added (k : ℕ) (hk : 3 ≤ k)(z : ℍ ):
  ∑' (n : ℕ+), (1/((z : ℂ)-n)^k+1/(z+n)^k) = ∑' (d : ℤ), 1/(z-d)^k :=
begin
sorry,
end





lemma sum_aux (r : ℝ) (hr : r < 1) (hr2 : 0 ≤ r) :
  summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n) * r^n)) :=
begin
simp,
have h2ne : (2 : ℝ) ≠ 0, by {exact ne_zero.ne 2},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
rw ←summable_mul_left_iff,
have H : ‖ r ‖ < 1, by {simp  [hr, hr2], rw _root_.abs_of_nonneg hr2, exact hr},
have := summable_norm_pow_mul_geometric_of_norm_lt_1  1 H,
simpa using this,
simpa using real.pi_ne_zero,
end
-/
--EXPERIMENTAL THINGS
theorem aut_contDiffOn (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d)) ℍ' :=
  by
  simp only [one_div, Opens.coe_mk]
  apply ContDiffOn.inv
  apply ContDiffOn.sub
  apply contDiffOn_id
  apply contDiffOn_const
  intro x hx
  have := upper_ne_int ⟨x, hx⟩ (-d)
  norm_cast at *
  simp at *
  rw [add_neg_eq_zero] at this
  rw [sub_eq_zero]
  convert this


/-
lemma continuous_on_tsum'
  {f : ℕ → ℂ → ℂ} {s : set ℂ}  (hf : ∀ i, continuous_on (f i) s) (hs : is_open s)
  (hu : ∀ K ⊆ s, is_compact K →
    (∃ (u : ℕ → ℝ), ( summable u ∧ ∀ (n : ℕ) (k : K), (complex.abs ((f n) k)) ≤ u n ))):
  continuous_on (λ x, ∑' n, f n x) s :=
begin
  have : tendsto_locally_uniformly_on (λ N, (λ x, ∑ n in finset.range N, f n x))
  (λ x, ∑' n, f n x) at_top s, by {
   rw tendsto_locally_uniformly_on_iff_forall_is_compact,
   intros K hK1 hK2,
   have HU := hu K hK1 hK2,
   obtain ⟨u, h1, h2⟩ := HU,
   apply tendsto_uniformly_on_tsum_nat,
   apply h1,
   simp at *,
   intros n x hx,
   apply h2 n ⟨x, hx⟩,
   exact hs,},
  apply this.continuous_on,
  apply (eventually_of_forall _),
  assume t,
  simp,
  apply continuous_on_finset_sum,
  intros i hi,
  apply hf,
end

-/
theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) ℍ')
      ((fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1)))
      ℍ' :=
  by
  intro x hx
  have h1 :
    (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) =
      (fun z : ℂ => 1 / (z - d)) + fun z : ℂ => 1 / (z + d) :=
    by rfl
  rw [h1]
  have := iter_deriv_within_add k ⟨x, hx⟩ (fun z : ℂ => 1 / (z - d)) fun z : ℂ => 1 / (z + d)
  simp at *
  rw [this]
  · have h2 := aut_iter_deriv d k hx
    have h3 := aut_iter_deriv' d k hx
    simp at *
    rw [h2, h3]
  · have h4 := aut_contDiffOn d k
    simp at h4
    apply h4
  · have h5 := aut_contDiffOn (-d) k
    simp at h5
    apply h5

theorem summable_iter_aut (k : ℕ) (z : ℍ) :
    Summable fun n : ℕ+ => iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) ℍ' z :=
  by
  have := fun d : ℕ+ => iter_div_aut_add d k z.2
  simp at *
  have ht := (summable_congr this).2 ?_
  norm_cast at *
  by_cases hk : 1 ≤ k
  apply Summable.add
  rw [summable_mul_left_iff]
  have h1 := lhs_summable_2 z (k + 1)
  norm_cast at *
  simp at *
  apply h1
  linarith
  simp only [Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero]
  apply Nat.factorial_ne_zero
  rw [summable_mul_left_iff]
  have h2 := lhs_summable_2' z (k + 1)
  norm_cast at *
  simp at *
  apply h2
  linarith
  simp only [Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero]
  apply Nat.factorial_ne_zero
  simp at hk
  simp_rw [hk]
  simp
  simpa using lhs_summable z

theorem diff_on_aux (k : ℕ) (n : ℕ+) :
    DifferentiableOn ℂ
      ((fun t : ℂ => (-1 : ℂ) ^ k * k ! * (1 / (t - n) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + n) ^ (k + 1)))
      ℍ' :=
  by
  apply DifferentiableOn.add
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.div
  apply differentiableOn_const
  norm_cast
  apply DifferentiableOn.pow
  rw [differentiableOn_sub_const_iff]
  apply differentiableOn_id
  intro x hx
  norm_cast
  apply pow_ne_zero
  have := upper_ne_int ⟨x, hx⟩ (-n : ℤ)
  simp at *
  exact this
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.div
  apply differentiableOn_const
  norm_cast
  apply DifferentiableOn.pow
  rw [differentiableOn_add_const_iff]
  apply differentiableOn_id
  intro x hx
  norm_cast
  apply pow_ne_zero
  have := upper_ne_int ⟨x, hx⟩ (n : ℤ)
  simp at *
  exact this

theorem diff_at_aux (s : ℍ') (k : ℕ) (n : ℕ+) :
    DifferentiableAt ℂ
      (fun z : ℂ => iteratedDerivWithin k (fun z : ℂ => (z - ↑n)⁻¹ + (z + ↑n)⁻¹) upperHalfSpace z)
      ↑s :=
  by
  have := iter_div_aut_add n k
  apply DifferentiableOn.differentiableAt
  apply DifferentiableOn.congr (diff_on_aux k n)
  intro r hr
  have ht := this hr
  simp at *
  apply ht
  apply IsOpen.mem_nhds
  apply upper_half_plane_isOpen
  apply s.2

theorem der_of_iter_der (s : ℍ'.1) (k : ℕ) (n : ℕ+) :
    deriv
        (fun z : ℂ =>
          iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) upperHalfSpace z)
        s =
      (-1) ^ (k + 1) * (k + 1)! * (1 / (s - n) ^ (k + 2)) +
        (-1) ^ (k + 1) * (k + 1)! * (1 / (s + n) ^ (k + 2)) :=
  by
  have h :
    deriv
        (fun z : ℂ =>
          iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) upperHalfSpace z)
        s =
      derivWithin
        (fun z : ℂ =>
          iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹)  upperHalfSpace z)
        ℍ' s :=
    by
    apply symm; apply DifferentiableAt.derivWithin
    apply diff_at_aux
    apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
    apply s.2
  rw [h]
  simp
  rw [← iteratedDerivWithin_succ]
  have h2 := iter_div_aut_add n (k + 1) s.2
  simp at h2
  norm_cast at *
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen _ s.2

theorem rfunct_abs_pos (z : ℍ') : 0 < |rfunct z| :=
  by
  simpa using rfunct_ne_zero z

theorem sub_bound (s : ℍ'.1) (A B : ℝ) (hB : 0 < B) (hs : s ∈ upperHalfSpaceSlice A B) (k : ℕ)
    (n : ℕ+) :
    Complex.abs ((-1) ^ (k + 1) * (k + 1)! * (1 / (s - n) ^ (k + 2))) ≤
      Complex.abs ((k + 1)! / rfunct (lbpoint A B hB) ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹ :=
  by
  simp
  rw [div_eq_mul_inv]
  simp_rw [mul_assoc]
  norm_cast
  simp
  rw [mul_le_mul_left]
  have hk : 1 ≤ (k + 2 : ℤ) := by linarith
  have hk20 : 0 ≤ (k + 2 : ℤ) := by linarith
  have := Eise_on_square_is_bounded'' (k + 2) hk20 s n hk ⟨1, -(n : ℤ)⟩
  have hn : 1 ≤ (n : ℕ) := by have hn2 := n.2; norm_cast;
  simp at this
  have ht := this hn
  norm_cast at *
  simp at ht
  apply le_trans ht
  nth_rw 1 [mul_comm]
  simp
  norm_cast
  rw [inv_le_inv]
  apply pow_le_pow_left
  apply (rfunct_abs_pos _).le
  have hss := rfunct_lower_bound_on_slice A B hB ⟨s, hs⟩
  rw [abs_of_pos (rfunct_pos _)]
  rw [abs_of_pos (rfunct_pos _)]
  apply hss
  apply pow_pos (rfunct_abs_pos _)
  apply pow_pos (rfunct_abs_pos _)
  norm_cast
  apply Nat.factorial_pos


theorem add_bound (s : ℍ'.1) (A B : ℝ) (hB : 0 < B) (hs : s ∈ upperHalfSpaceSlice A B) (k : ℕ)
    (n : ℕ+) :
    Complex.abs ((-1) ^ (k + 1) * (k + 1)! * (1 / (s + n) ^ (k + 2))) ≤
      Complex.abs ((k + 1)! / rfunct (lbpoint A B hB) ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹ :=
  by
  simp
  rw [div_eq_mul_inv]
  simp_rw [mul_assoc]
  norm_cast
  simp
  rw [mul_le_mul_left]
  have hk : 1 ≤ (k + 2 : ℤ) := by linarith
  have hk20 : 0 ≤ (k + 2 : ℤ) := by linarith
  have := Eise_on_square_is_bounded'' (k + 2) hk20 s n hk ⟨1, (n : ℤ)⟩
  have hn : 1 ≤ (n : ℕ) := by have hn2 := n.2; norm_cast;
  simp at this
  have ht := this hn
  norm_cast at *
  simp at ht
  apply le_trans ht
  nth_rw 1 [mul_comm]
  simp
  norm_cast
  rw [inv_le_inv]
  apply pow_le_pow_left
  apply (rfunct_abs_pos _).le
  have hss := rfunct_lower_bound_on_slice A B hB ⟨s, hs⟩
  rw [abs_of_pos (rfunct_pos _)]
  rw [abs_of_pos (rfunct_pos _)]
  apply hss
  apply pow_pos (rfunct_abs_pos _)
  apply pow_pos (rfunct_abs_pos _)
  norm_cast
  apply Nat.factorial_pos


theorem upper_bnd_summable (A B : ℝ) (hB : 0 < B) (k : ℕ) :
    Summable fun a : ℕ+ =>
      2 * Complex.abs ((k + 1)! / rfunct (lbpoint A B hB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹ :=
  by
  rw [summable_mul_left_iff]
  have hk : 1 < (k : ℝ) + 2 := by norm_cast; linarith
  have H := Real.summable_nat_rpow_inv.2 hk
  norm_cast at *
  apply Summable.subtype H
  simp [Nat.cast_mul, Nat.cast_add, algebraMap.coe_one, map_div₀, Complex.abs_pow,
    Ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero, div_eq_zero_iff, AbsoluteValue.eq_zero,
    Nat.cast_eq_zero, pow_eq_zero_iff, Nat.succ_pos', abs_eq_zero, false_or_iff]
  apply not_or_of_not
  norm_cast
  apply Nat.factorial_ne_zero
  have hr := rfunct_ne_zero (lbpoint A B hB)
  intro h
  norm_cast at *

theorem aut_bound_on_comp (K : Set ℂ) (hk : K ⊆ ℍ'.1) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
          Complex.abs
              (deriv
                (fun z : ℂ =>
                  iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) upperHalfSpace z)
                s) ≤
            u n :=
  by
  by_cases h1 : Set.Nonempty K
  have H := compact_in_slice' K h1 hk hk2
  obtain ⟨A, B, hB, hAB⟩ := H
  refine'
    ⟨fun a : ℕ+ => 2 * Complex.abs ((k + 1)! / rfunct (lbpoint A B hB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹,
      _, _⟩
  exact upper_bnd_summable A B hB k
  intro n s
  have hr := der_of_iter_der ⟨s.1, hk s.2⟩ k n
  simp  at *
  rw [hr]
  apply le_trans (Complex.abs.add_le _ _)
  simp_rw [mul_assoc]
  rw [two_mul]
  apply add_le_add
  have he1 := sub_bound ⟨s.1, hk s.2⟩ A B hB ?_ k n
  simp_rw [div_eq_mul_inv] at *
  simp at *
  norm_cast at *
  simp at *
  apply hAB
  simp
  have he1 := add_bound ⟨s.1, hk s.2⟩ A B hB ?_ k n
  simp_rw [div_eq_mul_inv] at *
  simp  at *
  norm_cast at *

  apply hAB
  simp  at *
  refine' ⟨fun _ => 0, _, _⟩
  apply summable_zero
  intro n
  rw [not_nonempty_iff_eq_empty] at h1
  intro r
  exfalso
  have hr := r.2
  simp_rw [h1] at hr
  simp at hr


theorem aut_bound_on_comp' (K : Set ℂ) (hk : K ⊆ ℍ'.1) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
          Complex.abs
              (deriv
                (fun z : ℂ =>
                  (-1 : ℂ) ^ k * ↑k ! / (z - (n : ℂ)) ^ (k + 1) +
                    (-1) ^ k * ↑k ! / (z + n) ^ (k + 1))
                s) ≤
            u n :=
  by
  have := aut_bound_on_comp K hk hk2 k
  obtain ⟨u, hu, H⟩ := this
  refine' ⟨u, hu, _⟩
  intro n s
  have H2 := H n s
  simp at *
  have H4 :
    Complex.abs
        (deriv
          (fun z : ℂ =>
            (-1) ^ k * ↑k ! / (z - ↑↑n) ^ (k + 1) + (-1) ^ k * ↑k ! / (z + ↑↑n) ^ (k + 1))
          ↑s) =
      Complex.abs
        (deriv (iteratedDerivWithin k (fun z : ℂ => (z - ↑↑n)⁻¹ + (z + ↑↑n)⁻¹) upperHalfSpace)
          ↑s) :=
    by
    apply congr_arg
    apply Filter.EventuallyEq.deriv_eq
    rw [eventuallyEq_iff_exists_mem]
    use ℍ'
    constructor
    apply IsOpen.mem_nhds upper_half_plane_isOpen
    apply hk s.2
    apply EqOn.symm
    simpa using iter_div_aut_add n k
  simp only [ge_iff_le] at *
  norm_cast at *
  rw [H4]
  apply H2

theorem aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ') :
    iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ' x =
      ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) ℍ' x :=
  by
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero]
  rw [iteratedDerivWithin_succ]
  have HH :
    derivWithin (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ') ℍ'
        x =
      derivWithin
        (fun z => ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) ℍ' z) ℍ'
        x :=
    by
    apply derivWithin_congr
    intro y hy
    apply IH ⟨y, hy⟩
    apply IH x
  simp_rw [HH]
  simp
  rw [deriv_tsum_fun']
  apply tsum_congr
  intro b
  rw [iteratedDerivWithin_succ]
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen x.2
  exact upper_half_plane_isOpen
  exact x.2
  intro y hy
  simpa using summable_iter_aut k ⟨y, hy⟩
  intro K hK hK2
  apply aut_bound_on_comp K hK hK2 k
  intro n r
  apply diff_at_aux r k n
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen
  exact x.2

theorem tsum_ider_der_eq (k : ℕ) (x : ℍ') :
    ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) ℍ' x =
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))) :=
  by
  apply tsum_congr
  intro b
  have h2 := iter_div_aut_add b k x.2
  simpa using h2

theorem auxp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ')
      (fun x : ℂ =>
        ∑' n : ℕ+,
          ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))))
      ℍ' :=
  by
  intro x hx
  have := aut_series_ite_deriv_uexp2 k ⟨x, hx⟩
  simp at *
  rw [this]
  have h2 := tsum_ider_der_eq k ⟨x, hx⟩
  simpa using h2

theorem summable_3 (m : ℕ) (y : ℍ') :
    Summable fun n : ℕ+ =>
      (-1 : ℂ) ^ m * ↑m ! * (1 / (y - ↑n) ^ (m + 1)) + (-1) ^ m * ↑m ! * (1 / (y + ↑n) ^ (m + 1)) :=
  by
  by_cases hm : m = 0
  simp_rw [hm]
  simp
  have := lhs_summable y
  simpa using this
  have hm2 : 2 ≤ m + 1 := by
    have : 1 ≤ m := by
      apply Nat.one_le_iff_ne_zero.mpr hm;
    linarith
  simp_rw [← mul_add]
  rw [summable_mul_left_iff]
  apply Summable.add
  have := lhs_summable_2 y (m + 1) hm2
  norm_cast at *
  have := lhs_summable_2' y (m + 1) hm2
  norm_cast at *
  simp [Nat.factorial_ne_zero]



theorem tsum_aexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ' :=
  by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm
  have h1 := auxp_series_ite_deriv_uexp''' m
  apply DifferentiableOn.congr _ h1
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  apply hasDerivWithinAt_tsum_fun _ upper_half_plane_isOpen
  apply hx
  intro y hy
  apply summable_3 m ⟨y, hy⟩
  intro K hK1 hK2
  have := aut_bound_on_comp' K hK1 hK2 m
  obtain ⟨u, hu, H⟩ := this
  refine' ⟨u, hu, _⟩
  intro n s
  simpa using H n s
  intro n r
  have hN : ℍ'.1 ∈ 𝓝 r.1 := by apply IsOpen.mem_nhds upper_half_plane_isOpen; exact r.2
  have:= (diff_on_aux m n)
  apply DifferentiableOn.differentiableAt
  simp at *
  norm_cast at *
  simpa using hN


theorem summable_factor (n : ℤ) (z : ℍ) (k : ℤ) (hk : 3 ≤ k) :
    Summable fun d : ℤ => ((-((n : ℂ) * z) + d) ^ k)⁻¹ :=
  by
  have H := Eisenstein_tsum_summable k z hk
  have H2 := H.prod_factor (-n)
  simp_rw [eise] at H2
  simp at *
  exact H2

theorem aux_iter_der_tsum (k : ℕ) (hk : 2 ≤ k) (x : ℍ') :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ' x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) :=
  by
  rw [iter_deriv_within_add]
  · have h1 := aut_iter_deriv 0 k x.2
    simp  at *
    rw [h1]
    have := aut_series_ite_deriv_uexp2 k x
    simp at *
    rw [this]
    have h2 := tsum_ider_der_eq k x
    simp at h2
    rw [h2]
    rw [int_tsum_pNat]
    · simp
      rw [tsum_add]
      · rw [tsum_mul_left]
        rw [tsum_mul_left]
        rw [mul_add]
        rw [mul_add]
        conv =>
          enter [2]
          rw [add_assoc]
          conv =>
            enter [2]
            rw [add_comm]
      rw [summable_mul_left_iff]
      · have hk2 : 2 ≤ k + 1 := by linarith
        simpa using lhs_summable_2 x (k + 1) hk2
      · simp only [Nat.factorial_ne_zero, Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero,
          not_false_iff]
      · rw [summable_mul_left_iff]
        · have hk2 : 2 ≤ k + 1 := by linarith
          simpa using lhs_summable_2' x (k + 1) hk2
        · simp only [Nat.factorial_ne_zero, Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero,
            not_false_iff]
    · have hk3 : 3 ≤ (k + 1 : ℤ) := by linarith
      have := summable_factor (-1 : ℤ) x (k + 1) hk3
      simpa using this
  · have := aut_contDiffOn 0 k
    simpa using this
  · apply tsum_aexp_contDiffOn k

theorem aux_iter_der_tsum_eqOn (k : ℕ) (hk : 3 ≤ k) :
    EqOn
      (iteratedDerivWithin (k - 1)
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) ℍ')
      (fun z : ℂ => (-1) ^ (k - 1) * (k - 1)! * ∑' n : ℤ, 1 / (z + n) ^ (k : ℕ)) ℍ' :=
  by
  intro z hz
  have hk0 : 2 ≤ k - 1 := le_tsub_of_add_le_left hk
  have := aux_iter_der_tsum (k - 1) hk0 ⟨z, hz⟩
  have hk1 : k - 1 + 1 = k := by
    apply Nat.sub_add_cancel
    linarith
  rw [hk1] at this
  norm_cast at *


theorem neg_even_pow (n : ℤ) (k : ℕ) (hk : Even k) : (-n) ^ k = n ^ k :=
  Even.neg_pow hk n

theorem complex_rie_summable (k : ℕ) (hk : 3 ≤ k) : Summable fun n : ℕ => ((n : ℂ) ^ k)⁻¹ :=
  by
  have hkk : 1 < (k : ℝ):= by
    norm_cast
    linarith
  have H := Real.summable_nat_rpow_inv.2 hkk
  norm_cast at *
  simp_rw [inv_eq_one_div]
  have H2 : (fun n : ℕ => 1 / (n : ℂ) ^ k) = (Complex.ofReal' ) ∘ fun (n : ℕ)  => 1 / (n : ℝ) ^ k :=
    by
    funext
    simp
  simp at *
  rw [H2]
  rw [coe_summable]
  apply Summable.congr H
  intro b
  simp

@[simp]
lemma Complex.summable_nat_pow_inv {p : ℕ} :  (Summable fun n : ℤ =>  ((n : ℂ) ^ p)⁻¹) ↔ 1 < p := by
  simp_rw [inv_eq_one_div]
  have H2 : ∀ (k : ℕ), (fun n : ℤ => 1 / (n : ℂ) ^ k) = (Complex.ofReal' ) ∘ fun (n : ℤ)  => 1 / (n : ℝ) ^ k :=
    by
    intro k
    funext
    simp
  constructor
  intro h
  have := H2 p
  simp at *
  rw [this] at h
  rw [ ←Real.summable_one_div_int_pow]
  simp at *
  rw [coe_summable] at h
  apply Summable.congr h
  simp at *
  intro h
  simp at *
  rw [H2 p]
  rw [coe_summable]
  simpa using (Real.summable_one_div_int_pow.2 h)
