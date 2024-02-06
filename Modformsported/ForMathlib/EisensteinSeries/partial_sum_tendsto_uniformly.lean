/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Modformsported.ForMathlib.EisensteinSeries.summable
import Modformsported.ForMathlib.ModForms2
import Modformsported.ModForms.HolomorphicFunctions
import Modformsported.ModForms.WeierstrassMTest
import Mathlib.NumberTheory.ZetaFunction

open Complex

open scoped BigOperators NNReal Classical Filter UpperHalfPlane Manifold Set

open ModularForm

open SlashInvariantForm

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

noncomputable section

namespace EisensteinSeries

/-lemmas to move-/

theorem complex_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (∑ i in s, f i) ≤ ∑ i in s, Complex.abs (f i) :=
  abv_sum_le_sum_abv (fun k : ι => f k) s

@[simp]
lemma uhc (z : ℍ) : (z : ℂ) = z.1 := by rfl

theorem div_self_add_eq_one_div_div_add_one (a b : ℝ) (h : a ≠ 0) : a / (a + b) = 1 / (b / a + 1) :=
  by
  rw [add_comm]
  field_simp

theorem aux4 (a b : ℝ) (h : 0 < b) :
    (b ^ 4 + (a * b) ^ 2) / (a ^ 2 + b ^ 2) ^ 2 = 1 / ((a / b) ^ 2 + 1) :=
  by
  field_simp
  ring

section upperHalfSpaceslices

def upperHalfSpaceSlice (A B : ℝ) :=
  {z : ℍ' | Complex.abs z.1.1 ≤ A ∧ B ≤ Complex.abs z.1.2}

/-- Canonical point in the `A B` slice-/
def lbpoint (A B : ℝ) (h : 0 < B) : ℍ :=
  ⟨⟨A, B⟩, by simp [h]⟩

instance sliceCoe (A B : ℝ) : CoeOut (upperHalfSpaceSlice A B) ℍ :=
  ⟨fun x : upperHalfSpaceSlice A B => (x : ℍ')⟩

theorem slice_mem (A B : ℝ) (z : ℍ) :
    z ∈ upperHalfSpaceSlice A B ↔ Complex.abs z.1.1 ≤ A ∧ Complex.abs z.1.2 ≥ B :=
  Iff.rfl

instance nonemp (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) : Nonempty (upperHalfSpaceSlice A B) :=
  by
  refine ⟨⟨(⟨A, B⟩ : ℂ), ?_⟩, ?_⟩
  · simp [UpperHalfPlane.upperHalfSpace, hb]
  · simp [upperHalfSpaceSlice, le_abs_self, abs_eq_self.2 ha]

theorem ball_in_upper_half (z : ℍ') (A B ε : ℝ) (hε : 0 < ε) (hBε : ε < B)
    (h : Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B) :
    Metric.closedBall z.1 ε ⊆ UpperHalfPlane.upperHalfSpace :=
  by
  intro x hx
  simp only [Metric.mem_closedBall] at hx
  simp only [UpperHalfPlane.upperHalfSpace, Set.mem_setOf_eq]
  rw [Metric.closedBall] at h
  have hz : z ∈ upperHalfSpaceSlice A B := by apply h; simp [hε.le]
  have hzB : B ≤ Complex.abs z.1.2 := hz.2
  rw [dist_eq_norm, norm_eq_abs] at hx
  have h3 := le_trans (abs_im_le_abs (x - z.1)) hx
  rw [sub_im, abs_sub_comm] at h3
  have h33 : -ε ≤ -|z.1.im - x.im| := by simp only [neg_le_neg_iff]; apply h3
  simp only [abs_ofReal] at hzB
  have h6 : B - ε ≤ |z.1.im| - |z.1.im - x.im| := by simp at *; linarith
  by_contra! hc
  have hcc : 0 ≤ -x.im := by exact neg_nonneg.mpr hc
  have hzc : |z.1.im - x.im| = z.1.im - x.im := by
    apply _root_.abs_of_nonneg
    rw [sub_eq_add_neg]
    apply add_nonneg
    · have := UpperHalfPlane.im_pos z
      apply this.le
    · apply hcc
  have hzp : |z.1.im| = z.1.im := _root_.abs_of_nonneg (UpperHalfPlane.im_pos z).le
  simp_rw [hzc, hzp, sub_sub_cancel] at h6
  linarith

theorem closedBall_in_slice (z : ℍ') :
    ∃ A B ε : ℝ, 0 < ε ∧ 0 < B ∧ Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧ 0 ≤ A ∧ ε < B :=
  by
  let e := 3⁻¹ * Complex.abs z.1.2
  let a := Complex.abs z.1.2 + Complex.abs z
  let b := Complex.abs z.1.2 - e
  refine ⟨a, b, e, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [abs_ofReal, gt_iff_lt, inv_pos, zero_lt_three,mul_pos_iff_of_pos_left, abs_pos, ne_eq]
    apply UpperHalfPlane.im_ne_zero z
  · ring_nf
    simp [UpperHalfPlane.coe_im]
    apply mul_pos
    · rw [abs_pos, ne_eq]
      apply UpperHalfPlane.im_ne_zero z
    · norm_num
  · intro x
    simp only [abs_ofReal, Metric.mem_closedBall, TopologicalSpace.Opens.coe_mk]
    intro hxz
    have d1 : dist x z = dist (x : ℂ) (z : ℂ) := Subtype.dist_eq x z
    rw [d1] at hxz
    rw [dist_eq_norm] at hxz
    simp only [norm_eq_abs] at hxz
    have := Complex.abs.sub_le (x : ℂ) (z : ℂ) 0
    simp only [sub_zero] at this
    simp only [upperHalfSpaceSlice, abs_ofReal, tsub_le_iff_right, Set.mem_setOf_eq]
    constructor
    · have hre := le_trans (abs_re_le_abs x.1) this
      apply le_trans hre
      simp only [add_le_add_iff_right]
      apply le_trans hxz
      apply mul_le_of_le_one_left (abs_nonneg _)
      norm_num
    have ineq1 := _root_.abs_sub_le z.1.2 x.1.2 0
    simp only [sub_zero] at ineq1
    apply le_trans ineq1
    rw [add_comm]
    simp only [add_le_add_iff_left]
    have ki := le_trans (abs_im_le_abs (x.1 - z.1)) hxz
    rwa [sub_im, abs_sub_comm] at ki
  · apply add_nonneg
    · apply Complex.abs.nonneg
    · apply Complex.abs.nonneg
  · ring_nf
    rw [← sub_pos]
    have hr : 0 < Complex.abs z.1.im := by simp; apply UpperHalfPlane.im_ne_zero z
    have hxim : 0 < |(z : ℂ).im| := by norm_cast at *
    simp only [abs_ofReal, Int.ofNat_eq_coe, Nat.cast_ofNat, Int.int_cast_ofNat, Nat.cast_one, Int.cast_one,
      sub_pos, gt_iff_lt, abs_pos, ne_eq]
    linarith

open Set Metric UpperHalfPlane

theorem mem_uhs (x : ℂ) : x ∈ ℍ'.1 ↔ 0 < x.im := by rfl

theorem compact_in_slice' (S : Set ℂ) (hne : Set.Nonempty S) (hs : S ⊆ ℍ') (hs2 : IsCompact S) :
    ∃ A B : ℝ, 0 < B ∧ Set.image (Set.inclusion hs) univ ⊆ upperHalfSpaceSlice A B :=
  by
  have hcts : ContinuousOn (fun t => Complex.im t) S := by apply Continuous.continuousOn; continuity
  have := IsCompact.exists_isMinOn hs2 hne hcts
  obtain ⟨b, hb, HB⟩ := this
  have hh : IsCompact (Set.image (inclusion hs) univ) := by
    apply IsCompact.image_of_continuousOn
    · exact isCompact_iff_isCompact_univ.mp hs2
    · exact continuous_inclusion hs |>.continuousOn
  let t := (⟨Complex.I, by simp⟩ : ℍ)
  have hb2 := _root_.Bornology.IsBounded.subset_ball_lt hh.isBounded 0 t
  obtain ⟨r, -, hr2⟩ := hb2
  refine ⟨r + 1, b.im, ?_, ?_⟩
  · simpa only [TopologicalSpace.Opens.coe_mk, UpperHalfPlane.mem_upperHalfSpace] using hs hb
  intro z hz
  simp only [TopologicalSpace.Opens.coe_mk, image_univ, range_inclusion, mem_setOf_eq] at *
  rw [slice_mem]
  simp only [abs_ofReal, ge_iff_le]
  constructor
  · apply le_trans (abs_re_le_abs z)
    have := Complex.abs.sub_le (z : ℂ) (t : ℂ) 0
    simp only [sub_zero, Subtype.coe_mk, abs_I] at this
    apply le_trans this
    simp only [add_le_add_iff_right]
    have hr3 := hr2 hz
    simp_rw [mem_ball, Subtype.dist_eq, dist_eq] at hr3
    apply hr3.le
  have hbz := HB hz
  simp only [mem_setOf_eq] at hbz
  apply hbz.trans <| le_abs_self _

/-- The sum of Eise over the `square`'s-/
def eisenSquare (k : ℤ) (n : ℕ) : ℍ → ℂ := fun z => ∑ x in square n, eise k z x

def eisenSquare' (k : ℤ) (n : ℕ) : ℍ' → ℂ := fun z : ℍ' => ∑ x in Finset.range n, eisenSquare k x z

theorem Eisenstein_series_is_sum_eisen_squares (k : ℤ) (z : ℍ) (h : 3 ≤ k) :
    Eisenstein_tsum k z = ∑' n : ℕ, eisenSquare k n z :=
  by
  rw [Eisenstein_tsum]; simp_rw [eisenSquare]
  have HI :=squares_cover_all
  let g := fun y : ℤ × ℤ => (eise k z) y
  have hgsumm : Summable g := by apply Eisenstein_tsum_summable k z h
  have index_lem := tsum_lemma g (fun (n : ℕ) => square n) HI hgsumm;
  exact index_lem

def eisenSquareSlice (k : ℤ) (A B : ℝ) (n : ℕ) : upperHalfSpaceSlice A B → ℂ := fun x =>
  eisenSquare k n (x : ℍ')

def eisenParSumSlice (k : ℤ) (A B : ℝ) (n : ℕ) : upperHalfSpaceSlice A B → ℂ := fun z =>
  ∑ x in Finset.range n, eisenSquareSlice k A B x z

def eisensteinSeriesRestrict (k : ℤ) (A B : ℝ) : upperHalfSpaceSlice A B → ℂ := fun x =>
  Eisenstein_tsum k (x : ℍ')


section rfunct_bounds

theorem rfunct_lower_bound_on_slice (A B : ℝ) (h : 0 < B) (z : upperHalfSpaceSlice A B) :
    rfunct (lbpoint A B h) ≤ rfunct z.1 := by
  simp_rw [lbpoint]
  have zpos := UpperHalfPlane.im_pos z.1
  have hz := z.2
  rw [slice_mem] at hz
  simp only [abs_ofReal, ge_iff_le] at hz
  rw [rfunct, rfunct]
  apply min_le_min
  · dsimp only
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_eq_self.mpr h.le]
    exact hz.2
  simp_rw [lb]
  rw [Real.sqrt_le_sqrt_iff]
  have := aux4 (z : ℂ).re (z : ℂ).im zpos
  simp only [uhc, div_pow, one_div] at this
  rw [this, aux4 A B h, one_div, inv_le_inv, add_le_add_iff_right, div_pow]
  apply div_le_div (sq_nonneg _)
  · simpa [even_two.pow_abs] using pow_le_pow_left (abs_nonneg _) hz.1 2
  · positivity
  · simpa [even_two.pow_abs] using pow_le_pow_left h.le hz.2 2
  · positivity
  · positivity
  · positivity

theorem rfunctbound (k : ℕ) (A B : ℝ) (hb : 0 < B) (z : upperHalfSpaceSlice A B) :
    8 / rfunct (z : ℍ') ^ k * Complex.abs (riemannZeta (k - 1)) ≤
      8 / rfunct (lbpoint A B hb) ^ k * Complex.abs (riemannZeta (k - 1))  :=
  by
  have h1 := rfunct_lower_bound_on_slice A B hb z
  simp only at h1
  have v2 : 0 ≤ rfunct (lbpoint A B hb) := by have := rfunct_pos (lbpoint A B hb); linarith
  have h2 := pow_le_pow_left v2 h1 k
  ring_nf
  rw [← inv_le_inv] at h2
  have h3 : 0 ≤ Complex.abs (riemannZeta (k - 1)) := by
    apply Complex.abs.nonneg
  norm_cast
  simp only [inv_pow, Int.negSucc_add_ofNat, Int.cast_subNatNat, Nat.cast_one, ge_iff_le]

  nlinarith
  apply pow_pos
  apply rfunct_pos
  apply pow_pos
  apply rfunct_pos

theorem rfunctbound' (k : ℕ) (A B : ℝ) (hb : 0 < B) (z : upperHalfSpaceSlice A B) (n : ℕ) :
    8 / rfunct (z : ℍ') ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ ≤
      8 / rfunct (lbpoint A B hb) ^ k * ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ :=
  by
  have h1 := rfunct_lower_bound_on_slice A B hb z
  simp
  have v2 : 0 ≤ rfunct (lbpoint A B hb) := by have := rfunct_pos (lbpoint A B hb); linarith
  have h2 := pow_le_pow_left v2 h1 k
  have h3 : 0 ≤ ((n : ℝ) ^ ((k : ℤ) - 1))⁻¹ := by
    simp only [one_div, inv_nonneg]
    apply zpow_nonneg
    simp only [Nat.cast_nonneg]
  apply mul_le_mul_of_nonneg_right ?_ h3
  ring_nf
  apply mul_le_mul_of_nonneg_right ?_ ?_
  rw [← inv_le_inv] at h2
  simp
  exact h2
  apply pow_pos
  apply rfunct_pos
  apply pow_pos
  apply rfunct_pos
  linarith

theorem Eisenstein_series_is_sum_eisen_squares_slice (k : ℤ) (h : 3 ≤ k) (A B : ℝ)
    (z : upperHalfSpaceSlice A B) :
    eisensteinSeriesRestrict k A B z = ∑' n : ℕ, eisenSquareSlice k A B n z := by
  rw [eisensteinSeriesRestrict]; simp_rw [eisenSquareSlice]
  have HI :=squares_cover_all
  let g := fun y : ℤ × ℤ => (eise k z) y
  have hgsumm : Summable g := by apply Eisenstein_tsum_summable k z h
  have index_lem := tsum_lemma g (fun (n : ℕ) => square n) HI hgsumm
  exact index_lem

lemma eisenslice_bounded (k : ℤ) (n : ℕ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B)
  (z : upperHalfSpaceSlice A B ): Complex.abs (eisenSquareSlice (k) A B n z) ≤
    8 / rfunct (lbpoint A B hb) ^ k * ((n : ℝ) ^ (↑k - 1))⁻¹ := by
  simp_rw [eisenSquareSlice]
  simp_rw [eisenSquare]
  simp_rw [eise]
  have SC := AbsEise_bounded_on_square k z h n
  simp_rw [AbsEise] at SC
  simp at SC
  simp
  have ineq1 :
    Complex.abs (∑ x : ℤ × ℤ in square n, ((↑x.fst * ↑↑z + ↑x.snd) ^ k)⁻¹) ≤
      ∑ x : ℤ × ℤ in square n, (Complex.abs ((↑x.fst * ↑↑z + ↑x.snd) ^ k))⁻¹ :=
    by
    simp
    have := complex_abs_sum_le (square n) fun x : ℤ × ℤ => (((x.1 : ℂ) * (z : ℂ) + (x.2 : ℂ)) ^ k)⁻¹
    simp at this
    exact this
  simp at *
  have SC2 := le_trans ineq1 SC
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  have rb := rfunctbound' k A B hb z n
  norm_cast at *
  apply le_trans SC2 rb


lemma Eisen_slice_bounded (k : ℤ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B)
  (z : upperHalfSpaceSlice A B ) :
   Complex.abs (eisensteinSeriesRestrict k A B z) ≤
    ∑' n : ℕ,  8 / rfunct (lbpoint A B hb) ^ k * ((n : ℝ) ^ (k - 1))⁻¹ := by
  have :=Eisenstein_series_is_sum_eisen_squares_slice k h A B  z
  rw [this]
  have hs := EisensteinSeries.summable_rfunct_twist k (lbpoint A B hb) h
  apply le_trans (abs_tsum' _)
  apply tsum_le_tsum
  intro n
  simpa using  (eisenslice_bounded k n h A B ha hb z)
  swap
  simpa using hs
  repeat {
  apply Summable.of_nonneg_of_le ?_
  intro b
  apply (eisenslice_bounded k b h A B ha hb z)
  simpa using hs
  intro b
  apply Complex.abs.nonneg}

lemma AbsEisen_slice_bounded (k : ℤ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
  (z : upperHalfSpaceSlice A B ) : ∑' (x : ℤ × ℤ), (AbsEise k z x) ≤
    ∑' (n : ℕ),  8 / rfunct (lbpoint A B hb) ^ k * (((n) : ℝ) ^ (k - 1))⁻¹ := by
  let In := fun (n : ℕ) => square n
  have HI := squares_cover_all
  let g := fun y : ℤ × ℤ => (AbsEise k z) y
  have gpos : ∀ y : ℤ × ℤ, 0 ≤ g y := by
    intro y
    simp_rw [AbsEise]
    simp
    apply zpow_nonneg
    apply Complex.abs.nonneg
  have index_lem := tsum_lemma g In HI
  simp at *
  rw [index_lem]
  apply tsum_le_tsum
  have smallerclaim := AbsEise_bounded_on_square k z h
  intro n
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  have rb := rfunctbound' k A B hb z n
  simp at *
  apply le_trans _ rb
  apply smallerclaim n
  apply Summable.of_nonneg_of_le ?_ ?_ (summable_rfunct_twist k z h)
  intro b
  apply Finset.sum_nonneg
  intro x _
  rw [AbsEise]
  apply Complex.abs.nonneg
  apply AbsEise_bounded_on_square k z h
  have := summable_rfunct_twist k (lbpoint A B hb) h
  simp at *
  exact this
  apply real_eise_is_summable k z h


/-
lemma lattice_tsum_upper_bound  (k : ℕ) (h : 3 ≤ k) (z : ℍ) :
  ∑' (n : ℕ),  8 / rfunct (z) ^ k * (((n) : ℝ) ^ (k - 1))⁻¹ =
    ∑' (n : ℕ), ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ := by

    sorry

lemma lattice_tsum_upper_bound' (k : ℕ) (h : 3 ≤ k) (z : ℍ) :
 ∑' (n : ℕ),  8 / rfunct (z) ^ k * (((n) : ℝ) ^ (k - 1))⁻¹ = ∑' (x : ℤ × ℤ),
  (1/(rfunct (z)^k))*((max x.1.natAbs x.2.natAbs : ℝ)^k)⁻¹ := by
  rw [lattice_tsum_upper_bound]

  rw [tsum_lemma _ (fun (n : ℕ) => square n)]
  congr
  ext1 n
  simp only [Real.rpow_nat_cast, one_div, Finset.sum_const, nsmul_eq_mul, ge_iff_le, Int.cast_le]
  have : ∑ v in square n, (1/(rfunct (z)^k))*((max v.1.natAbs v.2.natAbs: ℝ)^k)⁻¹ =
    ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ := by
     apply Finset.sum_congr
     rfl
     intro x hx
     simp at hx
     congr
     simp at *
     norm_cast at *
  simp at *
  rw [this]
  apply squares_cover_all
  rw [sum_lemma _ _ (fun (n : ℕ) => square n)]
  have : ∀ n : ℕ, ∑ v in square n, (1/(rfunct (z)^k))*((max v.1.natAbs v.2.natAbs: ℝ)^k)⁻¹ =
     ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ := by
     intro n
     apply Finset.sum_congr
     rfl
     intro x hx
     simp at hx
     congr
     simp at *
     norm_cast at *
  have hs : Summable (fun n : ℕ => ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ )  := by
    simp
    apply Summable.congr (summable_rfunct_twist k z h)
    intro b
    by_cases b0 : b = 0
    rw [b0]
    have hk : (0: ℝ)^((k : ℤ)-1) = 0:= by
      simp
      rw [Real.zero_rpow]
      have hk3 : (3 : ℝ) ≤ k := by norm_cast at *
      linarith

    simp at *
    rw [hk]
    simp
    right
    linarith
    have hb: 1 ≤ b := by
      exact Iff.mpr Nat.one_le_iff_ne_zero b0
    rw [square_size' b hb]
    field_simp
    ring_nf
    simp_rw [mul_assoc]
    have hbb : (b : ℝ)^(-1 + (k : ℝ)) = (b : ℝ)⁻¹ * b^(k : ℝ) := by
      rw [Real.rpow_add]
      congr
      exact Real.rpow_neg_one ↑b
      norm_cast
    rw [hbb]
    ring_nf
    simp
  apply Summable.congr hs
  intro b
  apply (this b).symm
  apply squares_cover_all
  intro y
  apply mul_nonneg
  simp
  apply pow_nonneg
  apply (rfunct_pos z).le
  simp only [ge_iff_le, Nat.cast_le, Real.rpow_nat_cast, inv_nonneg, le_max_iff, Nat.cast_nonneg,
    or_self, pow_nonneg]
  apply h
-/

lemma summable_upper_bound (k : ℤ) (h : 3 ≤ k) (z : ℍ) :
 Summable fun (x : ℤ × ℤ) =>
  (1/(rfunct (z)^k))*((max x.1.natAbs x.2.natAbs : ℝ)^k)⁻¹ := by
  rw [sum_lemma _ _ (fun (n : ℕ) => square n)]
  have : ∀ n : ℕ, ∑ v in square n, (1/(rfunct (z)^k))*((max v.1.natAbs v.2.natAbs: ℝ)^k)⁻¹ =
     ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ := by
     intro n
     apply Finset.sum_congr
     rfl
     intro x hx
     simp at hx
     congr
     norm_cast at *
  have hs : Summable (fun n : ℕ => ∑ v in square n, (1/(rfunct (z)^k))*((n : ℝ)^k)⁻¹ )  := by
    simp
    apply Summable.congr (summable_rfunct_twist k z h)
    intro b
    by_cases b0 : b = 0
    rw [b0]
    have hk : (0: ℝ)^((k : ℤ)-1) = 0:= by
      rw [zero_zpow]
      linarith
    simp at *
    rw [hk]
    simp
    right
    have hk0 : 0 ≤ k := by linarith
    lift k to ℕ using hk0
    simp  [zpow_coe_nat, ne_eq, zero_pow_eq_zero, gt_iff_lt]
    right
    linarith
    rw [square_size' b0]
    field_simp
    ring_nf
    simp_rw [mul_assoc]
    have hbb : (b : ℝ)^(-1 + (k : ℝ)) = (b : ℝ)⁻¹ * b^(k : ℝ) := by
      rw [Real.rpow_add]
      congr
      exact Real.rpow_neg_one ↑b
      simpa [pos_iff_ne_zero] using b0
    norm_cast at *
    rw [hbb]
    ring_nf
    simp
  apply Summable.congr hs
  intro b
  apply (this b).symm
  apply squares_cover_all
  intro y
  apply mul_nonneg
  simp
  apply zpow_nonneg
  apply (rfunct_pos z).le
  simp  [ge_iff_le, Nat.cast_le, Real.rpow_nat_cast, inv_nonneg, le_max_iff, Nat.cast_nonneg,
    or_self, zpow_nonneg]








def AbsEisenBound (A B : ℝ) (hb : 0 < B) (k : ℕ)  : ℝ :=
  ∑' (n : ℕ),  8 / rfunct (lbpoint A B hb) ^ k * (((n) : ℝ) ^ (k - 1))⁻¹


theorem Eisen_partial_tends_to_uniformly (k : ℤ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) :
    TendstoUniformly (eisenParSumSlice k A B) (eisensteinSeriesRestrict k A B) Filter.atTop :=
  by
  let M : ℕ → ℝ := fun x => 8 / rfunct (lbpoint A B hb) ^ k * ((x : ℝ) ^ ((k : ℤ) - 1))⁻¹
  have := M_test_uniform ?_ (eisenSquareSlice k A B) M
  simp_rw [← Eisenstein_series_is_sum_eisen_squares_slice k h A B  _] at this
  apply this
  simp_rw [eisenSquareSlice]
  simp_rw [eisenSquare]
  simp_rw [eise]
  intro n a
  have SC := AbsEise_bounded_on_square k a h n
  simp_rw [AbsEise] at SC
  simp at SC
  simp
  have ineq1 :
    Complex.abs (∑ x : ℤ × ℤ in square n, ((↑x.fst * ↑↑a + ↑x.snd) ^ k)⁻¹) ≤
      ∑ x : ℤ × ℤ in square n, (Complex.abs ((↑x.fst * ↑↑a + ↑x.snd) ^ k))⁻¹ :=
    by
    simp
    have := complex_abs_sum_le (square n) fun x : ℤ × ℤ => (((x.1 : ℂ) * (a : ℂ) + (x.2 : ℂ)) ^ k)⁻¹
    simp at this
    exact this
  simp at *
  have SC2 := le_trans ineq1 SC
  have hk0 : 0 ≤ k := by linarith
  lift k to ℕ using hk0
  have rb := rfunctbound' k A B hb a n
  norm_cast at rb
  norm_cast
  norm_cast at SC2
  apply le_trans SC2 rb
  have hk : 1 < (k - 1 : ℝ) := by
    have hy: 1 < (k -1  : ℤ) := by linarith
    norm_cast at *
  have nze : (8 / rfunct (lbpoint A B hb) ^ k : ℝ) ≠ 0 :=
    by
    apply div_ne_zero
    simp
    norm_cast
    apply zpow_ne_zero
    simp; by_contra HR
    have := rfunct_pos (lbpoint A B hb)
    rw [HR] at this
    simp at this
  have riesum := Real.summable_nat_rpow_inv.2 hk
  rw [← (summable_mul_left_iff nze).symm]

  --simp at riesum

  convert riesum
  norm_cast
  apply EisensteinSeries.nonemp A B ha hb



theorem Eisen_partial_tends_to_uniformly_on_ball (k : ℤ) (h : 3 ≤ k) (z : ℍ') :
    ∃ A B ε : ℝ,
      0 < ε ∧
        Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧
          0 < B ∧
            ε < B ∧
              TendstoUniformlyOn (eisenSquare' k) (Eisenstein_tsum k) Filter.atTop
                (Metric.closedBall z ε) :=
  by
  have h1 := closedBall_in_slice z
  obtain ⟨A, B, ε, hε, hB, hball, hA, hεB⟩ := h1
  use A
  use B
  use ε
  simp only [hε, hB, hball, hεB, true_and_iff]
  have hz : z ∈ upperHalfSpaceSlice A B := by apply hball; simp [hε.le]
  have hu := Eisen_partial_tends_to_uniformly k h A B hA hB
  have hu2 :
    TendstoUniformlyOn (eisenParSumSlice k A B) (eisensteinSeriesRestrict k A B) Filter.atTop
      (Metric.closedBall ⟨z, hz⟩ ε) :=
    by apply hu.tendstoUniformlyOn
  clear hu
  simp_rw [Metric.tendstoUniformlyOn_iff] at *
  simp_rw [eisenParSumSlice] at *
  simp_rw [eisenSquareSlice] at *
  simp_rw [eisenSquare']
  simp  [Filter.eventually_atTop, gt_iff_lt, ge_iff_le, instNonempty,
    Metric.mem_closedBall, Subtype.forall, SetCoe.forall, UpperHalfPlane.coe_im, Subtype.coe_mk,
      UpperHalfPlane.coe_re] at *
  intro δ hδ
  have hu3 := hu2 δ hδ
  clear hu2
  obtain ⟨a, ha⟩ := hu3
  use a
  intro b hb x hx hxx
  have ha2 := ha b hb x ?_
  apply ha2
  exact hxx
  apply hball
  simp only [hxx,hx, Metric.mem_closedBall]
  apply hx

theorem Eisen_partial_tends_to_uniformly_on_ball' (k : ℤ) (h : 3 ≤ k) (z : ℍ') :
    ∃ A B ε : ℝ,
      0 < ε ∧
        Metric.closedBall z ε ⊆ upperHalfSpaceSlice A B ∧
          0 < B ∧
            ε < B ∧
              TendstoUniformlyOn (fun n => extendByZero (eisenSquare' k n))
                (extendByZero (Eisenstein_tsum k)) Filter.atTop (Metric.closedBall z ε) :=
  by
  have H := Eisen_partial_tends_to_uniformly_on_ball k h z
  obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ := H
  refine ⟨A, B, ε, hε, hball, hB, hεB, ?_⟩
  simp_rw [Metric.tendstoUniformlyOn_iff] at *
  intro ε' hε'
  have h2 := hunif ε' hε'
  simp only [Filter.eventually_atTop, gt_iff_lt, ge_iff_le, Metric.mem_closedBall] at *
  obtain ⟨a, ha⟩ := h2
  use a
  have Hba := ball_in_upper_half z A B ε hε hεB hball
  intro b hb x hx
  have hxx : x ∈ ℍ'.1 := by apply Hba; simp [hx]
  have hf := extendByZero_eq_of_mem (Eisenstein_tsum k) _ hxx
  let F : ℕ → ℍ' → ℂ := fun n => eisenSquare' k n
  have hFb := extendByZero_eq_of_mem (F b) _ hxx
  simp  at *
  rw [hf]
  rw [hFb]
  apply ha b hb x hxx hx
