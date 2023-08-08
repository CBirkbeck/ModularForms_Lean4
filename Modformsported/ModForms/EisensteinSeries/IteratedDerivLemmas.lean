import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.Calculus.Series
import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Project.ForMathlib.ModForms2
import Project.ModForms.HolomorphicFunctions

#align_import mod_forms.Eisenstein_Series.iterated_deriv_lemmas

noncomputable section

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ'" => (⟨UpperHalfPlane.upperHalfSpace, upper_half_plane_isOpen⟩ : OpenSubs)

theorem iter_der_eqOn_cong (f g : ℂ → ℂ) (k : ℕ) (S : Set ℂ) (hs : IsOpen S) (hfg : EqOn f g S) :
    EqOn (iteratedDerivWithin k f S) (iteratedDerivWithin k g S) S :=
  by
  induction' k with k IH generalising f g
  simp only [iteratedDerivWithin_zero]
  apply hfg
  intro x hx
  rw [iteratedDerivWithin_succ]
  rw [iteratedDerivWithin_succ]
  apply derivWithin_congr
  apply IH
  apply IH hx
  all_goals apply IsOpen.uniqueDiffWithinAt hs hx

theorem iter_deriv_within_add (k : ℕ) (x : ℍ') (f g : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ')
    (hg : ContDiffOn ℂ k g ℍ') :
    iteratedDerivWithin k (f + g) ℍ' x =
      iteratedDerivWithin k f ℍ' x + iteratedDerivWithin k g ℍ' x :=
  by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_add_apply]
  simp
  apply hf
  apply hg
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply x.2

theorem iter_der_within_const_neg (k : ℕ) (hk : 0 < k) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) :
    iteratedDerivWithin k (fun z : ℂ => c - f z) ℍ' x =
      iteratedDerivWithin k (fun z => -f z) ℍ' x :=
  by
  simp
  induction' k with k IH
  exfalso
  simpa using hk
  rw [iteratedDerivWithin_succ']
  rw [iteratedDerivWithin_succ']
  apply iter_der_eqOn_cong
  apply upper_half_plane_isOpen
  intro y hy
  rw [derivWithin.neg]
  apply derivWithin_const_sub
  repeat' apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen hy
  apply x.2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply x.2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply x.2

theorem iter_der_within_const_mul (k : ℕ) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (c • f) ℍ' x = c • iteratedDerivWithin k f ℍ' x :=
  by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply]
  simp only [ContinuousMultilinearMap.smul_apply] at *
  apply hf
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply x.2

theorem iter_der_within_const_mul' (k : ℕ) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (fun z => c * f z) ℍ' x = c * iteratedDerivWithin k f ℍ' x := by
  simpa using iter_der_within_const_mul k x c f hf

theorem iter_der_within_neg (k : ℕ) (x : ℍ') (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (-f) ℍ' x = -iteratedDerivWithin k f ℍ' x :=
  by
  rw [neg_eq_neg_one_mul]
  nth_rw 2 [neg_eq_neg_one_mul]
  rw [← smul_eq_mul]
  rw [← smul_eq_mul]
  apply iter_der_within_const_mul k x (-1)
  apply hf

theorem iter_der_within_neg' (k : ℕ) (x : ℍ') (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (fun z => -f z) ℍ' x = -iteratedDerivWithin k f ℍ' x := by
  convert iter_der_within_neg k x f hf

theorem iter_deriv_within_sub (k : ℕ) (x : ℍ') (f g : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ')
    (hg : ContDiffOn ℂ k g ℍ') :
    iteratedDerivWithin k (f - g) ℍ' x =
      iteratedDerivWithin k f ℍ' x - iteratedDerivWithin k g ℍ' x :=
  by
  have h1 : f - g = f + -g := by rfl
  rw [h1]
  rw [iter_deriv_within_add k x]
  rw [iter_der_within_neg k x g hg]
  rfl
  apply hf
  apply ContDiffOn.neg hg

