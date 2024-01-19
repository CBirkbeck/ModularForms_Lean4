import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Series
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Modformsported.ForMathlib.ModForms2
import Modformsported.ModForms.HolomorphicFunctions


noncomputable section

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval NNReal ENNReal Topology BigOperators Nat Classical

local notation "ℍ'" =>
  (TopologicalSpace.Opens.mk UpperHalfPlane.upperHalfSpace upper_half_plane_isOpen)

theorem iter_der_eqOn_cong (f g : ℂ → ℂ) (k : ℕ) (S : Set ℂ) (hs : IsOpen S) (hfg : EqOn f g S) :
    EqOn (iteratedDerivWithin k f S) (iteratedDerivWithin k g S) S :=
  iteratedDerivWithin_congr hs.uniqueDiffOn hfg

theorem iter_deriv_within_add (k : ℕ) (x : ℍ') (f g : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ')
    (hg : ContDiffOn ℂ k g ℍ') :
    iteratedDerivWithin k (f + g) ℍ' x =
      iteratedDerivWithin k f ℍ' x + iteratedDerivWithin k g ℍ' x :=
  iteratedDerivWithin_add x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn hf hg

theorem iter_der_within_const_neg (k : ℕ) (hk : 0 < k) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) :
    iteratedDerivWithin k (fun z : ℂ => c - f z) ℍ' x =
      iteratedDerivWithin k (fun z => -f z) ℍ' x :=
  iteratedDerivWithin_const_neg x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn hk c

theorem iter_der_within_const_mul (k : ℕ) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (c • f) ℍ' x = c • iteratedDerivWithin k f ℍ' x :=
  iteratedDerivWithin_const_smul x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn c hf

theorem iter_der_within_const_mul' (k : ℕ) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (fun z => c * f z) ℍ' x = c * iteratedDerivWithin k f ℍ' x :=
  iteratedDerivWithin_const_mul x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn c hf

theorem iter_der_within_neg (k : ℕ) (x : ℍ') (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (-f) ℍ' x = -iteratedDerivWithin k f ℍ' x :=
  iteratedDerivWithin_neg x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn hf

theorem iter_der_within_neg' (k : ℕ) (x : ℍ') (f : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ') :
    iteratedDerivWithin k (fun z => -f z) ℍ' x = -iteratedDerivWithin k f ℍ' x :=
  iteratedDerivWithin_neg' x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn hf

theorem iter_deriv_within_sub (k : ℕ) (x : ℍ') (f g : ℂ → ℂ) (hf : ContDiffOn ℂ k f ℍ')
    (hg : ContDiffOn ℂ k g ℍ') :
    iteratedDerivWithin k (f - g) ℍ' x =
      iteratedDerivWithin k f ℍ' x - iteratedDerivWithin k g ℍ' x :=
  iteratedDerivWithin_sub x.2 UpperHalfPlane.upperHalfSpace.uniqueDiffOn hf hg
