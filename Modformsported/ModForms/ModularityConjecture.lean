import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open Complex
open scoped UpperHalfPlane Real ModularForm

noncomputable section

def mapToUpper (x : ℝ) : ℍ :=
  ⟨x + I, by simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, zero_lt_one]⟩

def modularFormAn (n : ℕ) {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..1, exp (-2 * π * I * n * (x + I)) * f.1 (mapToUpper x)

local notation:73 "a_[" n:0 "]" f:72 => modularFormAn n f

def ratRed (q : ℚ) (p : ℕ) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

def setOfPointsModN (E : EllipticCurve ℚ) (n : ℕ) :=
  {P : ZMod n × ZMod n |
    let ⟨x, y⟩ := P
    y ^ 2 + ratRed E.a₁ n * x * y + ratRed E.a₃ n * y =
      x ^ 3 + ratRed E.a₂ n * x ^ 2 + ratRed E.a₄ n * x + ratRed E.a₆ n}

/-- The set of point `mod n` is finite.-/
instance apFintype (E : EllipticCurve ℚ) (p : ℕ+) : Fintype (setOfPointsModN E p) := by
  rw [setOfPointsModN]
  apply Subtype.fintype _

def EllipticCurve.ap (E : EllipticCurve ℚ) (p : ℕ) : ℕ :=
  p - Cardinal.toNat (Cardinal.mk (setOfPointsModN E p))

def IsNormalisedEigenform {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : Prop :=
  a_[1]f = 1 ∧
    ∀ (m n : ℕ), m.Coprime n →
      a_[n * m]f = a_[n]f * a_[m]f ∧
        ∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) ≠ 0 →
          a_[p ^ r]f = a_[p]f * a_[p ^ (r - 1)]f - p ^ (k - 1) * a_[p ^ (r - 2)]f ∧
            ∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) = 0 →
              a_[p ^ r]f = (a_[p]f) ^ r

def ModularityConjecture (E : EllipticCurve ℚ) :=
  ∃ (N : ℕ+) (f : CuspForm (Gamma0 N) 2), IsNormalisedEigenform f ∧
    ∀ (p : ℕ), p.Prime → (N : ZMod p) ≠ 0 → a_[p]f = E.ap p

theorem modularity_conjecture (E : EllipticCurve ℚ) : ModularityConjecture E := sorry
