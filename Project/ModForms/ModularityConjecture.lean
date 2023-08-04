import Project.ForMathlib.ModForms2
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Project.ForMathlib.UnformLimitsOfHolomorphic

#align_import mod_forms.modularity_conjecture

open ModularForm Complex

open scoped Interval Real ModularForm

local notation "ℍ" => UpperHalfPlane

noncomputable section

def mapToUpper (x : ℝ) : ℍ :=
  ⟨x + I, by simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, zero_lt_one]⟩

def modularFormAn (n : ℕ) {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : ℂ :=
  ∫ x : ℝ in 0 ..1, exp (-2 * π * I * n * (x + I)) * f.1 (mapToUpper x)

local notation:73 "a_[" n:0 "]" f:72 => modularFormAn n f

def ratRed (q : ℚ) (p : ℕ) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

def setOfPointsModN (E : EllipticCurve ℚ) (n : ℕ) :=
  {P : ZMod n × ZMod n |
    let ⟨x, y⟩ := P
    y ^ 2 + ratRed E.a₁ n * x * y + ratRed E.a₃ n * y =
      x ^ 3 + ratRed E.a₂ n * x ^ 2 + ratRed E.a₄ n * x + ratRed E.a₆ n}

/-- The set of point `mod n` is finite.-/
instance apFintype (E : EllipticCurve ℚ) (p : ℕ+) : Fintype (setOfPointsModN E p) :=
  by
  rw [setOfPointsModN]
  apply Subtype.fintype _
  exact
    Classical.decPred fun x : ZMod ↑p × ZMod ↑p =>
      x ∈ {P : ZMod ↑p × ZMod ↑p | SetOfPointsModN._Match1 E (↑p) P}
  apply Prod.fintype _ _
  repeat' apply ZMod.fintype

def EllipticCurve.ap (E : EllipticCurve ℚ) (p : ℕ) : ℕ :=
  p - (Cardinal.mk (setOfPointsModN E p)).toNat

def IsNormalisedEigenform {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : Prop :=
  a_[1]f = 1 ∧
    ∀ (m n : ℕ) (hmn : m.coprime n),
      a_[n * m]f = a_[n]f * a_[m]f ∧
        ∀ (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (HpN : (N : ZMod p) ≠ 0),
          a_[p ^ r]f = a_[p]f * a_[p ^ (r - 1)]f - p ^ (k - 1) * a_[p ^ (r - 2)]f ∧
            ∀ (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (HpN : (N : ZMod p) = 0),
              a_[p ^ r]f = (a_[p]f) ^ r

theorem modularity_conjecture (E : EllipticCurve ℚ) :
    ∃ (N : ℕ) (f : CuspForm (Gamma0 N) 2) (hf : IsNormalisedEigenform f),
      ∀ (p : ℕ) (hp : p.Prime) (hN : (N : ZMod p) ≠ 0), a_[p]f = E.ap p :=
  by sorry

