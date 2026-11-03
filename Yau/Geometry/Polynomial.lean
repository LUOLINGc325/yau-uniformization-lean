import Yau.Geometry.Basic

/-!
# Polynomial maps of `ℂⁿ`, polynomial automorphisms and jets

Polynomial maps are `n`-tuples of `MvPolynomial`s; composition is `bind₁`.  A polynomial
automorphism is a pair of polynomial maps that are mutually inverse *as polynomials*.
Jets of holomorphic germs at `0` are compared through `iteratedFDeriv ℂ`.
(`dynamics.tex:1-153`, `uniformization.tex:324-338`.)
-/

open scoped Topology

noncomputable section

namespace Yau

variable {n : ℕ}

abbrev PolyMap (n : ℕ) := Fin n → MvPolynomial (Fin n) ℂ

namespace PolyMap

def eval (P : PolyMap n) (z : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => z j) (P i))

/-- `P.comp Q = P ∘ Q`. -/
def comp (P Q : PolyMap n) : PolyMap n := fun i => MvPolynomial.bind₁ Q (P i)

def id : PolyMap n := fun i => MvPolynomial.X i

/-- Degree `max_i deg P_i`. -/
def degree (P : PolyMap n) : ℕ := Finset.univ.sup fun i => (P i).totalDegree

/-- `ℓ¹` norm of all coefficients. -/
def coeffNorm (P : PolyMap n) : ℝ := ∑ i, ∑ m ∈ (P i).support, ‖(P i).coeff m‖

/-- Linear part `P'(0)` as a matrix (`i` = component, `j` = variable). -/
def linearPart (P : PolyMap n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (P i).coeff (Finsupp.single j 1)

def FixesZero (P : PolyMap n) : Prop := ∀ i, (P i).coeff 0 = 0

/-- Jacobian determinant as a polynomial. -/
def jacDet (P : PolyMap n) : MvPolynomial (Fin n) ℂ :=
  Matrix.det (fun i j => MvPolynomial.pderiv j (P i))

/-- `J_d P = J_d Q`: equal coefficients in all degrees `≤ d`. -/
def JetEq (P Q : PolyMap n) (d : ℕ) : Prop :=
  ∀ i (m : Fin n →₀ ℕ), (m.sum fun _ e => e) ≤ d → (P i).coeff m = (Q i).coeff m

end PolyMap

/-- `(P, Q)` is a polynomial automorphism of `ℂⁿ` with inverse `Q`. -/
def IsPolyAutomorphism (P Q : PolyMap n) : Prop :=
  P.comp Q = PolyMap.id ∧ Q.comp P = PolyMap.id

/-- An invertible constant-volume `d`-jet fixing `0` (`dynamics.tex:141-145`): degree `≤ d`,
invertible linear part, and Jacobian determinant constant through degree `d - 1`. -/
def IsConstantVolumeJet (J : PolyMap n) (d : ℕ) : Prop :=
  J.FixesZero ∧ J.degree ≤ d ∧ (J.linearPart).det ≠ 0 ∧
    ∀ m : Fin n →₀ ℕ, 1 ≤ (m.sum fun _ e => e) → (m.sum fun _ e => e) ≤ d - 1 →
      (J.jacDet).coeff m = 0

/-- Forward compositions `G_{0,k} = G_{k-1} ∘ ⋯ ∘ G_0`. -/
def forwardComp (G : ℕ → PolyMap n) : ℕ → PolyMap n
  | 0 => PolyMap.id
  | k + 1 => (G k).comp (forwardComp G k)

/-- Inverses `G_{0,k}^{-1} = G_0^{-1} ∘ ⋯ ∘ G_{k-1}^{-1}`. -/
def backwardComp (Ginv : ℕ → PolyMap n) : ℕ → PolyMap n
  | 0 => PolyMap.id
  | k + 1 => (backwardComp Ginv k).comp (Ginv k)

/-- Inverse composition from step `k` across `m` successive steps. -/
def backwardSegment (Ginv : ℕ → PolyMap n) (k : ℕ) : ℕ → PolyMap n
  | 0 => PolyMap.id
  | m + 1 => (backwardSegment Ginv k m).comp (Ginv (k + m))

/-- Agreement of holomorphic germs at `0` through order `d`. -/
def GermJetEq (F G : ComplexVector n → ComplexVector n) (d : ℕ) : Prop :=
  ∀ k ≤ d, iteratedFDeriv ℂ k F 0 = iteratedFDeriv ℂ k G 0

/-- Coefficient norm `|J_d F|` of the `d`-jet at `0`. -/
def jetNorm (F : ComplexVector n → ComplexVector n) (d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), ‖iteratedFDeriv ℂ k F 0‖

/-- Operator norm of `fderiv ℂ F 0` and of its inverse, for linear-algebra estimates. -/
def centerDeriv (F : ComplexVector n → ComplexVector n) : ComplexVector n →L[ℂ] ComplexVector n :=
  fderiv ℂ F 0

end Yau
