import Yau.Proofs.F01ACanonicalShift

/-! The smooth comparison passes to a fixed canonical section. The input
comparison concerns the same U/P for every weight and every time horizon. -/
noncomputable section
open Filter
open scoped Topology

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- This intermediate property is proved from the actual common approximating
family by the global-core construction. It is not an assumption of F01. -/
def SmoothRicciWeightComparison (X : KahlerManifold n) (u : Pt X → ℝ)
    (U P : STF X) (η : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
  ∀ ψ : Pt X → ℝ, SmoothFn ψ →
    (∀ x, HermLE (ricci X.metric.form x) (levi ψ x)) →
  ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
  ∀ A : ℝ, (∀ x, ψ x - ε * u x ^ 2 - A ≤ 0) →
  ∀ x t, t ∈ Set.Icc 0 (D / 2) →
    0 ≤ (D - t) * P x t + U x t - D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t

/-- A section and its coefficient precede all horizon, epsilon and time choices.
At its zeros the smooth regularization was used; the finite logarithmic bound
is asserted only where this same section is nonzero. -/
def CanonicalRhoPointBound (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (P : STF X) (η : ℝ) : Prop :=
  ∀ S : CanonicalSection X.manifold, IsHolomorphicCanonical S →
    (∃ c : ℝ, ∀ y, Real.log (canonicalNormSq X.metric.form S y) ≤
      c * (1 + distFrom X.metric.form o y)) →
  ∃ a : ℝ, 0 < a ∧
    ∀ D : ℝ, 0 < D → ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
    ∀ x t, t ∈ Set.Icc 0 (D / 2) → 0 < canonicalNormSq X.metric.form S x →
      -P x t ≤ 2 * (|Real.log (canonicalNormSq X.metric.form S x)| +
        ε * u x ^ 2 + a * (1 + ε⁻¹) + (n : ℝ))

/-- The scalar consequence uses U≤0 and the same singular comparison. -/
theorem rho_bound_of_canonical_comparison {D t p v w ε ux A N : ℝ}
    (hD : 0 < D) (ht : t ∈ Set.Icc 0 (D / 2)) (hN : 0 ≤ N) (hv : v ≤ 0)
    (hφ : w - ε * ux ^ 2 - A ≤ 0)
    (hQ : 0 ≤ (D - t) * p + v - D * (w - ε * ux ^ 2 - A) + N * t) :
    -p ≤ 2 * (-w + ε * ux ^ 2 + A + N) := by
  have hden : 0 < D - t := by linarith [ht.2]
  have hB : 0 ≤ -w + ε * ux ^ 2 + A := by linarith
  have hnum : (D - t) * (-p) ≤ D * (-w + ε * ux ^ 2 + A) + N * t := by
    nlinarith
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith [mul_nonneg (show 0 ≤ D - 2 * t by linarith [ht.2]) hB,
    mul_nonneg (show 0 ≤ D - 2 * t by linarith [ht.2]) hN,
    mul_nonneg hden.le hN]

end Yau.NodeProofs.F01Aux
