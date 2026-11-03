import Yau.Blueprint.Analytic

/-! Backward approximation in the stated inverse tubes; uniformization.tex:51-169.
The maps, the errors and the balls all use the same polynomial sequence. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
noncomputable section
namespace Yau.Blueprint
open Yau

/-- Uniform shadowing on an open parameter domain. It applies to the two raw
chart-coordinate families in uniformization.tex:51-68 by restricting to their
stated relatively compact parameter neighborhoods. -/
def BackwardShadowing (n m : ℕ) : Prop :=
  ∀ (Ω : Set (ComplexVector m)) (s : ℕ → ℝ) (G Ginv : ℕ → PolyMap n)
    (zeta : ℕ → ComplexVector m → ComplexVector n) (nu delta : ℝ),
    IsOpen Ω → 0 < nu → nu < 1 / 10 → 0 < delta → delta < 1 / 10 →
    Tendsto s atTop atTop →
    (∀ k, 1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k) →
    (∀ k, IsPolyAutomorphism (G k) (Ginv k)) →
    (∀ k, DifferentiableOn ℂ (zeta k) Ω) →
    (∀ᶠ k in atTop, ∀ z ∈ Ω,
      ‖zeta k z‖ ≤ Real.exp (-2 * nu * s k) ∧
      ‖zeta (k + 1) z - (G k).eval (zeta k z)‖ ≤ Real.exp (-10 * s k)) →
    (∀ᶠ k in atTop, ∀ u v : ComplexVector n,
      ‖u‖ < Real.exp (-nu * s (k + 1)) → ‖v‖ < Real.exp (-nu * s (k + 1)) →
      ‖(Ginv k).eval u - (Ginv k).eval v‖ ≤ Real.exp (s (k + 1) - s k) * ‖u - v‖) →
    ∃ xi : ℕ → ComplexVector m → ComplexVector n,
      (∀ᶠ k in atTop, DifferentiableOn ℂ (xi k) Ω ∧
        (∀ K ⊆ Ω, IsCompact K →
          TendstoUniformlyOn
            (fun l z => (backwardSegment Ginv k (l - k)).eval (zeta l z)) (xi k) atTop K) ∧
        (∀ z ∈ Ω, ‖xi k z - zeta k z‖ ≤ Real.exp (-6 * s k) ∧
          xi (k + 1) z = (G k).eval (xi k z))) ∧
      (∀ᶠ k in atTop, ∀ l, k ≤ l → ∀ i, k ≤ i → i < l → ∀ z ∈ Ω,
        ‖(backwardSegment Ginv (i + 1) (l - (i + 1))).eval (zeta l z)‖ <
          Real.exp (-nu * s (i + 1)) ∧
        ‖(G i).eval (zeta i z)‖ < Real.exp (-nu * s (i + 1)))

end Yau.Blueprint
