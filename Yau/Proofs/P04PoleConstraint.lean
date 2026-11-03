import Yau.Proofs.P04DbarSlice

noncomputable section
open Set MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
variable (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)

/-- A fixed-source distributional slice intersected with an actual bounded
operator norm ball in the common weighted Hilbert space. -/
def canonicalPoleConstraint
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (T : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ →L[ℂ]
      L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (R : ℝ) :=
  canonicalDbarSlice g μ hμ Φ hΦ f ∩ T ⁻¹' Metric.closedBall 0 R

theorem canonicalPoleConstraint_isClosed
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (T : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ →L[ℂ]
      L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (R : ℝ) : IsClosed (canonicalPoleConstraint g μ hμ Φ hΦ f T R) :=
  (canonicalDbarSlice_isClosed g μ hμ Φ hΦ f).inter (Metric.isClosed_closedBall.preimage T.continuous)

theorem canonicalPoleConstraint_convex
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (T : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ →L[ℂ]
      L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (R : ℝ) : Convex ℝ (canonicalPoleConstraint g μ hμ Φ hΦ f T R) :=
  (canonicalDbarSlice_convex g μ hμ Φ hΦ f).inter
    ((convex_closedBall (0 : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ
      flatMetric flatMetric_smooth Φ hΦ) R).linear_preimage (T.restrictScalars ℝ).toLinearMap)

end Yau.Proofs.P04Aux
