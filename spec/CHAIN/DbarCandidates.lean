import Yau.Geometry.HolomorphicBundle

/-!
Internally scheduled L07/L14 targets. These definitions are propositions to be
proved; importing this file supplies no theorem or axiom. Smooth weights only:
the singular logarithmic regularization and interpolation stay in P03.
-/
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle
noncomputable section

namespace Yau.LeafCandidates
open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The induced local tensor-determinant pairings descend on overlaps.
This is a concrete gluing obligation, not a freely supplied tensor metric. -/
def TensorDetMetricDescent : Prop :=
  ∀ (h : Metric E) (a b x : M.Carrier),
    x ∈ (chartAt (ComplexVector n) a).source →
    x ∈ (chartAt (ComplexVector n) b).source →
    x ∈ (localTriv (r := r) E a).baseSet →
    x ∈ (localTriv (r := r) E b).baseSet →
    ∀ u v : TensorDetFiber (r := r) E x,
      tensorDetLocalPairing (r := r) E h a x u v =
        tensorDetLocalPairing (r := r) E h b x u v

/-- Internal differential-calculus bridge for the actual determinant tensor
metric; source identity: Demailly 1982, Lemma 2.5, p.467.
This identity is not assumed in `DemaillySkoda`. -/
def TensorDetCurvatureIdentity : Prop :=
  ∀ (h : Metric E), Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E h →
    ∀ a z, z ∈ localDomain (r := r) E a → ∀ i j,
      curvatureMatrix (tensorDetMetricMatrix (r := r) E h a) z i j =
        (BundleDbar.metricMatrix (r := r) E h a z).det •
          (curvature (r := r) E h a z i j +
            Matrix.trace ((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ *
              curvature (r := r) E h a z i j) • BundleDbar.metricMatrix (r := r) E h a z)

/-- Nonnegative part of Demailly 1982, Theorem 2.6(2.1), p.467, expressed
through the Chern curvature computed from the induced determinant tensor
metric. This is a theorem target, with no assumption of Nakano positivity of E. -/
def DemaillySkoda : Prop :=
  ∀ (h : Metric E), Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E h →
    GriffithsNonnegative (r := r) E h → TensorDetNakanoNonnegative (r := r) E h

/-- Smooth-weight `(n,1)` complete Kähler estimate. The source only needs
local L² plus finite inverse-curvature integral; global unweighted L² of the
source is deliberately absent, as in Demailly Theorem 5.1.

`inverseCurvatureIntegral` is the extended variational inverse of the actual
curvature quadratic form, so the statement also makes sense for semipositive
curvature. No arbitrary operator or positivity certificate is supplied.

The metric g has a complete induced length metric and closed Kähler form in
its concrete type, and μ is required to satisfy the actual chart volume law. -/
def WeightedDbarEstimate : Prop :=
  ∀ (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ),
    IsRiemannianVolume g.form μ → Holomorphic (r := r) E →
    BundleDbar.SmoothMetric (r := r) E h → SmoothFn φ →
    WeightedNakanoNonnegative (r := r) E h φ →
    ∀ f : NQForm E 1, WeaklyClosed (r := r) E f →
      inverseCurvatureIntegral (r := r) E g.form h μ φ f < ⊤ →
      ∃ u : NQForm E 0,
        WeightedL2 (r := r) E g.form h μ φ u ∧ WeakDbar (r := r) E u f ∧
          weightedNormSq (r := r) E g.form h μ φ u ≤
            inverseCurvatureIntegral (r := r) E g.form h μ φ f

/-- Metric independence in the exact `q=1` estimate: both the unknown top-form
integral and the inverse-curvature source integral agree for any two smooth Hermitian
metrics, including the original incomplete metric on a coordinate ball. This is the local conformal cancellation consumed on Δ*, and
the more general Remark 4.5 bridge. It is not asserted for a coarse scalar
lower-eigenvalue bound (Remark 4.2), which the source explicitly excludes. -/
def TopDegreeMetricIndependence : Prop :=
  ∀ (g₁ g₂ : HermitianField M) (μ₁ μ₂ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ),
    IsRiemannianVolume g₁ μ₁ → IsRiemannianVolume g₂ μ₂ →
    MetricSmooth g₁ → MetricSmooth g₂ →
    Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E h → SmoothFn φ →
    WeightedNakanoNonnegative (r := r) E h φ →
    (∀ u : NQForm E 0, LocallyL2 (r := r) E u →
      weightedNormSq (r := r) E g₁ h μ₁ φ u =
        weightedNormSq (r := r) E g₂ h μ₂ φ u) ∧
    (∀ f : NQForm E 1, LocallyL2 (r := r) E f →
      inverseCurvatureIntegral (r := r) E g₁ h μ₁ φ f =
        inverseCurvatureIntegral (r := r) E g₂ h μ₂ φ f)

end Yau.LeafCandidates
