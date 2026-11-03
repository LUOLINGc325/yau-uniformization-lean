import Yau.Proofs.P02BisectionalBound
import Yau.Proofs.G01BisectionalNormalization

/-! The genuine compact real bisectional lower bound has the exact Chern
normalization, including both factors two in the real metric. -/

noncomputable section
open Set
open scoped Topology Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
open Yau.NodeProofs.P02Aux Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem compact_chern_bisectional_lower_bound (X : KahlerManifold n)
    (K : Set X.manifold.Carrier) (hK : IsCompact K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y ∈ K, ∀ u v : TangentVector X.manifold y,
      κ * hermitianNormSq (X.metric.form y) u * hermitianNormSq (X.metric.form y) v ≤
        bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v) := by
  obtain ⟨κ, hκ, hbound⟩ := compact_bisectional_lower_bound X.metric
    X.positive_bisectional_curvature K hK
  refine ⟨κ, hκ, ?_⟩
  intro y hy u v
  have H := hbound y hy ((realTangentEquiv y).symm u) ((realTangentEquiv y).symm v)
  simp only [underlyingRealRiemannianMetric_inner, transportBisectional,
    ContinuousLinearEquiv.apply_symm_apply] at H
  rw [paper_numerator_eq_bisectionalForm X.metric.form
    (metricSmooth_of_smoothMetric X.metric) X.kahler_metric] at H
  change κ * (2 * hermitianNormSq (X.metric.form y) u) *
    (2 * hermitianNormSq (X.metric.form y) v) ≤
      4 * bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v) at H
  linarith

end Yau.Proofs.C03Aux
