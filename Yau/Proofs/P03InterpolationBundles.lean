import Yau.Proofs.P03AntiCanonicalNakano
import Yau.Proofs.P03TangentAntiCanonicalNakano

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

/-- The actual anticanonical coefficient bundle carries the fixed smooth
Nakano nonnegative metric induced by the original Kähler metric. -/
theorem antiCanonical_interpolation_bundle {n : ℕ} (X : KahlerManifold n) :
    Holomorphic (r := 1) (AntiCanonicalFiber X.manifold) ∧
      BundleDbar.SmoothMetric (r := 1) (AntiCanonicalFiber X.manifold)
        (antiCanonicalMetric X.metric.form) ∧
      NakanoNonnegative (r := 1) (AntiCanonicalFiber X.manifold)
        (antiCanonicalMetric X.metric.form) :=
  ⟨antiCanonical_holomorphic, antiCanonical_metric_smooth X.metric, antiCanonical_nakano X⟩

/-- The actual tangent-anticanonical tensor bundle carries the fixed smooth
Nakano nonnegative metric obtained from the computed tangent curvature. -/
theorem tangentAntiCanonical_interpolation_bundle {n : ℕ} (X : KahlerManifold n) :
    Holomorphic (r := n) (TangentAntiCanonicalFiber X.manifold) ∧
      BundleDbar.SmoothMetric (r := n) (TangentAntiCanonicalFiber X.manifold)
        (tangentAntiCanonicalMetric X.metric.form) ∧
      NakanoNonnegative (r := n) (TangentAntiCanonicalFiber X.manifold)
        (tangentAntiCanonicalMetric X.metric.form) :=
  ⟨tangentAntiCanonical_holomorphic, tangentAntiCanonical_metric_smooth X.metric,
    tangentAntiCanonical_nakano X⟩

end Yau.NodeProofs.P03Aux
