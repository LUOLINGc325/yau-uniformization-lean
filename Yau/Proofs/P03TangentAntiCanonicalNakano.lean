import Yau.Proofs.P03TangentGriffiths
import Yau.Proofs.P03TensorNakanoAlgebra

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ}

theorem tangentAntiCanonical_nakano (X : KahlerManifold n) :
    NakanoNonnegative (r := n) (TangentAntiCanonicalFiber X.manifold)
      (tangentAntiCanonicalMetric X.metric.form) := by
  intro a z hz U
  rw [tangentAntiCanonical_localDomain] at hz
  exact tangentAntiCanonical_nakano_nonnegative_at X.metric a hz
    (tangent_griffiths_nonnegative X a hz) U

end Yau.NodeProofs.P03Aux
