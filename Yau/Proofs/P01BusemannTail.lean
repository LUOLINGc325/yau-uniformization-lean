import Yau.Proofs.P01BusemannLimit
import spec.CHAIN.CONTRACTS
import Yau.LeafProofs.L12

noncomputable section
open Filter
open scoped Topology NNReal

namespace Yau.NodeProofs.P01Aux
open Yau Yau.Blueprint

/-- The analytic tail of P01. Ray existence is constructed separately before
this conditional helper can be used to close the original node. -/
theorem busemannConclusion_of_isometric_ray {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (ray : ℝ≥0 → Pt X) (hzero : ray 0 = o)
    (hray : ∀ s t,
      distFrom X.metric.form (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) :
    BusemannConclusion X o := by
  refine ⟨ray, hzero, hray, ?_⟩
  letI := Yau.LeafProofs.L12Aux.inducedMetricSpace X.metric
  exact exists_busemann_limit o ray hzero hray

end Yau.NodeProofs.P01Aux
