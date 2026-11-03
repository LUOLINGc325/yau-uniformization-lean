import Yau.Proofs.C03GeodesicBoundary

/-! The actual physical speed is exactly the source-chart metric quadratic
of the actual coordinate derivative. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem actualSpeedSq_source_chart (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ : ℝ → ComplexVector n) (t : ℝ) (hγ : ContDiffAt ℝ 1 γ t) :
    actualSpeedSq k γ t =
      realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t) := by
  letI := manifold_realSmooth (ComplexEuclideanManifold n hn)
  have hM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t := hγ.contMDiffAt
  have hsrc : γ t ∈ (chartAt (ComplexVector n) (0 : ComplexVector n)).source := by
    rw [euclidean_chartSource hn]
    trivial
  have H := actualSpeedSq_eq_chartEnergy k γ (0 : ComplexVector n) t hsrc hM
  simpa only [chartGeodesicEnergy, geoChartState, euclidean_chartPt] using H

end Yau.Proofs.C03Aux
