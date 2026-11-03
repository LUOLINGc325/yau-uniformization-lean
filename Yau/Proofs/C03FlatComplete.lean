import Yau.Proofs.C03FlatCompleteDistance
import Yau.Proofs.C03FlatCompleteVolume

/-! A genuine complete Euclidean Kähler background with its exact volume measure. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ENNReal
open MeasureTheory Filter
namespace Yau.Proofs.C03Aux.FlatComplete
open Yau Yau.LeafProofs

/-- The complete flat background; no completeness or volume oracle is an input. -/
def euclideanCompleteMetric (n : ℕ) (hn : 1 ≤ n) :
    SmoothMetric (ComplexEuclideanManifold n hn) :=
  C04ChartsAux.smoothMetric_of_complete_field (euclideanHermitianField n hn)
    (euclidean_metricSmooth n hn) (euclidean_kahlerClosed n hn)
    (euclidean_complete_distance n hn)

@[simp] theorem euclideanCompleteMetric_form (n : ℕ) (hn : 1 ≤ n) :
    (euclideanCompleteMetric n hn).form = euclideanHermitianField n hn := rfl

theorem euclideanCompleteMetric_distance (n : ℕ) (hn : 1 ≤ n)
    (x y : ComplexVector n) :
    lengthDist (euclideanCompleteMetric n hn).form x y = dist x y :=
  euclidean_lengthDist n hn x y

theorem euclideanCompleteMetric_volume (n : ℕ) (hn : 1 ≤ n) :
    IsRiemannianVolume (euclideanCompleteMetric n hn).form
      (euclideanVolume n hn) :=
  euclidean_isRiemannianVolume n hn

end Yau.Proofs.C03Aux.FlatComplete
