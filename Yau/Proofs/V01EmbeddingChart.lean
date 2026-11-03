import Yau.Proofs.V01EmbeddingCoordinates
import Yau.Proofs.V03Charts

/-! V01 scratch source: fiber evaluation in every actual fixed chart.
The target/source hypotheses are never discarded. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n N m : ℕ} {M : ComplexManifold n}

theorem covectorOfCoords_apply_tangent
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (η : ComplexVector n) (v : TangentVector M y) :
    covectorOfCoords x y η v = ∑ b, (tangentCoords x y v) b * η b := by
  calc
    _ = covectorOfCoords x y η (chartVec x y (tangentCoords x y v)) :=
      congrArg (covectorOfCoords x y η)
        (Yau.Blueprint.V03Proof.chartVec_tangentCoords x y hy v).symm
    _ = ∑ b, (tangentCoords x y v) b *
        (covectorCoords x y (covectorOfCoords x y η)) b :=
      Yau.Blueprint.V03Proof.covector_apply_chartVec x y _ _
    _ = _ := by rw [Yau.Blueprint.V03Proof.covectorCoords_ofCoords x y hy]

theorem cotangentEmbedding_chart_base
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) (z η : ComplexVector n) (i : Fin N) :
    cotangentEmbedding F V (cotangentChartInv x (z, η)) (Fin.castAdd m i) =
      F (chartInv x z) i := by
  rw [cotangentEmbedding_base]
  rfl

theorem cotangentEmbedding_chart_fiber
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (η : ComplexVector n) (j : Fin m) :
    cotangentEmbedding F V (cotangentChartInv x (z, η)) (Fin.natAdd N j) =
      ∑ b, (fieldCoords (V j) x z) b * η b := by
  rw [cotangentEmbedding_fiber]
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  exact covectorOfCoords_apply_tangent x (chartInv x z) hy η (V j (chartInv x z))


theorem cotangentEmbedding_in_chart
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) {p : CotangentCoord n} (hp : p ∈ cotangentTarget x) :
    cotangentEmbedding F V (cotangentChartInv x p) = cotangentEmbeddingChart F V x p := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [cotangentEmbeddingChart] using cotangentEmbedding_chart_base F V x p.1 p.2 j
  · simpa [cotangentEmbeddingChart] using cotangentEmbedding_chart_fiber F V x hp.1 p.2 j

end Yau.Blueprint.V01Proof
