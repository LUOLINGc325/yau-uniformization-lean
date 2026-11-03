import Yau.Proofs.V01EmbeddingCoordinates

/-! V01 scratch source: the explicit block derivative of the finite
cotangent map. Derivative-identification lemmas will retain the chart target. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n N m : ℕ} {M : ComplexManifold n}

def embeddingChartDerivative
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) (p : CotangentCoord n) :
    CotangentCoord n →L[ℂ] ComplexVector (N + m) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + m) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.addCases
      (fun i => (EuclideanSpace.proj i).comp
        ((fderiv ℂ (inChart x F) p.1).comp
          (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n))))
      (fun j => ∑ b,
        (p.2 b • ((EuclideanSpace.proj b).comp
          ((fderiv ℂ (fieldCoords (V j) x) p.1).comp
            (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)))) +
        (fieldCoords (V j) x p.1) b • ((EuclideanSpace.proj b).comp
          (ContinuousLinearMap.snd ℂ (ComplexVector n) (ComplexVector n)))))))

theorem embeddingChartDerivative_base
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) (p v : CotangentCoord n) (i : Fin N) :
    embeddingChartDerivative F V x p v (Fin.castAdd m i) =
      (fderiv ℂ (inChart x F) p.1 v.1) i := by
  simp [embeddingChartDerivative, ContinuousLinearMap.comp_apply]

theorem embeddingChartDerivative_fiber
    (F : M.Carrier → ComplexVector N) (V : Fin m → VectorField M)
    (x : M.Carrier) (p v : CotangentCoord n) (j : Fin m) :
    embeddingChartDerivative F V x p v (Fin.natAdd N j) =
      ∑ b, (p.2 b * (fderiv ℂ (fieldCoords (V j) x) p.1 v.1) b +
        (fieldCoords (V j) x p.1) b * v.2 b) := by
  simp [embeddingChartDerivative, ContinuousLinearMap.comp_apply, smul_eq_mul]

end Yau.Blueprint.V01Proof
