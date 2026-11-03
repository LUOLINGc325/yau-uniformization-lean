import Yau.LeafProofs.L17ChartNaturality
import Yau.LeafProofs.L17HermitianMatrixAssemblyPullback

noncomputable section
open scoped Manifold

namespace Yau.LeafProofs.L17HermitianMatrixAssemblyAux

variable {n : ℕ} {M : ComplexManifold n}

/-- The native derivative of the chart, with the model tangent-space identification. -/
def canonicalTangentCoordinatesCLM (x : M.Carrier) : TangentVector M x →L[ℂ] ComplexVector n :=
  (NormedSpace.fromTangentSpace (𝕜 := ℂ) (chartPt x x)).toContinuousLinearMap.comp
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) x)

theorem canonicalTangentCoordinatesCLM_apply (x : M.Carrier) (v : TangentVector M x) :
    canonicalTangentCoordinatesCLM x v = tangentCoords x x v := rfl

/-- The canonical frame equivalence is derived from the actual two inverse differentials. -/
def canonicalTangentCoordinates (x : M.Carrier) : TangentVector M x ≃ₗ[ℂ] ComplexVector n where
  toLinearMap := (canonicalTangentCoordinatesCLM x).toLinearMap
  invFun := chartVec x x
  left_inv v := L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) v
  right_inv v := L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) v

theorem canonicalTangentCoordinates_apply (x : M.Carrier) (v : TangentVector M x) :
    canonicalTangentCoordinates x v = tangentCoords x x v := rfl

theorem canonicalTangentCoordinates_symm_apply (x : M.Carrier) (v : ComplexVector n) :
    (canonicalTangentCoordinates x).symm v = chartVec x x v := rfl

/-- Raw finite coordinates for the actual matrix Hermitian inner product. -/
def canonicalRawTangentCoordinates (x : M.Carrier) : TangentVector M x ≃ₗ[ℂ] (Fin n → ℂ) :=
  (canonicalTangentCoordinates x).trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))

theorem canonicalRawTangentCoordinates_apply (x : M.Carrier) (v : TangentVector M x) :
    canonicalRawTangentCoordinates x v = WithLp.ofLp (tangentCoords x x v) := rfl

end Yau.LeafProofs.L17HermitianMatrixAssemblyAux
