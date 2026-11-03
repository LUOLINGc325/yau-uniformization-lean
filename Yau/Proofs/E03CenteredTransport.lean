import Yau.Proofs.E03EnvelopeChartChange
import Yau.Proofs.V03DualTransport
import Yau.Proofs.E01Congruence

/-! SOURCE-ONLY E03 candidate: one actual centered fiber map transports both norm and envelope. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.E01Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem centered_fiber_matrix_isUnit (c y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) c).source) :
    IsUnit (tangentFrameMatrix c y y)ᵀ := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
  exact (tangentFrameMatrix_isUnit c y hy).map Matrix.detMonoidHom

theorem centered_cometric_congruence (h : HermitianField M) (c y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) c).source) :
    (tangentFrameMatrix c y y)ᵀᴴ * ((hMat h c (chartPt c y))⁻¹)ᵀ *
        (tangentFrameMatrix c y y)ᵀ = ((gMat h y)⁻¹)ᵀ := by
  rw [hMat_eq_centered_congruence h c y hy]
  exact inverse_transpose_congruence (gMat h y) (tangentFrameMatrix c y y)
    (tangentFrameMatrix_isUnit c y hy)

theorem centered_covector_coordinates (c y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) c).source) (ξ : Covector n) :
    covectorCoords c y ξ = matrixFiberMap (tangentFrameMatrix c y y)ᵀ
      (covectorCoords y y ξ) := by
  apply WithLp.ofLp_injective
  exact covectorCoords_eq_transpose_mulVec c y hy ξ

theorem centered_envelope_congruence (h : ℝ → HermitianField M) (T : ℝ)
    (c y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) c).source)
    (η : ComplexVector n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    envelopeChart h T c (chartPt c y, matrixFiberMap (tangentFrameMatrix c y y)ᵀ η, t) =
      envelopeChart h T y (chartPt y y, η, t) := by
  have hself : y ∈ (extChartAt (ComplexModel n) y).source :=
    mem_extChartAt_source (I := ComplexModel n) y
  have hbase : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv hself
  have htarget : chartPt y y ∈ chartTarget y :=
    mem_extChartAt_target (I := ComplexModel n) y
  have hother : chartInv y (chartPt y y) ∈ (extChartAt (ComplexModel n) c).source := by
    rwa [hbase]
  have he := envelopeChart_chartChange h T y c (chartPt y y, η, t) htarget hother ht
  have hcoords : spaceTimeChartChange y c (chartPt y y, η, t) =
      (chartPt c y, matrixFiberMap (tangentFrameMatrix c y y)ᵀ η, t) := by
    change (chartPt c (chartInv y (chartPt y y)),
      covectorCoords c (chartInv y (chartPt y y))
        (covectorOfCoords y (chartInv y (chartPt y y)) η), t) = _
    rw [hbase, centered_covector_coordinates c y hy,
      covectorCoords_ofCoords y y hself η]
  rw [hcoords] at he
  exact he

end Yau.NodeProofs.E03Aux
