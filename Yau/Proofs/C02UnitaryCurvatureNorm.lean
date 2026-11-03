import Yau.Proofs.C02UnitaryFrameMatrix
import Yau.Proofs.C02TensorOrthonormalNorm

noncomputable section
open scoped Matrix InnerProductSpace Manifold
namespace Yau.Blueprint.C02Proof
open Yau.NodeProofs.G01Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureJetNorm_zero_eq_unitary_frame_norm (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    curvatureJetNorm h 0 p =
      ‖(WithLp.toLp 2 (tensorFrameTransform (physicalUnitaryRealMatrix (unitaryFrameMatrix p U))
        (rmTensor h p (chartPt p p))) : EuclideanSpace ℝ (Fin 4 → RIdx n))‖ := by
  apply sqrt_covTensorNormSq_eq_frame_norm
  rw [realMetricFn_eq_rawReal]
  exact physicalUnitaryRealMatrix_gram _ _ (unitaryFrameMatrix_gram h p U hU)

end Yau.Blueprint.C02Proof
