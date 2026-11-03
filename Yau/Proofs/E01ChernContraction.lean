import Yau.Proofs.E01TensorQuadratic
import Yau.Proofs.E01WirtingerCoordinates
import Yau.LeafProofs.L17ChartNaturality

/-! The actual centered Chern contraction, with the native conjugated curvature vector. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem centered_chern_residual_contraction
    (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (ξ a : ComplexVector n) :
    ellipsoidQuadratic
      ((complexMatrixWirt (hMat h x) (chartPt x x) a)ᵀ * (gMat h x)⁻¹ᵀ *
          (complexMatrixWirtBar (hMat h x) (chartPt x x) a)ᵀ -
        (complexMatrixWirt (fun w => complexMatrixWirtBar (hMat h x) w a) (chartPt x x) a)ᵀ) ξ =
      bisectionalForm h x (WithLp.toLp 2 (star (WithLp.ofLp ξ))) a := by
  have hH (i j : Fin n) : ContDiffAt ℝ 2 (fun w => hMat h x w i j) (chartPt x x) :=
    ((Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth h hs x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))).of_le (by simp)
  rw [complexMatrixWirt_direction_coordinates, complexMatrixWirtBar_direction_coordinates,
    complexMatrixMixed_direction_coordinates _ _ _ hH]
  have hh := quadratic_chern_residual_contraction (gMat h x)⁻¹
    (fun k => complexMatrixWirt (hMat h x) (chartPt x x) (stdVec k))
    (fun l => complexMatrixWirtBar (hMat h x) (chartPt x x) (stdVec l))
    (fun k l => complexMatrixWirt (fun w => complexMatrixWirtBar (hMat h x) w (stdVec l))
      (chartPt x x) (stdVec k)) (WithLp.ofLp a) ξ
  simpa only [complexMatrixWirt, complexMatrixWirtBar, chernCurvature,
    bisectionalForm, PiLp.toLp_apply, Pi.star_apply, star_star] using hh

end Yau.NodeProofs.E01Aux
