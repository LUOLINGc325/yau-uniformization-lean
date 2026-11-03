import Yau.LeafProofs.L17BootstrapRelativeLogarithm
import Yau.LeafProofs.L17LocalHolderAlgebraBilinear
import Yau.LeafProofs.L17NonlinearResidual

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux
open L17LocalHolderBanachAlgebraAux
local instance conjugatedResidualMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)

def relativeLogDifference
    (K Hstar Htheta Hzero : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma) : LocalHolderSpace ℝ P T gamma :=
  (valueContinuousLinearEquiv ℝ P T gamma)
    (relativeTraceLog P T gamma K Hstar Htheta-relativeTraceLog P T gamma K Hstar Hzero)-dLog

def assembledLogCorrection
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (sigma : LocalHolderSpace ℝ P T gamma)
    (K Hstar Htheta Hzero : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma) : HolderSpace P T gamma :=
  J (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma
    (relativeLogDifference P T gamma K Hstar Htheta Hzero dLog))

theorem assembledLogCorrection_zero
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (sigma : LocalHolderSpace ℝ P T gamma)
    (K Hstar H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) :
    assembledLogCorrection P T gamma J sigma K Hstar H H 0=0 := by
  unfold assembledLogCorrection relativeLogDifference
  rw [sub_self,map_zero,sub_zero,map_zero,map_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem assembledLogCorrection_contDiffOn
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (sigma : LocalHolderSpace ℝ P T gamma)
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {dLog : E → LocalHolderSpace ℝ P T gamma}
    (hHt : ContDiffOn ℝ ∞ Htheta s) (hH0 : ContDiffOn ℝ ∞ Hzero s)
    (hdLog : ContDiffOn ℝ ∞ dLog s)
    (hSmallt : ∀a∈s, ‖relativeMetricPerturbation P T gamma K Hstar (Htheta a)‖<1)
    (hSmall0 : ∀a∈s, ‖relativeMetricPerturbation P T gamma K Hstar (Hzero a)‖<1) :
    ContDiffOn ℝ ∞ (fun a => assembledLogCorrection P T gamma J sigma K Hstar
      (Htheta a) (Hzero a) (dLog a)) s := by
  have hD := ((valueContinuousLinearEquiv ℝ P T gamma).contDiff.comp_contDiffOn
    ((relativeTraceLog_contDiffOn P T gamma K Hstar hHt hSmallt).sub
      (relativeTraceLog_contDiffOn P T gamma K Hstar hH0 hSmall0))).sub hdLog
  exact J.contDiff.comp_contDiffOn
    ((localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma).contDiff.comp_contDiffOn hD)

end Yau.LeafProofs.L17BootstrapMetricAux
