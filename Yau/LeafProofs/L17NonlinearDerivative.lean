import Yau.LeafProofs.L17GlobalNonlinearMap

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance nonlinearDerivativeTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

theorem normalizedPotentialCLM_opNorm_le :
    ‖normalizedPotentialCLM P T γ hT hTime hγ1 hr‖≤normalizedPotentialBudget P.charts γ :=
  (normalizedPotentialCLM P T γ hT hTime hγ1 hr).opNorm_le_bound
    (normalizedPotentialBudget_nonneg P.charts γ)
    (normalizedPotentialCLM_norm_le P T γ hT hTime hγ1 hr)

theorem normalizedMetricPerturbation_hasFDerivAt (u : SchauderSpace P T γ hT) :
    HasFDerivAt (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr)
      (normalizedPotentialCLM P T γ hT hTime hγ1 hr) u :=
  (normalizedPotentialCLM P T γ hT hTime hγ1 hr).hasFDerivAt.sub_const _

theorem localNonlinearMap_hasFDerivAt {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1) :
    HasFDerivAt (localNonlinearMap P T γ hT hTime hγ hγ1 hr)
      ((fderiv ℝ (matrixTraceLogRemainder P T γ)
        (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u)).comp
          (normalizedPotentialCLM P T γ hT hTime hγ1 hr)) u := by
  have hR := ((matrixTraceLogRemainder_contDiffOn P T γ).contDiffAt
    (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hu))).differentiableAt (by simp)
  exact (hR.hasFDerivAt.comp u
    (normalizedMetricPerturbation_hasFDerivAt P T γ hT hTime hγ hγ1 hr u)).sub_const _

theorem localNonlinearMap_fderiv_norm_le {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤1/8) :
    ‖fderiv ℝ (localNonlinearMap P T γ hT hTime hγ hγ1 hr) u‖≤
      16*‖matrixRealTraceCLM n‖*‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖*
        normalizedPotentialBudget P.charts γ := by
  rw [(localNonlinearMap_hasFDerivAt P T γ hT hTime hγ hγ1 hr (by linarith : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (matrixTraceLogRemainder_fderiv_norm_le P T γ hu)
      (normalizedPotentialCLM_opNorm_le P T γ hT hTime hγ1 hr)
      (norm_nonneg _) (by positivity))

theorem globalNonlinearMap_hasFDerivAt
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1) :
    HasFDerivAt (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J)
      ((nonlinearAssemblyCLM P T γ J).comp
        (fderiv ℝ (localNonlinearMap P T γ hT hTime hγ hγ1 hr) u)) u := by
  have hN := (localNonlinearMap_contDiffAt P T γ hT hTime hγ hγ1 hr hu).differentiableAt (by simp)
  exact (nonlinearAssemblyCLM P T γ J).hasFDerivAt.comp u hN.hasFDerivAt

theorem globalNonlinearMap_fderiv_norm_le
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤1/8) :
    ‖fderiv ℝ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u‖≤
      8*‖J‖*‖matrixRealTraceCLM n‖*‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖*
        normalizedPotentialBudget P.charts γ := by
  rw [(globalNonlinearMap_hasFDerivAt P T γ hT hTime hγ hγ1 hr J
    (by linarith : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)).fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (nonlinearAssemblyCLM_opNorm_le P T γ J)
      (localNonlinearMap_fderiv_norm_le P T γ hT hTime hγ hγ1 hr hu)
      (norm_nonneg _) (by positivity)).trans_eq (by ring))

end Yau.LeafProofs.L17Aux
