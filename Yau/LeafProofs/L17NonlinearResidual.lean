import Yau.LeafProofs.L17NonlinearDerivative
import Yau.LeafProofs.L17ScalarLinearization
import Yau.LeafProofs.L17ParabolicOperator

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance nonlinearResidualTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

def scalarNonlinearResidualMap (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (u : SchauderSpace P T γ hT) : HolderSpace P T γ :=
  scalarParabolicCLM P T γ hT hTime hγ1 hr u-globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u

theorem scalarNonlinearResidualMap_contDiffOn
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ) :
    ContDiffOn ℝ ∞ (scalarNonlinearResidualMap P T γ hT hTime hγ hγ1 hr J)
      {u | ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1} := by
  intro u hu
  exact ((scalarParabolicCLM P T γ hT hTime hγ1 hr).contDiff.contDiffAt.sub
    (globalNonlinearMap_contDiffAt P T γ hT hTime hγ hγ1 hr J hu)).contDiffWithinAt

theorem scalarNonlinearResidual_domain_isOpen :
    IsOpen {u : SchauderSpace P T γ hT |
      ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1} :=
  isOpen_lt (normalizedMetricPerturbation_contDiff P T γ hT hTime hγ hγ1 hr).continuous.norm continuous_const

theorem scalarNonlinearResidualMap_hasFDerivAt
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1) :
    HasFDerivAt (scalarNonlinearResidualMap P T γ hT hTime hγ hγ1 hr J)
      (scalarParabolicCLM P T γ hT hTime hγ1 hr-
        fderiv ℝ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u) u := by
  have hN := (globalNonlinearMap_contDiffAt P T γ hT hTime hγ hγ1 hr J hu).differentiableAt (by simp)
  exact (scalarParabolicCLM P T γ hT hTime hγ1 hr).hasFDerivAt.sub hN.hasFDerivAt

theorem exists_scalarNonlinearResidual_linearization
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (e : SchauderSpace P T γ hT ≃L[ℝ] HolderSpace P T γ)
    (he : e.toContinuousLinearMap=scalarParabolicCLM P T γ hT hTime hγ1 hr)
    {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)
    (hD : ‖e.symm.toContinuousLinearMap‖*
      ‖fderiv ℝ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u‖≤1/4) :
    ∃ B : SchauderSpace P T γ hT ≃L[ℝ] HolderSpace P T γ,
      B.toContinuousLinearMap=fderiv ℝ (scalarNonlinearResidualMap P T γ hT hTime hγ hγ1 hr J) u ∧
      ‖B.symm.toContinuousLinearMap‖≤(4/3)*‖e.symm.toContinuousLinearMap‖ := by
  let D := fderiv ℝ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u
  have hlt : ‖e.symm.toContinuousLinearMap‖*‖D‖<1 := by linarith
  let B := subPerturbationEquiv e D hlt
  refine ⟨B,?_,subPerturbationEquiv_symm_norm_le e D hlt hD⟩
  rw [(scalarNonlinearResidualMap_hasFDerivAt P T γ hT hTime hγ hγ1 hr J hu).fderiv]
  apply ContinuousLinearMap.ext
  intro w
  change subPerturbationEquiv e D hlt w=_
  rw [subPerturbationEquiv_apply]
  change e.toContinuousLinearMap w-D w=_
  rw [he]
  rfl

end Yau.LeafProofs.L17Aux
