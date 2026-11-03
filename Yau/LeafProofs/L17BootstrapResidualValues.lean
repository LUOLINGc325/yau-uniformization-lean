import Yau.LeafProofs.L17NonlinearPointValues

noncomputable section
open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17LocalHolderBanachAlgebraAux
local instance bootstrapResidualValuesMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)

/-- The original totalized nonlinearity has its actual logarithmic value throughout
its analytic domain wherever the actual coordinate metric is positive. -/
theorem localNonlinearMap_value_of_positive (hg : MetricSmooth g)
    (u : SchauderSpace P T gamma hT)
    (hu : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (q : LocalCylinder P T)
    (hPos : (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q).PosDef) :
    localNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr u q=
      potentialNonlinearFunction u (chartPoint P T q.1 q.2) := by
  rw [localNonlinearMap_trace_identity P T gamma hT hTime hgamma0 hgamma1 hr u]
  change matrixTraceLogIncrement P T gamma _ q-matrixRealTraceBanachCLM P T gamma _ q=_
  rw [matrixTraceLogIncrement_value P T gamma _ hu,
    normalizedPotential_trace_eq_laplacian P T gamma hT hTime hgamma1 hr u q]
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hG := pullbackMatrix_posDef g (P.charts.chart q.1) (P.charts.differentiable q.1)
    (P.charts.inverse_differentiable q.1) (P.charts.closedBall_source q.1 (ball_subset_closedBall hz))
  have hPoint := normalizedMetricPerturbation_point_norm_lt_one P T gamma hT hTime hgamma0 hgamma1 hr hu q
  have hValue : normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u q=
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*coordinateMetricError u q := by
    rw [normalizedMetricPerturbation_value,coordinateMetricError_eq]
  rw [hValue] at hPoint ⊢
  rw [matrixTraceLogIncrement_eq_logdet_ratio _ _ hG hPos hPoint,
    coordinateMetricMatrix_determinant_ratio hg u q]
  rfl

theorem globalNonlinearMap_value_of_positive (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ v, holderFun (J v)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P v)
    (u : SchauderSpace P T gamma hT)
    (hu : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (hPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q).PosDef) :
    holderFun (globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u)=potentialNonlinearFunction u ∧
      Continuous (potentialNonlinearFunction u) := by
  apply globalNonlinearMap_value_of_compatible P T gamma hT hTime hgamma0 hgamma1 hr J hJ u
  intro p zt
  exact localNonlinearMap_value_of_positive P T gamma hT hTime hgamma0 hgamma1 hr hg u hu ⟨p,zt⟩ (hPos _)

end Yau.LeafProofs.L17BootstrapMetricAux
