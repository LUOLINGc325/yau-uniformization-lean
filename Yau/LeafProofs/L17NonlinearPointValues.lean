import Yau.LeafProofs.L17PotentialMetricNaturality
import Yau.LeafProofs.L17GlobalNonlinearMap
import Yau.LeafProofs.L17MatrixLogDetPath
import Yau.LeafProofs.L17NormalizedPotentialTrace

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17LocalHolderBanachAlgebraAux L17BanachLogarithmAux
local instance nonlinearPointValuesTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

theorem localNonlinearMap_trace_identity (u : SchauderSpace P T γ hT) :
    localNonlinearMap P T γ hT hTime hγ hγ1 hr u=
      matrixTraceLogIncrement P T γ (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u)-
        matrixRealTraceBanachCLM P T γ (normalizedPotentialCLM P T γ hT hTime hγ1 hr u) := by
  unfold localNonlinearMap matrixTraceLogRemainder matrixTraceLogIncrement logRemainder normalizedMetricPerturbation
  rw [(matrixRealTraceBanachCLM P T γ).map_sub,(matrixRealTraceBanachCLM P T γ).map_sub]
  abel

theorem normalizedMetricPerturbation_point_norm_lt_one {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)
    (q : LocalCylinder P T) :
    ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u q‖<1 := by
  have hb := (evalCLM (Matrix (Fin n) (Fin n) ℂ) P T γ q).le_of_opNorm_le
    (evalCLM_norm_le_half (Matrix (Fin n) (Fin n) ℂ) P T γ q)
      (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u)
  change ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u q‖≤
    (1/2 : ℝ)*‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖ at hb
  linarith

def potentialNonlinearFunction {P : UniformChartPartition g} {T γ : ℝ} {hT : 0<T} (u : SchauderSpace P T γ hT) (q : Cylinder M T) : ℝ :=
  Real.log ((potentialMetricMatrix u q).det.re/(gMat g q.1).det.re)-actualLaplacian u q

theorem localNonlinearMap_value (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (q : LocalCylinder P T) :
    localNonlinearMap P T γ hT hTime hγ hγ1 hr u q=
      potentialNonlinearFunction u (chartPoint P T q.1 q.2) := by
  rw [localNonlinearMap_trace_identity P T γ hT hTime hγ hγ1 hr u]
  change matrixTraceLogIncrement P T γ _ q-matrixRealTraceBanachCLM P T γ _ q=_
  rw [matrixTraceLogIncrement_value P T γ _ hu,
    normalizedPotential_trace_eq_laplacian P T γ hT hTime hγ1 hr u q]
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hG := pullbackMatrix_posDef g (P.charts.chart q.1) (P.charts.differentiable q.1)
    (P.charts.inverse_differentiable q.1) (P.charts.closedBall_source q.1 (ball_subset_closedBall hz))
  have hE := (coordinateMetric_half_double u hSmall q).1
  have hPoint := normalizedMetricPerturbation_point_norm_lt_one P T γ hT hTime hγ hγ1 hr hu q
  have hValue : normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u q=
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*coordinateMetricError u q := by
    rw [normalizedMetricPerturbation_value,coordinateMetricError_eq]
  rw [hValue] at hPoint ⊢
  rw [matrixTraceLogIncrement_eq_logdet_ratio _ _ hG hE hPoint,
    coordinateMetricMatrix_determinant_ratio hg u q]
  rfl

theorem globalNonlinearMap_value (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (hJ : ∀ v, holderFun (J v)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P v)
    (u : SchauderSpace P T γ hT)
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹) :
    holderFun (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u)=potentialNonlinearFunction u ∧
      Continuous (potentialNonlinearFunction u) := by
  apply globalNonlinearMap_value_of_compatible P T γ hT hTime hγ hγ1 hr J hJ u
  intro p zt
  exact localNonlinearMap_value P T γ hT hTime hγ hγ1 hr hg u hu hSmall ⟨p,zt⟩

end Yau.LeafProofs.L17Aux
