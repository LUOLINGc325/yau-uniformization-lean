import Yau.LeafProofs.L17MatrixLogarithmHolder

open Set Metric
open scoped Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17LocalHolderBanachAlgebraAux
local instance potentialTraceTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalizedPotential_trace_eq_laplacian (P : UniformChartPartition g)
    (T γ : ℝ) (hT : 0<T) (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    matrixRealTraceBanachCLM P T γ (normalizedPotentialCLM P T γ hT hTime hγ hr u) q =
      actualLaplacian u (chartPoint P T q.1 q.2) := by
  rw [matrixRealTraceBanachCLM_value,normalizedPotentialCLM_value]
  change traceWith (pullbackMatrix g (P.charts.chart q.1) q.2.1)
    (leviC (chartFunction u q.1 q.2.2) q.2.1) =
      laplacian g (fun y => schauderFun u (y,q.2.2)) (P.charts.chart q.1 q.2.1)
  rw [traceWith_levi_eq_scalarSymbol _
    ((chartFunction_contDiffOn_two u q.1 q.2.2).contDiffAt (isOpen_ball.mem_nhds q.2.1.property)),
    selected_chart_laplacian u q.1 q.2.1 q.2.2]
  change realHessianContraction (chartCoefficient P.charts q.1 q.2.1)
    (chartFunction u q.1 q.2.2) q.2.1 = _
  rw [← hessianContractionCLM_eq_actual,(chartFunction_hasSecondFDerivAt u q.1 q.2.2 q.2.1.property).fderiv]

end Yau.LeafProofs.L17Aux
