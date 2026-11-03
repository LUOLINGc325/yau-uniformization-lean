import Yau.LeafProofs.L17BootstrapResidualPointValue
import Yau.LeafProofs.L17BootstrapMetricBase

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux
local instance candidateCoordinateResidualMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)

/-- The actual scalar residual has its coordinate determinant value on every
original chart cylinder, with no additional norm-smallness premise. -/
theorem scalarResidual_value_in_chart (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u : SchauderSpace P T gamma hT)
    (huZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (huPos : ∀q : LocalCylinder P T,
      (Hstar P hT hTime hgamma0 hgamma1 hr u q).PosDef)
    (q : LocalCylinder P T) :
    holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J u)
      (chartPoint P T q.1 q.2)=timeFun u (chartPoint P T q.1 q.2)-
        Real.log ((Hstar P hT hTime hgamma0 hgamma1 hr u q).det.re/
          (pullbackMatrix g (P.charts.chart q.1) q.2.1).det.re) := by
  have hPos : ∀r : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart r.1) r.2.1+coordinateMetricError u r).PosDef := by
    intro r
    simpa only [Hstar_value] using huPos r
  rw [scalarNonlinearResidualMap_value_of_positive P T gamma hT hTime hgamma0 hgamma1 hr
    hg J hJ u huZ hPos]
  rw [Hstar_value,coordinateMetricMatrix_determinant_ratio hg u q]

/-- The original equation gives the actual time derivative as the coordinate
logarithmic determinant ratio, including the two endpoints. -/
theorem timeFun_eq_coordinate_logratio_of_equation (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u : SchauderSpace P T gamma hT)
    (huZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (huPos : ∀q : LocalCylinder P T,
      (Hstar P hT hTime hgamma0 hgamma1 hr u q).PosDef)
    (hEquation : scalarParabolicCLM P T gamma hT hTime hgamma1 hr u=
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u)
    (q : LocalCylinder P T) :
    timeFun u (chartPoint P T q.1 q.2)=
      Real.log ((Hstar P hT hTime hgamma0 hgamma1 hr u q).det.re/
        (pullbackMatrix g (P.charts.chart q.1) q.2.1).det.re) := by
  have hPhi : scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J u=0 := by
    change scalarParabolicCLM P T gamma hT hTime hgamma1 hr u-
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u=0
    rw [hEquation,sub_self]
  have h := congrArg (fun w => holderFun w (chartPoint P T q.1 q.2)) hPhi
  rw [scalarResidual_value_in_chart P T gamma hT hTime hgamma0 hgamma1 hr hg J hJ u huZ huPos q] at h
  exact sub_eq_zero.mp h

/-- The finite logarithm cancellation used for the transported equation. -/
theorem coordinate_logratio_cancellation {a b c d : ℝ}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    Real.log (a/c)-Real.log (b/d)=Real.log (a/b)-(Real.log c-Real.log d) := by
  rw [Real.log_div ha hc,Real.log_div hb hd,Real.log_div ha hb]
  ring

end Yau.LeafProofs.L17BootstrapMetricAux
