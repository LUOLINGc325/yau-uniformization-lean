import Yau.LeafProofs.L17PotentialHermitianField
import Yau.LeafProofs.L17ParabolicOperator

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance potentialEquationTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

theorem potentialFunction_hasDerivWithinAt_of_equation (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (hJ : ∀ v, holderFun (J v)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P v)
    (u : SchauderSpace P T γ hT)
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hEq : scalarParabolicCLM P T γ hT hTime hγ1 hr u=
      globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u)
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (potentialFunction u x)
      (Real.log ((gMat (potentialFlowField hg u hSmall (t : ℝ)) x).det.re/(gMat g x).det.re))
      (Icc (0:ℝ) T) (t : ℝ) := by
  have hN := (globalNonlinearMap_value P T γ hT hTime hγ hγ1 hr hg J hJ u hu hSmall).1
  have h := congrArg (fun w : HolderSpace P T γ => holderFun w (x,t)) hEq
  rw [scalarParabolicCLM_value,hN] at h
  change timeFun u (x,t)-actualLaplacian u (x,t)=
    Real.log ((potentialMetricMatrix u (x,t)).det.re/(gMat g x).det.re)-actualLaplacian u (x,t) at h
  have hTimeEq : timeFun u (x,t)=
      Real.log ((potentialMetricMatrix u (x,t)).det.re/(gMat g x).det.re) := by linarith
  have hD := schauderFun_hasDerivWithinAt u x t
  change HasDerivWithinAt (potentialFunction u x) (timeFun u (x,t)) (Icc (0:ℝ) T) (t : ℝ) at hD
  rw [hTimeEq] at hD
  rw [gMat_potentialFlowField]
  exact hD

end Yau.LeafProofs.L17Aux
