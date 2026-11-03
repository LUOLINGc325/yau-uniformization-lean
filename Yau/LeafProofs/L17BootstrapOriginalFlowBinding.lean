import Yau.LeafProofs.L17PotentialEquation

/-! The original closed-time Hermitian potential-flow conditions with comparison constant two. -/
noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapOriginalFlowBindingAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux

local instance originalFlowBindingMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Bind the actual potential equation, metric bounds and smoothness to the original leaf body. -/
theorem potential_flow_original_conditions
    (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hr : P.radius ≤ 1) (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w) = L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u : SchauderSpace P T gamma hT)
    (hZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖ < 1)
    (hSmall : ‖u‖ + T * backgroundLogDetHessianBudget P.charts ≤ (P.charts.bound 0)⁻¹)
    (hEq : scalarParabolicCLM P T gamma hT hTime hgamma1 hr u =
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u)
    (hSmoothU : SmoothSpaceTime (potentialFunction u) (Icc 0 T))
    (hSmoothH : MetricFamilySmooth (potentialFlowField hg u hSmall) (Icc 0 T)) :
    potentialFlowField hg u hSmall 0 = g ∧
      MetricFamilySmooth (potentialFlowField hg u hSmall) (Icc 0 T) ∧
      SmoothSpaceTime (potentialFunction u) (Icc 0 T) ∧
      (∀ x, potentialFunction u x 0 = 0) ∧
      ∀ x t, t ∈ Icc 0 T →
        (gMat (potentialFlowField hg u hSmall t) x -
          (((2 : ℝ)⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((2 : ℂ) • gMat g x - gMat (potentialFlowField hg u hSmall t) x).PosSemidef ∧
        gMat (potentialFlowField hg u hSmall t) x =
          gMat g x - (t : ℂ) • ricci g x + levi (fun y => potentialFunction u y t) x ∧
        HasDerivWithinAt (potentialFunction u x)
          (Real.log ((gMat (potentialFlowField hg u hSmall t) x).det.re / (gMat g x).det.re))
          (Icc 0 T) t := by
  refine ⟨potentialFlowField_initial hg u hSmall, hSmoothH, hSmoothU,
    potentialFunction_initial u, ?_⟩
  intro x t ht
  let ti : Time T := ⟨t, ht⟩
  have hCompare := potentialFlowField_comparison hg u hSmall ti x
  refine ⟨?_, hCompare.2, potentialFlowField_matrix_identity hg u hSmall ti x, ?_⟩
  · simpa only [show (((2 : ℝ)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num] using hCompare.1
  · exact potentialFunction_hasDerivWithinAt_of_equation P T gamma hT hTime
      hgamma0 hgamma1 hr hg J hJ u hZ hSmall hEq x ti

end Yau.LeafProofs.L17BootstrapOriginalFlowBindingAux
