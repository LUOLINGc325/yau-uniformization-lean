import Yau.Proofs.F01ClosedMetricEvolution
import Yau.Proofs.F01NativeScalarHeat
import Yau.Proofs.F01MetricFamilySlices

/-! The original short-time potential tuple has the actual scalar
logdet evolution and heat equation on the entire original closed slab. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem closed_slab_logdet_evolution_and_heat
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) (Icc 0 T) s)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (flowLogDetRatio α h x) (-scalarCurvature (h t) x) (Icc 0 T) t ∧
      fieldHeatWithin h (Icc 0 T) (fun s y => flowLogDetRatio α h y s) x t =
        -traceWith (gMat (h t) x) (ricci α x) := by
  have hmetric (i j : Fin n) :=
    closed_slab_potential_metric_evolution α hα h U hT hh hU hpot hpde x i j t ht
  exact ⟨native_logdet_ratio_hasDerivWithinAt α h x hmetric,
    native_logdet_ratio_heat_identity α hα h (metricFamilySmooth_slice hh ht) x
      ((uniqueDiffOn_Icc hT) t ht) hmetric⟩

end Yau.NodeProofs.F01Aux
