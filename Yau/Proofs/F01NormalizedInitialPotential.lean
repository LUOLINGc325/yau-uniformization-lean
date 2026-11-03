import Yau.Proofs.F01NormalizedInitialFlowMatrix
import Yau.Proofs.F01ParabolicDilationTime
import Yau.Proofs.F01InitialPotentialEquation

/-! The actual short-time native potential supplies the original
normalized initial-surface C2 and equation inputs, with the same background,
the genuine zero extension, and both closed time faces. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem bounded_chart_spaceTime_smooth {α : HermitianField M} (A : BoundedChartFamily α)
    {U : M.Carrier → ℝ → ℝ} {I : Set ℝ} (hU : SmoothSpaceTime U I) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun q : Point n => U (A.chart a q.1) q.2) (ball 0 A.radius ×ˢ I) :=
  (smoothSpaceTime_holomorphic_chart hU (A.chart a) (A.differentiable a)).mono
    (prod_mono (fun z hz => A.closedBall_source a (ball_subset_closedBall hz)) Subset.rfl)

theorem normalized_initial_potential_C2
    (α : HermitianField M) (A : BoundedChartFamily α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α) (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s) (a : M.Carrier) :
    C2 (ball 0 1 ×ˢ Icc (-1) 1) (forwardZeroSpaceTime
      (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) :=
  parabolicRescalePotential_zeroExtension_C2
    (F := fun q : Point n => U (A.chart a q.1) q.2)
    (D := fun q : Point n => flowLogDetRatio α h (A.chart a q.1) q.2) hρ hρr hρT
    (bounded_chart_spaceTime_smooth A hU a) (fun x _ => hU0 (A.chart a x))
    (fun x _ => flowLogDetRatio_initial α h hh0 (A.chart a x))
    (fun x _ s hs => hpde (A.chart a x) s hs)

theorem normalized_zero_potential_initial_equation
    (α : HermitianField M) (hα : MetricSmooth α) (A : BoundedChartFamily α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α) (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    timeD (ball 0 1 ×ˢ Icc (-1) 1) (forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) p -
      logDetReal (clampedBackground (fun z => pullbackMatrix α (A.chart a) (ρ • z)) p +
        complexHessianMap (hessian (forwardZeroSpaceTime
          (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) p)) =
      backgroundSource (fun z => pullbackMatrix α (A.chart a) (ρ • z)) p := by
  have hd := zero_extended_parabolicRescalePotential_timeD
    (F := fun q : Point n => U (A.chart a q.1) q.2)
    (D := fun q : Point n => flowLogDetRatio α h (A.chart a q.1) q.2) hρ hρr hρT
    (fun x _ => hU0 (A.chart a x))
    (fun x _ => flowLogDetRatio_initial α h hh0 (A.chart a x))
    (fun x _ s hs => hpde (A.chart a x) s hs) hp
  rw [hd, normalized_initial_transformed_flow_matrix α hα A h U hρ hρr hρT hU hh0 hpot a hp]
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have hs : ρ • p.1 ∈ (A.chart a).source := A.closedBall_source a (ball_subset_closedBall hz)
  rw [logDetReal_iota_posDef _
    (pullbackMatrix_posDef _ (A.chart a) (A.differentiable a) (A.inverse_differentiable a) hs)]
  change flowLogDetRatio α h (A.chart a (ρ • p.1)) (ρ ^ 2 * max p.2 0) -
    Real.log (pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1)).det.re = _
  rw [flowLogDetRatio_pullback_difference α h (A.chart a) (A.differentiable a)
    (A.inverse_differentiable a) hs]
  unfold backgroundSource
  ring

end Yau.NodeProofs.F01Aux
