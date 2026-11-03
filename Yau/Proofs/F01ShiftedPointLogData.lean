import Yau.Proofs.F01NativeShiftedPoint
import Yau.Proofs.F01ShiftedNativeClock
import Yau.Proofs.F01PotentialClockRHS

/-! The native logdet identity and positivity require only the actual
clock point to lie in the supplied interval, not the normalization's
terminal clock to lie there. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_native_point_log_data
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : ρ ≠ 0) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) (p : Point n) (hz : ρ • p.1 ∈ ball 0 A.radius)
    (ht : τ + ρ ^ 2 * p.2 ∈ Icc 0 T) :
    flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
        (affineParabolicPoint ρ 0 τ p).2 =
      localPotentialClockRHS (shiftedComplexBackground A a ρ τ)
        (fun q => normalizedPotentialLogSource A a ρ q.1)
        (shiftedNativePotential A U a ρ τ) p ∧
    (chartPotentialMatrix (shiftedComplexBackground A a ρ τ)
      (shiftedNativePotential A U a ρ τ) p).PosDef := by
  have hMatrix := shifted_native_flow_matrix_at hg A h U hρ hU hpot a p hz ht
  have hSpace : (affineParabolicPoint ρ (0 : Space n) τ p).1 ∈ (A.chart a).source := by
    apply A.closedBall_source a
    simpa only [affineParabolicPoint, add_zero] using ball_subset_closedBall hz
  constructor
  · change flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
      (affineParabolicPoint ρ 0 τ p).2 =
      Real.log (chartPotentialMatrix (shiftedComplexBackground A a ρ τ)
        (shiftedNativePotential A U a ρ τ) p).det.re + normalizedPotentialLogSource A a ρ p.1
    rw [hMatrix]
    have hh := flowLogDetRatio_pullback_difference g h (A.chart a)
      (A.differentiable a) (A.inverse_differentiable a) hSpace
      (affineParabolicPoint ρ 0 τ p).2
    simpa only [normalizedPotentialLogSource, BoundedChartFamily.backgroundLogDet,
      affineParabolicPoint, add_zero, sub_eq_add_neg] using hh
  · rw [hMatrix]
    exact pullbackMatrix_posDef _ (A.chart a) (A.differentiable a)
      (A.inverse_differentiable a) hSpace

end Yau.NodeProofs.F01Aux
