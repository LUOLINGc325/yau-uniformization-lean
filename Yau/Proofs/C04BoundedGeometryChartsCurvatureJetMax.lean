import Yau.Proofs.C04BoundedGeometryChartsCurvatureJetTop
import Yau.Proofs.C04BoundedGeometryChartsCompactJetNorm

/-! The actual compact curvature maxima satisfy the same highest-order estimate. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem radialCurvatureOperator_jetMax_top
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (hm : 1 ≤ m) {L : ℝ} (hL : 1 ≤ L)
    (hcurv : ∀ j x, x ∈ Metric.closedBall (0 : ComplexVector n) R →
      curvatureJetNorm g.form j (unitaryExponential g p U x) ≤ K j)
    (hA0 : ∀ x ∈ Metric.closedBall (0 : ComplexVector n) R, ‖radialCoframe g p U x‖ ≤ 2)
    (hlow : ∀ k < m,
      closedBallJetNorm R (radialCoframe g p U) k ≤ L ∧
      closedBallJetNorm R (radialConnection g p U) k ≤ L) :
    closedBallJetNorm R (radialCurvatureOperator g p U) m ≤
      curvatureTopCoefficient n K * closedBallJetNorm R (radialCoframe g p U) m +
        curvatureLowerJetBudget n K m L := by
  apply closedBallJetNorm_le hR _ (radialCurvatureOperator_smooth g p U hU) m
  intro x hx
  have H := radialCurvatureOperator_jet_top g p U hU K hK m hm x hL
    (fun j hj => hcurv j x hx) (hA0 x hx)
    (fun k hk => (norm_iteratedFDeriv_le_closedBallJetNorm hR _ (radialCoframe_smooth g p U) k hx).trans (hlow k hk).1)
    (fun k hk => (norm_iteratedFDeriv_le_closedBallJetNorm hR _ (radialConnection_smooth g p U) k hx).trans (hlow k hk).2)
  exact H.trans (add_le_add (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_le_closedBallJetNorm hR _ (radialCoframe_smooth g p U) m hx)
    (curvatureTopCoefficient_nonneg (n := n) K hK)) le_rfl)

def curvatureZeroJetBudget (n : ℕ) (K : ℕ → ℝ) : ℝ :=
  ‖curvatureRaisingMap n‖ * curvatureFormModelBound n K 0 * 4

theorem curvatureZeroJetBudget_nonneg (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) :
    0 ≤ curvatureZeroJetBudget n K := by
  have H := curvatureFormModelBound_nonneg (n := n) K hK 0
  unfold curvatureZeroJetBudget
  positivity

theorem radialCurvatureOperator_jetMax_zero
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) {R : ℝ} (hR : 0 ≤ R)
    (hcurv : ∀ x ∈ Metric.closedBall (0 : ComplexVector n) R,
      curvatureJetNorm g.form 0 (unitaryExponential g p U x) ≤ K 0)
    (hA0 : ∀ x ∈ Metric.closedBall (0 : ComplexVector n) R, ‖radialCoframe g p U x‖ ≤ 2) :
    closedBallJetNorm R (radialCurvatureOperator g p U) 0 ≤ curvatureZeroJetBudget n K := by
  apply closedBallJetNorm_le hR _ (radialCurvatureOperator_smooth g p U hU) 0
  intro x hx
  rw [norm_iteratedFDeriv_zero]
  have hT := radialCurvatureForm_norm_le g p U hU 0 x (hK 0) (hcurv x hx)
  have hAn : 0 ≤ ‖radialCoframe g p U x‖ := norm_nonneg _
  have hAsq : ‖radialCoframe g p U x‖ ^ 2 ≤ 4 := by nlinarith [hA0 x hx]
  exact (radialCurvatureOperator_norm_le g p U x).trans (by
    unfold curvatureZeroJetBudget
    exact mul_le_mul (mul_le_mul_of_nonneg_left hT (norm_nonneg _)) hAsq
      (sq_nonneg _) (mul_nonneg (norm_nonneg _) (curvatureFormModelBound_nonneg K hK 0)))

end Yau.Proofs.C04ChartsAux
