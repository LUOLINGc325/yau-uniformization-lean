import Yau.Proofs.C04BoundedGeometryChartsRadialIntegrals
import Yau.Proofs.C04BoundedGeometryChartsCompactJetNorm

/-! Integral inequalities for the genuine compact jet maxima. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem radialConnection_iteratedFDeriv_integral_bound (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    {R : ℝ} (hR : 0 ≤ R) (m : ℕ) {x : ComplexVector n}
    (hx : x ∈ Metric.closedBall (0 : ComplexVector n) R) :
    ‖iteratedFDeriv ℝ m (radialConnection g p U) x‖ ≤
      R * closedBallJetNorm R (radialCurvatureOperator g p U) m +
        (m : ℝ) * closedBallJetNorm R (radialCurvatureOperator g p U) (m - 1) := by
  have hO := radialCurvatureOperator_smooth g p U hU
  let f := fun y => multilinearThreeCurry n (radialCurvatureOperator g p U y)
  have hf : ContDiff ℝ ∞ f := (multilinearThreeCurry n).contDiff.comp hO
  have H := C04Aux.radialIntegral_iteratedFDeriv_bound f hf m hR
    (fun j => closedBallJetNorm R (radialCurvatureOperator g p U) j)
    (fun j => closedBallJetNorm_nonneg hR _ hO j)
    (fun j hj y hy => (multilinearThreeCurry_iteratedFDeriv_le _ hO j y).trans
      (norm_iteratedFDeriv_le_closedBallJetNorm hR _ hO j hy)) hx
  rw [radialConnection_eq_radialIntegral g p U hU]
  exact H

theorem radialConnection_jetMax_integral_bound (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    closedBallJetNorm R (radialConnection g p U) m ≤
      R * closedBallJetNorm R (radialCurvatureOperator g p U) m +
        (m : ℝ) * closedBallJetNorm R (radialCurvatureOperator g p U) (m - 1) := by
  apply closedBallJetNorm_le hR _ (radialConnection_smooth g p U) m
  intro x hx
  exact radialConnection_iteratedFDeriv_integral_bound g p U hU hR m hx

theorem radialCoframe_iteratedFDeriv_integral_bound (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    {R : ℝ} (hR : 0 ≤ R) (m : ℕ) (hm : 1 ≤ m) {x : ComplexVector n}
    (hx : x ∈ Metric.closedBall (0 : ComplexVector n) R) :
    ‖iteratedFDeriv ℝ m (radialCoframe g p U) x‖ ≤
      R * closedBallJetNorm R (radialConnection g p U) m +
        (m : ℝ) * closedBallJetNorm R (radialConnection g p U) (m - 1) := by
  have hω := radialConnection_smooth g p U
  let f := fun y => (radialConnection g p U y).flip
  have hf : ContDiff ℝ ∞ f :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)).toContinuousLinearEquiv.contDiff.comp hω
  have hjet (j : ℕ) (y : ComplexVector n) :
      ‖iteratedFDeriv ℝ j f y‖ = ‖iteratedFDeriv ℝ j (radialConnection g p U) y‖ :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)).norm_iteratedFDeriv_comp_left _ y j
  have H := C04Aux.radialIntegral_iteratedFDeriv_bound f hf m hR
    (fun j => closedBallJetNorm R (radialConnection g p U) j)
    (fun j => closedBallJetNorm_nonneg hR _ hω j)
    (fun j hj y hy => (hjet j y).le.trans
      (norm_iteratedFDeriv_le_closedBallJetNorm hR _ hω j hy)) hx
  have hI := C04Aux.radialIntegral_contDiff f hf
  have heq : radialCoframe g p U = (fun _ => ContinuousLinearMap.id ℝ (ComplexVector n)) +
      C04Aux.radialIntegral f := radialCoframe_eq_radialIntegral g p U
  rw [heq, iteratedFDeriv_add (contDiff_const : ContDiff ℝ (m : ℕ∞ω)
      (fun _ : ComplexVector n => ContinuousLinearMap.id ℝ (ComplexVector n)))
    (hI.of_le (by simp)), Pi.add_apply, iteratedFDeriv_const_of_ne (by omega : m ≠ 0)]
  simpa only [Pi.zero_apply, zero_add] using H

theorem radialCoframe_jetMax_integral_bound (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (hm : 1 ≤ m) :
    closedBallJetNorm R (radialCoframe g p U) m ≤
      R * closedBallJetNorm R (radialConnection g p U) m +
        (m : ℝ) * closedBallJetNorm R (radialConnection g p U) (m - 1) := by
  apply closedBallJetNorm_le hR _ (radialCoframe_smooth g p U) m
  intro x hx
  exact radialCoframe_iteratedFDeriv_integral_bound g p U hR m hm hx

end Yau.Proofs.C04ChartsAux
