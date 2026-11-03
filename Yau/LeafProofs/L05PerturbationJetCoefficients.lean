import Yau.LeafProofs.L05PerturbationJetGeometry
import Yau.LeafProofs.L05PerturbationPolynomialExtraction

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_taylor_coefficient_bounds {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) {z w : Point n} (hz : z∈Q) (hw : w∈Q)
    {r B T : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (x : Space n)
    (hTaylor : ∀ p∈perturbClosed x r T,
      |perturbTaylor Q u z p-perturbTaylor Q u w p| ≤ B) :
    |timeD Q u z-timeD Q u w| ≤ 2*B/r^2 ∧
      ‖spatialDD u z-spatialDD u w‖ ≤ 4*B/r^2 := by
  have hPoly : ∀ p∈perturbClosed x r T,
      |perturbPolynomial (perturbTaylorConstant Q u z) (perturbTaylorLinear u z)
          (hessian u z) (timeD Q u z) p-
        perturbPolynomial (perturbTaylorConstant Q u w) (perturbTaylorLinear u w)
          (hessian u w) (timeD Q u w) p| ≤ B := by
    intro p hp
    simpa only [← perturb_taylor_global_polynomial hu hz,← perturb_taylor_global_polynomial hu hw]
      using hTaylor p hp
  obtain ⟨hTime,hSpace⟩ := perturb_polynomial_coefficients hr hB x
    (perturbTaylorConstant Q u z) (perturbTaylorConstant Q u w) (timeD Q u z) (timeD Q u w)
    (perturbTaylorLinear u z) (perturbTaylorLinear u w) (hessian u z) (hessian u w) hPoly
  refine ⟨hTime,?_⟩
  simpa only [perturb_polynomial_spatialDD,← perturb_spatialDD_eq_bilinear hu hz,
    ← perturb_spatialDD_eq_bilinear hu hw] using hSpace

end Yau.LeafProofs.L05Aux
