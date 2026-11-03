import Yau.Proofs.E01QuadraticFiber

/-! Exact scalar homogeneity of the actual covector norm and admissible cotangent discs. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem covectorCoords_complex_smul (x y : M.Carrier) (c : ℂ) (ξ : Covector n) :
    covectorCoords x y (c • ξ) = c • covectorCoords x y ξ := by
  ext i
  rfl

theorem dualNormMat_complex_smul (H : Herm n) (c : ℂ) (η : ComplexVector n) :
    dualNormMat H (c • η) = ‖c‖ ^ 2 * dualNormMat H η :=
  ellipsoidQuadratic_complex_smul (H⁻¹)ᵀ c η

theorem dualNorm_complex_smul (h : HermitianField M) (y : M.Carrier)
    (c : ℂ) (ξ : Covector n) :
    dualNorm h y (c • ξ) = ‖c‖ ^ 2 * dualNorm h y ξ := by
  unfold dualNorm
  rw [covectorCoords_complex_smul, dualNormMat_complex_smul]

theorem original_cotangentDisc_const_smul {f : ℂ → M.Carrier} {ξ : ℂ → Covector n}
    (hd : IsCotangentDisc f ξ) (c : ℂ) :
    IsCotangentDisc f (fun ζ => c • ξ ζ) := by
  refine ⟨hd.1, fun ζ₀ hζ₀ => ?_⟩
  simpa only [covectorCoords_complex_smul] using (hd.2 ζ₀ hζ₀).const_smul c

theorem original_circleAverage_const_mul (c : ℝ) (f : ℝ → ℝ) :
    circleAverage (fun θ => c * f θ) = c * circleAverage f := by
  unfold circleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

end Yau.NodeProofs.E01Aux
