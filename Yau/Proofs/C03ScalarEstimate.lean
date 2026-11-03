import Yau.Proofs.C03ScalarEstimateL2
import Yau.Proofs.C03ScalarRecoveryJet

/-! One derivative constant is chosen before all seed, solution, weight and bound data. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace Yau.Proofs.C03Aux.ScalarEstimate
open Yau
variable {n : ℕ}

theorem exists_weighted_derivative_bound (R : ℝ) (hR : 0 < R) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f h : ComplexVector n → ℂ) (φ : ComplexVector n → ℝ)
      (M S B : ℝ), Continuous f → Differentiable ℂ h → Continuous φ →
      0 ≤ S → 0 ≤ B →
      (∀ z ∈ closedBall (0 : ComplexVector n) R, ‖f z‖ ≤ S) →
      (∀ z ∈ closedBall (0 : ComplexVector n) R, φ z ≤ M) →
      (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-φ z))
        ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B →
      ‖fderiv ℂ h 0‖ ≤ D * Real.sqrt
        (2 * S ^ 2 * (volume : Measure (ComplexVector n)).real (closedBall 0 R) +
          2 * Real.exp M * B) := by
  obtain ⟨D, hD, hjet⟩ := ScalarRecovery.exists_derivative_L2_bound (n := n) R hR
  refine ⟨D, hD, ?_⟩
  intro f h φ M S B hf hh hφ hS hB hfS hφM hb
  have hL2 := local_L2_le f h φ R M S B hf hh.continuous hφ hS hB hfS hφM hb
  exact (hjet h hh).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL2) hD.le)

end Yau.Proofs.C03Aux.ScalarEstimate
