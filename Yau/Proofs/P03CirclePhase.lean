import Yau.Proofs.P03Convolution
import Yau.Proofs.P03Measure

open scoped Topology Convolution
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- Multiplication by a unit complex phase is an actual real linear isometry
of the Euclidean model, rather than a supplied change-of-variables promise. -/
def phaseIsometry (c : ℂ) (hc : ‖c‖ = 1) :
    ComplexVector n ≃ₗᵢ[ℝ] ComplexVector n where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by
    have hc0 : c ≠ 0 := by intro h; simpa [h] using hc
    change c⁻¹ • (c • x) = x
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  right_inv x := by
    have hc0 : c ≠ 0 := by intro h; simpa [h] using hc
    change c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  map_add' x y := smul_add c x y
  map_smul' r x := smul_comm c r x
  norm_map' x := by
    change ‖c • x‖ = ‖x‖
    rw [norm_smul, hc, one_mul]

theorem phaseIsometry_measurePreserving (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (phaseIsometry (n := n) c hc) :=
  (phaseIsometry c hc).measurePreserving

theorem integral_phase_smul (c : ℂ) (hc : ‖c‖ = 1) (f : ComplexVector n → ℂ) :
    (∫ y : ComplexVector n, f (c • y)) = ∫ y : ComplexVector n, f y := by
  exact (phaseIsometry_measurePreserving c hc).integral_comp
    (phaseIsometry c hc).toHomeomorph.measurableEmbedding f

/-- The exact phase change of variables used before averaging over a scalar
circle. Integrability for the later Fubini step is proved separately. -/
theorem smoothBy_phase_change (k : ComplexVector n → ℝ) (h : ComplexVector n → ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (hkinv : ∀ y, k (c • y) = k y) (x : ComplexVector n) :
    smoothBy k h x = ∫ y : ComplexVector n, k y • h (x - c • y) := by
  have he := integral_phase_smul c hc (fun y => k y • h (x - y))
  simpa only [smoothBy, convolution_def, ContinuousLinearMap.lsmul_apply, hkinv] using he.symm

end Yau.NodeProofs.P03Aux
