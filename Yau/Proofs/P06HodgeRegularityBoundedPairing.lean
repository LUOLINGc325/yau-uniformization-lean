import Yau.Proofs.P06HodgeRegularityCalculus
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Normed.Operator.Banach

/-! An actual L¹ test gives a bounded linear pairing on bounded continuous
functions, used to verify the closed graph of chart smoothing jets. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E)

theorem regularityBCF_mul_integrable (φ : E → ℝ) (hφ : Integrable φ ν) (f : E →ᵇ ℝ) :
    Integrable (fun z => f z * φ z) ν := by
  exact hφ.bdd_smul ‖f‖ f.continuous.aestronglyMeasurable
    (Eventually.of_forall fun z => BoundedContinuousFunction.norm_coe_le_norm f z)

def regularityBCFPairingLinear (φ : E → ℝ) (hφ : Integrable φ ν) : (E →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ z, f z * φ z ∂ν
  map_add' f g := by
    change (∫ z, (f z + g z) * φ z ∂ν) = _
    simp only [add_mul]
    exact integral_add (regularityBCF_mul_integrable ν φ hφ f) (regularityBCF_mul_integrable ν φ hφ g)
  map_smul' c f := by
    change (∫ z, (c * f z) * φ z ∂ν) = c * _
    simp_rw [mul_assoc]
    exact integral_const_mul c _

theorem regularityBCFPairingLinear_bound (φ : E → ℝ) (hφ : Integrable φ ν) (f : E →ᵇ ℝ) :
    ‖regularityBCFPairingLinear ν φ hφ f‖ ≤ (∫ z, ‖φ z‖ ∂ν) * ‖f‖ := by
  have hi := regularityBCF_mul_integrable ν φ hφ f
  calc
    _ ≤ ∫ z, ‖f z * φ z‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f‖ * ‖φ z‖ ∂ν := integral_mono hi.norm (hφ.norm.const_mul ‖f‖) (fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm f z) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul,mul_comm]

def regularityBCFPairing (φ : E → ℝ) (hφ : Integrable φ ν) : (E →ᵇ ℝ) →L[ℝ] ℝ :=
  (regularityBCFPairingLinear ν φ hφ).mkContinuous (∫ z, ‖φ z‖ ∂ν)
    (regularityBCFPairingLinear_bound ν φ hφ)

@[simp] theorem regularityBCFPairing_apply (φ : E → ℝ) (hφ : Integrable φ ν) (f : E →ᵇ ℝ) :
    regularityBCFPairing ν φ hφ f = ∫ z, f z * φ z ∂ν := rfl

end Yau.NodeProofs.P06Aux
