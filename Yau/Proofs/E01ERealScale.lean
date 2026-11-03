import Mathlib.Topology.Instances.EReal.Lemmas

/-! Positive finite scaling is an actual complete-order automorphism of EReal. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

def erealPositiveScale (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun x := (c : EReal) * x
  invFun x := (c⁻¹ : ℝ) * x
  left_inv x := by
    change ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * x) = x
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  right_inv x := by
    change (c : EReal) * (((c⁻¹ : ℝ) : EReal) * x) = x
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  map_rel_iff' := by
    intro x y
    change (c : EReal) * x ≤ (c : EReal) * y ↔ x ≤ y
    constructor
    · intro h
      have hh := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr (inv_nonneg.mpr hc.le))
      simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul] using hh
    · exact fun h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le)

theorem erealPositiveScale_apply (c : ℝ) (hc : 0 < c) (x : EReal) :
    erealPositiveScale c hc x = (c : EReal) * x := rfl

theorem erealPositiveScale_iInf (c : ℝ) (hc : 0 < c) {ι : Sort*} (f : ι → EReal) :
    (c : EReal) * (⨅ i, f i) = ⨅ i, (c : EReal) * f i :=
  (erealPositiveScale c hc).map_iInf f

end Yau.NodeProofs.E01Aux
