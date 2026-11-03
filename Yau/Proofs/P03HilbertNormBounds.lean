import Yau.Geometry.Calculus

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The exact extended squared-norm bound is the ordinary closed-ball
condition used for the nested Hilbert constraints. -/
theorem ofReal_norm_sq_le_iff_norm_le_sqrt {H : Type*} [NormedAddCommGroup H]
    (v : H) {B : ℝ} (hB : 0 ≤ B) :
    ENNReal.ofReal (‖v‖ ^ 2) ≤ ENNReal.ofReal B ↔ ‖v‖ ≤ Real.sqrt B := by
  constructor
  · intro h
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hB] at ht
    nlinarith [Real.sq_sqrt hB, Real.sqrt_nonneg B, norm_nonneg v]
  · intro h
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.sq_sqrt hB, Real.sqrt_nonneg B, norm_nonneg v]

end Yau.NodeProofs.P03Aux
