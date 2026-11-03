import Yau.Blueprint.Nodes

open scoped Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

/-- Multiplication by a strictly positive finite real on the extended reals. -/
def positiveScaleIso (a : ℝ) (ha : 0 < a) : EReal ≃o EReal where
  toFun x := (a : EReal) * x
  invFun x := ((a⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    cases x <;> simp only [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_top_of_pos ha,
      EReal.coe_mul_bot_of_pos (inv_pos.mpr ha), EReal.coe_mul_top_of_pos (inv_pos.mpr ha),
      ← EReal.coe_mul, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  right_inv x := by
    cases x <;> simp only [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_top_of_pos ha,
      EReal.coe_mul_bot_of_pos (inv_pos.mpr ha), EReal.coe_mul_top_of_pos (inv_pos.mpr ha),
      ← EReal.coe_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;>
      simp [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_top_of_pos ha,
        ← EReal.coe_mul, EReal.coe_le_coe_iff, mul_le_mul_iff_right₀ ha]

theorem positive_scale_le_real_iff {a : ℝ} (ha : 0 < a) (v : EReal) (b : ℝ) :
    (a : EReal) * v ≤ (b : EReal) ↔ v ≤ ((b / a : ℝ) : EReal) := by
  cases v <;> simp [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_top_of_pos ha,
    ← EReal.coe_mul, EReal.coe_le_coe_iff, le_div_iff₀ ha, mul_comm]

/-- Positive rescaling preserves the original EReal psh predicate, including
its value minus infinity. -/
theorem isPshOn_positive_scale {n : ℕ} {Ω : Set (ComplexVector n)}
    {u : ComplexVector n → EReal} (hu : IsPshOn u Ω) {a : ℝ} (ha : 0 < a) :
    IsPshOn (fun z => (a : EReal) * u z) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have h := (positiveScaleIso a ha).strictMono (hu.1 z hz)
    change (a : EReal) * u z < (a : EReal) * ⊤ at h
    simpa only [EReal.coe_mul_top_of_pos ha] using h
  · exact (positiveScaleIso a ha).continuous.comp_upperSemicontinuousOn hu.2.1
      (positiveScaleIso a ha).monotone
  · intro z w hdisc φ hφ hmajor
    apply (positive_scale_le_real_iff ha _ _).mpr
    have hmean := hu.2.2 z w hdisc (fun θ => φ θ / a) (hφ.div_const a)
      (fun θ => (positive_scale_le_real_iff ha _ _).mp (hmajor θ))
    have havg : circleAverage (fun θ => φ θ / a) = circleAverage φ / a := by
      unfold circleAverage
      simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const]
      ring
    simpa only [havg] using hmean

end Yau.Proofs.C07Aux
