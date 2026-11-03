import Yau.Proofs.P06PositiveResolvent

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : H →ₗ.[ℝ] H) (hd : Dense (T.domain : Set H)) (hself : T.adjoint = T)
  (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u))

/-- The normalized implicit Euler step of the original unbounded operator:
the resolvent at h⁻¹ applied to h⁻¹ times the actual input. -/
def normalizedResolvent (h : ℝ) (hh : 0 < h) : H →L[ℝ] H :=
  (positiveResolvent T hd hself hp h⁻¹ (inv_pos.mpr hh)).comp (h⁻¹ • (1 : H →L[ℝ] H))

theorem normalizedResolvent_graph (h : ℝ) (hh : 0 < h) (f : H) :
    (normalizedResolvent T hd hself hp h hh f,
      h⁻¹ • (f - normalizedResolvent T hd hself hp h hh f)) ∈ T.graph := by
  simpa only [normalizedResolvent, ContinuousLinearMap.comp_apply,
    smul_apply, one_apply_eq_self, smul_sub] using
    positiveResolvent_graph T hd hself hp h⁻¹ (inv_pos.mpr hh) (h⁻¹ • f)

theorem normalizedResolvent_norm_le (h : ℝ) (hh : 0 < h) (f : H) :
    ‖normalizedResolvent T hd hself hp h hh f‖ ≤ ‖f‖ := by
  have hb := positiveResolvent_bound T hd hself hp h⁻¹ (inv_pos.mpr hh) (h⁻¹ • f)
  simpa only [normalizedResolvent, ContinuousLinearMap.comp_apply,
    smul_apply, one_apply_eq_self,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh), inv_inv,
    ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] using hb

theorem normalizedResolvent_euler_relation (h : ℝ) (hh : 0 < h) (f : H) :
    normalizedResolvent T hd hself hp h hh
      (h • f + (1 - h) • positiveResolvent T hd hself hp 1 zero_lt_one f) =
        positiveResolvent T hd hself hp 1 zero_lt_one f := by
  let R := positiveResolvent T hd hself hp 1 zero_lt_one
  have hR : (R f, f - R f) ∈ T.graph := by
    simpa only [R, one_smul] using positiveResolvent_graph T hd hself hp 1 zero_lt_one f
  apply positiveShift_graph_injective T hp (inv_pos.mpr hh)
    (normalizedResolvent_graph T hd hself hp h hh (h • f + (1 - h) • R f)) hR
  rw [smul_sub, sub_add_cancel, smul_add, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [smul_smul]
  have he : h⁻¹ * (1 - h) = h⁻¹ - 1 := by
    rw [mul_sub, mul_one, inv_mul_cancel₀ hh.ne']
  rw [he]
  module

theorem normalizedResolvent_euler_operator_relation (h : ℝ) (hh : 0 < h) :
    normalizedResolvent T hd hself hp h hh *
      (h • (1 : H →L[ℝ] H) + (1 - h) • positiveResolvent T hd hself hp 1 zero_lt_one) =
        positiveResolvent T hd hself hp 1 zero_lt_one := by
  apply ContinuousLinearMap.ext
  intro f
  exact normalizedResolvent_euler_relation T hd hself hp h hh f

end Yau.NodeProofs.P06Aux
