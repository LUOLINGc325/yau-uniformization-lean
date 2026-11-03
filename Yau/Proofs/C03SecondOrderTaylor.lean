import Yau.Proofs.C03EnergyTaylor

/-! Genuine C² regularity and vanishing jets give the full multivariable
quadratic little-o remainder used by the energy argument. -/

noncomputable section
open Filter Asymptotics Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_order_littleO_of_zero_jets (f : E → G)
    (hf : ContDiffAt ℝ 2 f 0) (hfirst : fderiv ℝ f 0 = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) 0 = 0) :
    (fun x => f x - f 0) =o[𝓝 0] (fun x => ‖x‖ ^ 2) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (by norm_num)).differentiableAt_one
  have hsmall : (fderiv ℝ f) =o[𝓝 0] (fun x : E => ‖x‖) := by
    have H := hD.hasFDerivAt.isLittleO
    rw [hsecond] at H
    simpa only [hfirst, sub_zero, ContinuousLinearMap.zero_apply] using H.norm_right
  have hnear : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x := by
    filter_upwards [(hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)] with x hx
    exact hx.differentiableAt_one
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have H := (convex_ball (0 : E) ε).isLittleO_pow_succ
    (Metric.mem_ball_self hε)
    (fun x hx => (hball hx).hasFDerivAt.hasFDerivWithinAt)
    (n := 1) (by simpa only [sub_zero, pow_one] using hsmall.mono nhdsWithin_le_nhds)
  simpa only [sub_zero, pow_one, nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : E) hε)] using H

end Yau.Proofs.C03Aux
