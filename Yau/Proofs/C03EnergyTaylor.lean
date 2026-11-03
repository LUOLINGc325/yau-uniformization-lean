import Mathlib

/-! A genuinely two-parameter quadratic Taylor remainder yields admissibility
on a whole punctured neighborhood, rather than only on its coordinate axes. -/

open Filter Asymptotics
open scoped Topology

namespace Yau.Proofs.C03Aux

theorem eventually_lt_of_negative_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (c : ℝ) (hc : c < 0)
    (hrem : (fun x => f x - f 0 - c * ‖x‖ ^ 2) =o[𝓝 0] (fun x => ‖x‖ ^ 2)) :
    ∀ᶠ x in 𝓝 (0 : E), x ≠ 0 → f x < f 0 := by
  have hε : 0 < -c / 2 := by linarith
  filter_upwards [hrem.def hε] with x hx hne
  have hs : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hx' : |f x - f 0 - c * ‖x‖ ^ 2| ≤ (-c / 2) * ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using hx
  have hu := (abs_le.mp hx').2
  have hneg := mul_neg_of_neg_of_pos hc hs
  nlinarith

theorem distance_lt_radius_of_energy_lt {d E ρ : ℝ}
    (hρ : 0 < ρ) (hE : d ^ 2 ≤ E) (hstrict : E < ρ ^ 2) : d < ρ := by
  nlinarith [sq_nonneg (d - ρ)]

end Yau.Proofs.C03Aux
