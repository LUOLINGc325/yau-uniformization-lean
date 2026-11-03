import spec.CHAIN.CONTRACTS

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smul_closedBall_two_mem {r ρ : ℝ} (hr : 0 < r) (hρ : 2 * r < ρ)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) 2) : r • x ∈ Metric.ball (0 : E) ρ := by
  have hxN : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left hxN hr.le).trans_lt (by linarith)

theorem isOpen_smul_preimage_ball (r ρ : ℝ) :
    IsOpen ((fun x : E => r • x) ⁻¹' Metric.ball (0 : E) ρ) :=
  Metric.isOpen_ball.preimage (continuous_const_smul r)

theorem contDiffOn_comp_smul_preimage {O : Set E} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f O) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun x => f (r • x)) ((fun x : E => r • x) ⁻¹' O) := by
  have hD : ContDiff ℝ ∞ (fun x : E => r • x) := by fun_prop
  exact hf.comp hD.contDiffOn (fun _ hx => hx)

end Yau.Blueprint.C02Proof
