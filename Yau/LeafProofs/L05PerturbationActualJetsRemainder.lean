import Yau.LeafProofs.L05PerturbationActualJetsPeano

open Filter Asymptotics Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L05Aux

/-- A constant uniformly bounded by a positive power at every small radius vanishes. -/
theorem perturb_actual_constant_zero {a E r0 s : ℝ} (hr0 : 0 < r0) (hs : 0 < s)
    (h : ∀ r : ℝ, 0 < r → r ≤ r0 → |a| ≤ E * r ^ s) : a = 0 := by
  have ht : Tendsto (fun r : ℝ => E * r ^ s) (𝓝[>] 0) (𝓝 0) := by
    have hp := ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 (0 : ℝ)) (𝓝 0)).rpow_const
      (Or.inr hs.le)).const_mul E
    simpa [Real.zero_rpow hs.ne'] using hp.mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] 0, |a| ≤ E * r ^ s := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hr0).filter_mono nhdsWithin_le_nhds] with r hr hb
    exact h r hr hb.le
  have hz : |a| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht hbound
  exact abs_nonpos_iff.mp hz

/-- A literal radius estimate of order above two is a genuine squared-norm Peano error. -/
theorem perturb_actual_error_littleO {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {eta E r0 : ℝ} (heta : 0 < eta) (hr0 : 0 < r0)
    (hf0 : f 0 = 0)
    (herr : ∀ r : ℝ, 0 < r → r ≤ r0 → ∀ x : V, ‖x‖ ≤ r → |f x| ≤ E * r ^ (2 + eta)) :
    f =o[𝓝 (0 : V)] (fun x => ‖x‖ ^ 2) := by
  have ht : Tendsto (fun x : V => E * ‖x‖ ^ eta) (𝓝 0) (𝓝 0) := by
    have hn : Tendsto (fun x : V => ‖x‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto (0 : V))
    simpa [Real.zero_rpow heta.ne'] using (hn.rpow_const (Or.inr heta.le)).const_mul E
  apply IsLittleO.of_bound
  intro eps heps
  filter_upwards [Metric.ball_mem_nhds (0 : V) hr0, (tendsto_order.mp ht).2 eps heps] with x hx he
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  by_cases hx0 : x = 0
  · simp [hx0, hf0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxrad : ‖x‖ ≤ r0 := (by simpa using hx : ‖x‖ < r0).le
  calc
    |f x| ≤ E * ‖x‖ ^ (2 + eta) := herr ‖x‖ hxpos hxrad x le_rfl
    _ = (E * ‖x‖ ^ eta) * ‖x‖ ^ 2 := by
      rw [Real.rpow_add hxpos, Real.rpow_two]
      ring
    _ ≤ eps * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right he.le (sq_nonneg _)

end Yau.LeafProofs.L05Aux
