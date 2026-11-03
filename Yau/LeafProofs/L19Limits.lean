import Yau.LeafProofs.L19

/-! Removing the spatial and temporal localizations in the Li--Yau
argument. All constants in these elementary limits remain explicit. -/

noncomputable section

open Filter
open scoped Topology

namespace Yau.LeafProofs.L19Aux

/-- An error constant may depend on all data other than the outer radius.
No sign assumption on that constant is needed when the radius diverges. -/
theorem liYau_remove_radius {A D E : ℝ}
    (h : ∀ R : ℝ, 0 < R → A ≤ D + E / R ^ 2) : A ≤ D := by
  have hlim : Tendsto (fun R : ℝ => D + E / R ^ 2) atTop (𝓝 D) := by
    have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hD : Tendsto (fun _ : ℝ => D) atTop (𝓝 D) := tendsto_const_nhds
    have hE : Tendsto (fun _ : ℝ => E) atTop (𝓝 E) := tendsto_const_nhds
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] using hD.add (hE.mul (hi.pow 2))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact h R hR

/-- The proof may start at every strictly positive time. Letting that
starting time tend to zero uses no regularity assertion at time zero. -/
theorem liYau_remove_initial_time {A D t : ℝ} (ht : 0 < t)
    (h : ∀ τ : ℝ, 0 < τ → τ < t → A ≤ D / (t - τ)) : A ≤ D / t := by
  have hc : ContinuousAt (fun τ : ℝ => D / (t - τ)) 0 := by
    apply ContinuousAt.div continuousAt_const (continuousAt_const.sub continuousAt_id)
    simpa using ht.ne'
  have hlim : Tendsto (fun τ : ℝ => D / (t - τ)) (𝓝[>] 0) (𝓝 (D / t)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with τ hτ hτt
  exact h τ hτ hτt

/-- The strict auxiliary coefficient tends to one while the time
derivative remains unrestricted in sign. -/
theorem liYau_remove_alpha {A B D : ℝ}
    (h : ∀ α : ℝ, 1 < α → A - α * B ≤ D * α ^ 2) : A - B ≤ D := by
  have hleft : ContinuousAt (fun α : ℝ => A - α * B) 1 := by fun_prop
  have hright : ContinuousAt (fun α : ℝ => D * α ^ 2) 1 := by fun_prop
  have hL : Tendsto (fun α : ℝ => A - α * B) (𝓝[>] 1) (𝓝 (A - B)) := by
    simpa using hleft.tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun α : ℝ => D * α ^ 2) (𝓝[>] 1) (𝓝 D) := by
    simpa using hright.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact h α hα

/-- The complete order of the localization limits. In particular the
radius error may blow up as the strict coefficient tends to one or the
starting time tends to zero, since those parameters are fixed first. -/
theorem liYau_remove_localizations {A B d t : ℝ} (ht : 0 < t)
    (h : ∀ α : ℝ, 1 < α → ∀ τ : ℝ, 0 < τ → τ < t →
      ∃ E : ℝ, ∀ R : ℝ, 0 < R →
        A - α * B ≤ d * α ^ 2 / (t - τ) + E / R ^ 2) :
    A - B ≤ d / t := by
  apply liYau_remove_alpha
  intro α hα
  have htime : A - α * B ≤ (d * α ^ 2) / t := by
    apply liYau_remove_initial_time ht
    intro τ hτ hτt
    obtain ⟨E, hE⟩ := h α hα τ hτ hτt
    exact liYau_remove_radius hE
  convert htime using 1
  ring

end Yau.LeafProofs.L19Aux
