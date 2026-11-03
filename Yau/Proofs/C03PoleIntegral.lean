import Mathlib

/-! The integral at the critical logarithmic pole tends to zero on shrinking
punctured balls. This retains the small-o information needed for the first jet. -/

open MeasureTheory Filter Set
open scoped Topology

namespace Yau.Proofs.C03Aux

theorem punctured_ball_integral_tendsto_zero
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (f : E → ℝ) (o : E) (r : ℕ → ℝ)
    (hr : Antitone r) (hr0 : Tendsto r atTop (𝓝 0))
    (hf : IntegrableOn f (Metric.ball o (r 0) \ {o}) μ) :
    Tendsto (fun j => ∫ x in Metric.ball o (r j) \ {o}, f x ∂μ) atTop (𝓝 0) := by
  have hsets : Antitone (fun j => Metric.ball o (r j) \ {o}) := by
    intro i j hij x hx
    exact ⟨Metric.ball_subset_ball (hr hij) hx.1, hx.2⟩
  have hempty : (⋂ j, Metric.ball o (r j) \ {o}) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxo : x ≠ o := by
      simpa only [mem_singleton_iff] using (mem_iInter.mp hx 0).2
    have hdist : 0 < dist x o := dist_pos.mpr hxo
    have hevent : ∀ᶠ j in atTop, r j < dist x o :=
      hr0.eventually (gt_mem_nhds hdist)
    obtain ⟨j, hj⟩ := hevent.exists
    have hball := (mem_iInter.mp hx j).1
    rw [Metric.mem_ball] at hball
    exact (lt_asymm hball hj)
  have H := tendsto_setIntegral_of_antitone
    (fun j => measurableSet_ball.diff (measurableSet_singleton o)) hsets ⟨0, hf⟩
  simpa [hempty] using H

end Yau.Proofs.C03Aux
