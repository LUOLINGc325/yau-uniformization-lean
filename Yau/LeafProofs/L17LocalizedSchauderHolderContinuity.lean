import Yau.LeafProofs.L17LocalizedSchauderDistance

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]

/-- Continuity follows from an actual positive-power difference estimate and
a continuous vanishing distance function. -/
theorem continuous_of_power_difference {f : X → F} {d : X → X → ℝ} {gamma C : ℝ}
    (hγ : 0 < gamma) (hDist : ∀ x, Continuous (fun y => d y x))
    (hZero : ∀ x, d x x = 0) (hNonneg : ∀ x y, 0 ≤ d x y)
    (hDiff : ∀ x y, ‖f x-f y‖ ≤ C*(d x y)^gamma) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hPower : ContinuousAt (fun y => C*(d y x)^gamma) x :=
    continuousAt_const.mul ((hDist x).continuousAt.rpow_const (Or.inr hγ.le))
  have hLimit : Tendsto (fun y => C*(d y x)^gamma) (𝓝 x) (𝓝 0) := by
    simpa only [hZero x,Real.zero_rpow hγ.ne',mul_zero] using hPower.tendsto
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => hDiff y x) hLimit

end Yau.LeafProofs.L17LocalizedSchauderAux
