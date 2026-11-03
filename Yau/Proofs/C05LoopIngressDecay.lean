import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Positive power decay controls the precise square-root curve-length coefficient. -/
noncomputable section
open Filter
open scoped Topology
namespace Yau.Proofs.C05LoopIngressAux

theorem tendsto_sqrt_power_decay (a B L : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.sqrt (B * t ^ (-a)) * L) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => B * t ^ (-a)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ha).const_mul B
  have H := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hp
  simpa only [mul_zero, Real.sqrt_zero, zero_mul, Function.comp_apply] using H.mul_const L

theorem eventually_small_sqrt_power_decay (tw : ℕ → ℝ)
    (htw : Tendsto tw atTop atTop) (a B L ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ i in atTop, Real.sqrt (B * tw i ^ (-a)) * L < ε :=
  ((tendsto_sqrt_power_decay a B L ha).comp htw).eventually (gt_mem_nhds hε)

end Yau.Proofs.C05LoopIngressAux
