import Yau.Proofs.F03ScalarL2

/-! Convergence in the literal scalar distance is genuine L² convergence. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem tendsto_scalarToLp_iff (μ : Measure M.Carrier)
    (fs : ℕ → M.Carrier → ℝ) (f : M.Carrier → ℝ)
    (hfs : ∀ j, ScalarL2 μ (fs j)) (hf : ScalarL2 μ f) :
    Tendsto (fun j => scalarToLp (hfs j)) atTop (𝓝 (scalarToLp hf)) ↔
      Tendsto (fun j => scalarL2DistanceSq μ (fs j) f) atTop (𝓝 0) := by
  have heq : (fun j => scalarL2DistanceSq μ (fs j) f) =
      fun j => ENNReal.ofReal (‖scalarToLp (hfs j) - scalarToLp hf‖ ^ 2) :=
    funext (fun j => scalarL2DistanceSq_eq_norm (hfs j) hf)
  rw [heq]
  constructor
  · intro h
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    have hp : Tendsto (fun j => ‖scalarToLp (hfs j) - scalarToLp hf‖ ^ 2)
        atTop (𝓝 0) := by simpa using hn.pow 2
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hp
  · intro h
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    have hp : Tendsto (fun j => ‖scalarToLp (hfs j) - scalarToLp hf‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
        ENNReal.toReal_zero, Function.comp_def] using ht
    have hs := (Real.continuous_sqrt.tendsto 0).comp hp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def] using hs

end Yau.Proofs.F03Aux
