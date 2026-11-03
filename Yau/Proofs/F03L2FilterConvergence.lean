import Yau.Proofs.F03ScalarL2

/-! Exact squared-distance convergence for arbitrary filters, including the positive initial face. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem tendsto_ofReal_norm_sq_iff {ι E : Type*} [SeminormedAddCommGroup E]
    (l : Filter ι) (u : ι → E) :
    Tendsto (fun i => ENNReal.ofReal (‖u i‖ ^ 2)) l (𝓝 0) ↔ Tendsto u l (𝓝 0) := by
  constructor
  · intro h
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    have hp : Tendsto (fun i => ‖u i‖ ^ 2) l (𝓝 (0 : ℝ)) := by
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero,
        Function.comp_def] using ht
    have hs := (Real.continuous_sqrt.tendsto 0).comp hp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def,
      sub_zero] using hs
  · intro h
    have hp : Tendsto (fun i => ‖u i‖ ^ 2) l (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero, zero_pow (by omega : 2 ≠ 0)] using h.norm.pow 2
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hp

variable {n : ℕ} {M : ComplexManifold n}

theorem tendsto_scalarToLp_filter_iff {ι : Type*} (l : Filter ι)
    (μ : Measure M.Carrier) (fs : ι → M.Carrier → ℝ) (f : M.Carrier → ℝ)
    (hfs : ∀ i, ScalarL2 μ (fs i)) (hf : ScalarL2 μ f) :
    Tendsto (fun i => scalarToLp (hfs i)) l (𝓝 (scalarToLp hf)) ↔
      Tendsto (fun i => scalarL2DistanceSq μ (fs i) f) l (𝓝 0) := by
  have heq : (fun i => scalarL2DistanceSq μ (fs i) f) =
      fun i => ENNReal.ofReal (‖scalarToLp (hfs i) - scalarToLp hf‖ ^ 2) :=
    funext (fun i => scalarL2DistanceSq_eq_norm (hfs i) hf)
  rw [heq, tendsto_ofReal_norm_sq_iff]
  exact tendsto_sub_nhds_zero_iff.symm

end Yau.Proofs.F03Aux
