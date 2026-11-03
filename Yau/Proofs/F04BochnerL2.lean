import Yau.Proofs.F04PositiveEnergyHilbert

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure X}

theorem bochner_l2_norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem bochner_toLp_sub_norm_sq (u v : X → E) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ‖hu.toLp u - hv.toLp v‖ ^ 2 = ∫ x, ‖u x - v x‖ ^ 2 ∂μ := by
  rw [bochner_l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hu.toLp u) (hv.toLp v), hu.coeFn_toLp, hv.coeFn_toLp]
    with x hs hx hy
  simp only [hs, Pi.sub_apply, hx, hy]

theorem bochner_toLp_tendsto_of_integral (U : ℕ → X → E) (u : X → E)
    (hU : ∀ j, MemLp (U j) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun j => ∫ x, ‖U j x - u x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => (hU j).toLp (U j)) atTop (𝓝 (hu.toLp u)) := by
  have hs : Tendsto (fun j => ‖(hU j).toLp (U j) - hu.toLp u‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [bochner_toLp_sub_norm_sq] using hlim
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

theorem bochner_integral_tendsto_of_toLp (U : ℕ → X → E) (u : X → E)
    (hU : ∀ j, MemLp (U j) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun j => (hU j).toLp (U j)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun j => ∫ x, ‖U j x - u x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hs := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).pow 2
  simpa only [bochner_toLp_sub_norm_sq, zero_pow (by norm_num : 2 ≠ 0)] using hs

theorem bochner_eLpNorm_tendsto_of_integral (U : ℕ → X → E) (u : X → E)
    (hU : ∀ j, MemLp (U j) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun j => ∫ x, ‖U j x - u x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (U j - u) 2 μ) atTop (𝓝 0) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' U hU u hu).mp
    (bochner_toLp_tendsto_of_integral U u hU hu hlim)

theorem bochner_integral_tendsto_of_eLpNorm (U : ℕ → X → E) (u : X → E)
    (hU : ∀ j, MemLp (U j) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun j => eLpNorm (U j - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖U j x - u x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  bochner_integral_tendsto_of_toLp U u hU hu
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' U hU u hu).mpr hlim)

end Yau.F04Proof
