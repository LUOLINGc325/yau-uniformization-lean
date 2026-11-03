import Yau.Proofs.F04LpParameterContinuity

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

/-- Actual pointwise one-sided derivatives and an L2 slope majorant give
the actual one-sided derivative in L2. No derivative of a representative is
postulated at the level of the quotient. -/
theorem hasDerivWithinAt_toLp_of_dominated_slopes
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℝ → X → ℝ) (hf : ∀ s, MemLp (f s) 2 μ)
    (d : X → ℝ) (hd : MemLp d 2 μ) (I : Set ℝ) (t : ℝ)
    (hder : ∀ᵐ x ∂μ, HasDerivWithinAt (fun s => f s x) (d x) I t)
    (b : X → ℝ) (hb : MemLp b 2 μ)
    (hbound : ∀ᶠ s in 𝓝[I \ {t}] t, ∀ᵐ x ∂μ,
      ‖slope (fun r => f r x) t s‖ ≤ b x) :
    HasDerivWithinAt (fun s => (hf s).toLp (f s)) (hd.toLp d) I t := by
  let S := fun s x => slope (fun r => f r x) t s
  have hS (s : ℝ) : MemLp (S s) 2 μ := by
    simpa only [S, slope_def_module, Pi.smul_def, Pi.sub_def] using
      ((hf s).sub (hf t)).const_smul (s - t)⁻¹
  have hSb : ∀ᶠ s in 𝓝[I \ {t}] t, ∀ᵐ x ∂μ, ‖S s x - d x‖ ≤ ‖b x‖ + ‖d x‖ := by
    filter_upwards [hbound] with s hs
    filter_upwards [hs] with x hx
    exact (norm_sub_le _ _).trans (add_le_add
      (hx.trans (le_abs_self _)) le_rfl)
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun s => S s x) (𝓝[I \ {t}] t) (𝓝 (d x)) := by
    filter_upwards [hder] with x hx
    exact hasDerivWithinAt_iff_tendsto_slope.mp hx
  have hlim := toLp_tendsto_of_dominated_differences μ S hS d hd
    (fun x => ‖b x‖ + ‖d x‖) (hb.norm.add hd.norm) hSb hpoint
  have hclass (s : ℝ) : (hS s).toLp (S s) = slope (fun r => (hf r).toLp (f r)) t s := by
    apply Lp.ext
    filter_upwards [(hS s).coeFn_toLp,
      Lp.coeFn_smul (s - t)⁻¹ ((hf s).toLp (f s) - (hf t).toLp (f t)),
      Lp.coeFn_sub ((hf s).toLp (f s)) ((hf t).toLp (f t)),
      (hf s).coeFn_toLp, (hf t).coeFn_toLp] with x hSx hsm hsub hfs hft
    change (hS s).toLp (S s) x = ((s - t)⁻¹ • ((hf s).toLp (f s) - (hf t).toLp (f t))) x
    rw [hSx, hsm]
    simp only [Pi.smul_apply]
    rw [hsub]
    simp only [S, slope_def_module, Pi.smul_apply, Pi.sub_apply, hfs, hft]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  simpa only [hclass] using hlim

end Yau.F04Proof
