import Yau.Proofs.F04BochnerComposition
import Yau.Proofs.F04BochnerL2

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

/-- Strong L2 continuity for an actual continuous time-dependent composition
with linear growth and a genuine L2 inhomogeneous profile. -/
theorem continuous_growth_comp_L2
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (Θ : ℝ × E → F) (hΘ : Continuous Θ) (C : ℝ) (hC : 0 ≤ C)
    (b : ℝ → ℝ) (hb : MemLp b 2 τ)
    (hbound : ∀ t v, ‖Θ (t, v)‖ ≤ C * ‖v‖ + b t)
    (U : ℕ → ℝ → E) (u : ℝ → E) (hU : ∀ j, MemLp (U j) 2 τ) (hu : MemLp u 2 τ)
    (hlim : Tendsto (fun j => ∫ t, ‖U j t - u t‖ ^ 2 ∂τ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ t, ‖Θ (t, U j t) - Θ (t, u t)‖ ^ 2 ∂τ) atTop (𝓝 0) := by
  let G : ℕ → ℝ → ℝ := fun j t => C * ‖U j t‖ + b t
  let g₀ : ℝ → ℝ := fun t => C * ‖u t‖ + b t
  have hG (j : ℕ) : MemLp (G j) 2 τ := ((hU j).norm.const_mul C).add hb
  have hg₀ : MemLp g₀ 2 τ := (hu.norm.const_mul C).add hb
  have hpoint (j : ℕ) (t : ℝ) : ‖G j t - g₀ t‖ ^ 2 ≤ C ^ 2 * ‖U j t - u t‖ ^ 2 := by
    have he : G j t - g₀ t = C * (‖U j t‖ - ‖u t‖) := by dsimp only [G, g₀]; ring
    rw [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg hC, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (by
      simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (U j t) (u t))
  have hGlim : Tendsto (fun j => ∫ t, ‖G j t - g₀ t‖ ^ 2 ∂τ) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _) (fun j => ?_)
      (by simpa only [mul_zero] using hlim.const_mul (C ^ 2))
    have hi := (memLp_two_iff_integrable_sq_norm ((hU j).sub hu).aestronglyMeasurable).mp ((hU j).sub hu)
    have hgi := (memLp_two_iff_integrable_sq_norm ((hG j).sub hg₀).aestronglyMeasurable).mp ((hG j).sub hg₀)
    have hm := integral_mono hgi (hi.const_mul (C ^ 2)) (hpoint j)
    simpa only [Pi.sub_apply, integral_const_mul] using hm
  have hGUI : UnifIntegrable G 2 τ := unifIntegrable_of_tendsto_Lp
    (p := (2 : ℝ≥0∞)) (f := G) (g := g₀) (by norm_num) (by norm_num) hG hg₀
    (bochner_eLpNorm_tendsto_of_integral G g₀ hG hg₀ hGlim)
  have hm (j : ℕ) : AEStronglyMeasurable (fun t => Θ (t, U j t)) τ :=
    hΘ.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk (hU j).aestronglyMeasurable)
  have hmu : AEStronglyMeasurable (fun t => Θ (t, u t)) τ :=
    hΘ.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hu.aestronglyMeasurable)
  have hΘU (j : ℕ) : MemLp (fun t => Θ (t, U j t)) 2 τ :=
    (hG j).of_le (hm j) (ae_of_all τ fun t => (hbound t (U j t)).trans (le_abs_self (G j t)))
  have hΘu : MemLp (fun t => Θ (t, u t)) 2 τ :=
    hg₀.of_le hmu (ae_of_all τ fun t => (hbound t (u t)).trans (le_abs_self (g₀ t)))
  have hΘUI : UnifIntegrable (fun j t => Θ (t, U j t)) 2 τ :=
    unifIntegrable_mono_norm hGUI hm (fun j t => (hbound t (U j t)).trans (le_abs_self (G j t)))
  apply bochner_integral_tendsto_of_eLpNorm (fun j t => Θ (t, U j t)) (fun t => Θ (t, u t)) hΘU hΘu
  have hmeas : TendstoInMeasure τ U atTop u := tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (bochner_eLpNorm_tendsto_of_integral U u hU hu hlim)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hsub : TendstoInMeasure τ (fun j => U (ns j)) atTop u :=
    fun ε hε => (hmeas ε hε).comp hns
  obtain ⟨ms, _, hms⟩ := hsub.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hp : ∀ᵐ t ∂τ, Tendsto (fun j => Θ (t, U (ns (ms j)) t)) atTop (𝓝 (Θ (t, u t))) := by
    filter_upwards [hms] with t ht
    exact ((hΘ.comp (continuous_const.prodMk continuous_id)).tendsto (u t)).comp ht
  have hz := tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun j => hm (ns (ms j))) hΘu (hΘUI.comp (fun j => ns (ms j))) hp
  simpa only [Function.comp_def, Pi.sub_def] using hz

end Yau.F04Proof
