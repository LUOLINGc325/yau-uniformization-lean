import Yau.Proofs.F04SmoothPositiveLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {X : Type*} [MeasurableSpace X]

def smoothPositiveL2 (μ : Measure X) (δ : ℝ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (smoothPositive_lipschitz δ).compLp (smoothPositive_zero δ) f

theorem smoothPositiveL2_coe (μ : Measure X) (δ : ℝ) (f : Lp ℝ 2 μ) :
    (smoothPositiveL2 μ δ f : X → ℝ) =ᵐ[μ] (fun x => smoothPositive δ (f x)) :=
  (smoothPositive_lipschitz δ).coeFn_compLp (smoothPositive_zero δ) f

/-- The scalar approximations converge in the actual L2 pivot without a
finite-volume hypothesis or an unsupported full-sequence AE limit. -/
theorem smoothPositiveL2_tendsto (μ : Measure X) (f : Lp ℝ 2 μ)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => smoothPositiveL2 μ (δ j) f) atTop (𝓝 (Lp.posPart f)) := by
  let F : ℕ → X → ℝ := fun j x => (smoothPositive (δ j) (f x) - max (f x) 0) ^ 2
  have hm (j : ℕ) : AEStronglyMeasurable (F j) μ :=
    (((smoothPositive_contDiff (δ j)).continuous.comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable).sub
      (Lp.lipschitzWith_pos_part.continuous.comp_aestronglyMeasurable
        (Lp.memLp f).aestronglyMeasurable)).pow 2
  have hd (j : ℕ) : ∀ᵐ x ∂μ, ‖F j x‖ ≤ (f x) ^ 2 := by
    apply ae_of_all
    intro x
    have hp : max (f x) 0 ≤ |f x| := max_le (le_abs_self _) (abs_nonneg _)
    have he := (smoothPositive_error_le_pos (hδ j) (f x)).trans hp
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr he
    simpa only [F, Real.norm_eq_abs, abs_pow, sq_abs] using hs
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro x
    simpa only [F, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      ((smoothPositive_tendsto (f x) δ hδ hlim).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => max (f x) 0) atTop (𝓝 (max (f x) 0)))).pow 2
  have hi := tendsto_integral_of_dominated_convergence (fun x => (f x) ^ 2)
    hm (Lp.memLp f).integrable_sq hd hl
  have he (j : ℕ) : ‖smoothPositiveL2 μ (δ j) f - Lp.posPart f‖ ^ 2 = ∫ x, F j x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (smoothPositiveL2 μ (δ j) f) (Lp.posPart f),
      smoothPositiveL2_coe μ (δ j) f, Lp.coeFn_posPart f] with x hs hb hp
    simp only [hs, Pi.sub_apply, hb, hp, F, RCLike.inner_apply, conj_trivial, pow_two]
  have hs : Tendsto (fun j => ‖smoothPositiveL2 μ (δ j) f - Lp.posPart f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [he, integral_zero] using hi
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end Yau.F04Proof
