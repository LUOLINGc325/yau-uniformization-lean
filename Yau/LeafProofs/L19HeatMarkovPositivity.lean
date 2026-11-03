import Yau.LeafProofs.L19HeatMarkov

/-! Positivity on all actual L² inputs and zero-endpoint bounded estimates. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Nonnegative L² functions are limits of bounded nonnegative clips, on
arbitrary measure spaces. No integrability of a constant is required. -/
theorem normalClipL2_tendsto_of_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Tendsto (fun k : ℕ => normalClipL2 μ ((k : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) := by
  let K : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hK (k : ℕ) : 0 ≤ K k := by dsimp [K]; positivity
  let F : ℕ → X → ℝ := fun k x => (normalClip (K k) (f x) - f x) ^ 2
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) μ :=
    (((normalClip_lipschitz (K k)).continuous.comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable).sub (Lp.memLp f).aestronglyMeasurable).pow 2
  have hdom (k : ℕ) : ∀ᵐ x ∂μ, ‖F k x‖ ≤ 4 * f x ^ 2 := by
    apply ae_of_all
    intro x
    have hc := normalClip_abs_le (hK k) (f x)
    have hdiff : |normalClip (K k) (f x) - f x| ≤ 2 * |f x| :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdiff
    simp only [mul_pow, sq_abs] at hs
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hs
    simpa [F, Real.norm_eq_abs] using hs
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hf] with x hx
    apply tendsto_nhds_of_eventually_eq
    have ht : Tendsto K atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (f x))] with k hk
    simp only [F, normalClip_eq_self ⟨hx, hk⟩, sub_self, zero_pow (by decide : 2 ≠ 0)]
  have ht := tendsto_integral_of_dominated_convergence (fun x => 4 * f x ^ 2)
    hmeas ((Lp.memLp f).integrable_sq.const_mul 4) hdom hlim
  have hn (k : ℕ) : ‖normalClipL2 μ (K k) (hK k) f - f‖ ^ 2 = ∫ x, F k x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (normalClipL2 μ (K k) (hK k) f) f,
      normalClipL2_coe μ (K k) (hK k) f] with x hsub hc
    simp only [hsub, Pi.sub_apply, hc, F, RCLike.inner_apply, conj_trivial, pow_two]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have ht' : Tendsto (fun k => ‖normalClipL2 μ (K k) (hK k) f - f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by simpa only [hn, integral_zero] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, K] using hs

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual heat is positive on every nonnegative L² input. -/
theorem scalarHeatFamily_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∀ᵐ x ∂μ, 0 ≤ scalarHeatFamily g μ hμ t f x := by
  have hlim := (scalarHeatFamily g μ hμ t).continuous.continuousAt.tendsto.comp
    (normalClipL2_tendsto_of_nonneg μ f hf)
  have hbound (k : ℕ) : 0 ≤ scalarHeatFamily g μ hμ t
      (normalClipL2 μ ((k : ℝ) + 1) (by positivity) f) := by
    apply (Lp.coeFn_nonneg _).mp
    have hfclip : ∀ᵐ x ∂μ, 0 ≤ normalClipL2 μ ((k : ℝ) + 1) (by positivity) f x ∧
        normalClipL2 μ ((k : ℝ) + 1) (by positivity) f x ≤ (k : ℝ) + 1 := by
      filter_upwards [normalClipL2_coe μ ((k : ℝ) + 1) (by positivity) f] with x hx
      rw [hx]
      exact normalClip_mem_interval (by positivity) _
    exact (scalarHeatFamily_markov g μ hμ ht ((k : ℝ) + 1) (by positivity) _ hfclip).mono
      (fun _ h => h.1)
  apply (Lp.coeFn_nonneg _).mpr
  have hclosed : IsClosed {v : Lp ℝ 2 μ | (0 : Lp ℝ 2 μ) ≤ v} := isClosed_Ici
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hbound)

/-- The bounded Markov interval includes its degenerate zero endpoint. -/
theorem scalarHeatFamily_submarkov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ, 0 ≤ scalarHeatFamily g μ hμ t f x ∧ scalarHeatFamily g μ hμ t f x ≤ K := by
  rcases hK.eq_or_lt with rfl | hK
  · have hf0 : f = 0 := by
      apply Lp.ext
      filter_upwards [hf, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx hzero
      exact (le_antisymm hx.2 hx.1).trans hzero.symm
    have hTf : scalarHeatFamily g μ hμ t f = (0 : Lp ℝ 2 μ) := by rw [hf0, map_zero]
    rw [hTf]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx
    rw [hx]
    exact ⟨le_rfl, le_rfl⟩
  · exact scalarHeatFamily_markov g μ hμ ht K hK f hf

/-- L∞ contractivity for every nonnegative numerical bound. -/
theorem scalarHeatFamily_linf (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, |f x| ≤ K) :
    ∀ᵐ x ∂μ, |scalarHeatFamily g μ hμ t f x| ≤ K := by
  rcases hK.eq_or_lt with rfl | hK
  · have hf0 : f = 0 := by
      apply Lp.ext
      filter_upwards [hf, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx hzero
      exact (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))).trans hzero.symm
    have hTf : scalarHeatFamily g μ hμ t f = (0 : Lp ℝ 2 μ) := by rw [hf0, map_zero]
    rw [hTf]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx
    rw [hx]
    simp only [Pi.zero_apply, abs_zero, le_refl]
  · exact scalarHeatFamily_abs_markov g μ hμ ht K hK f hf

end Yau.LeafProofs.L19Aux
