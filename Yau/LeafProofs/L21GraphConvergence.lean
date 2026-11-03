import Yau.LeafProofs.L21GraphCutoffs

/-! Dominated convergence for the actual weighted L² graph errors. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem tendsto_integral_norm_sq_of_dominated
    {α F G : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (μ : Measure α) {u : α → F} (hu : MemLp u 2 μ)
    (f : ℕ → α → G) (hmeas : ∀ m, AEStronglyMeasurable (f m) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ m, ∀ᵐ x ∂μ, ‖f m x‖ ≤ C * ‖u x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => f m x) atTop (𝓝 0)) :
    (∀ m, MemLp (f m) 2 μ) ∧
      Tendsto (fun m => ∫ x, ‖f m x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let B := fun x => C ^ 2 * ‖u x‖ ^ 2
  have hB : Integrable B μ := (hu.integrable_norm_pow (p := 2) (by decide)).const_mul _
  have hfm (m : ℕ) : AEStronglyMeasurable (fun x => ‖f m x‖ ^ 2) μ := (hmeas m).norm.pow 2
  have hdom (m : ℕ) : ∀ᵐ x ∂μ, ‖‖f m x‖ ^ 2‖ ≤ B x := by
    filter_upwards [hbound m] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (norm_nonneg (f m x)) (mul_nonneg hC (norm_nonneg (u x)))).mpr hx
    simpa only [mul_pow] using hs
  refine ⟨?_, ?_⟩
  · intro m
    exact (memLp_two_iff_integrable_sq_norm (hmeas m)).mpr (hB.mono' (hfm m) (hdom m))
  · have hh := tendsto_integral_of_dominated_convergence B hfm hB hdom
      (by
        filter_upwards [hlim] with x hx
        simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hx.norm.pow 2)
    simpa only [integral_zero] using hh

theorem boundaryCutoff_L2_convergence
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure E) {u : E → G} (hu : MemLp u 2 (μ.restrict (Metric.ball 0 1))) :
    (∀ m : ℕ, MemLp (fun x => (boundaryCutoff m x - 1) • u x) 2 (μ.restrict (Metric.ball 0 1))) ∧
      Tendsto (fun m : ℕ => ∫ x in Metric.ball (0 : E) 1,
        ‖(boundaryCutoff m x - 1) • u x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_norm_sq_of_dominated (C := 1) _ hu
  · intro m
    exact ((contDiff_boundaryCutoff m).continuous.sub continuous_const).aestronglyMeasurable.smul
      hu.aestronglyMeasurable
  · norm_num
  · intro m
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs, one_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [abs_of_nonpos (by linarith [boundaryCutoff_le_one m x])]
    linarith [boundaryCutoff_nonneg m x]
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have he : (fun m : ℕ => (boundaryCutoff m x - 1) • u x) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_boundaryCutoff_eq_one hx] with m hm
      simp only [hm, sub_self, zero_smul]
    exact tendsto_const_nhds.congr' he.symm

theorem boundaryCutoff_scaled_derivative_L2_convergence
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure E) {u : E → G} (hu : MemLp u 2 (μ.restrict (Metric.ball 0 1))) (v : E) :
    (∀ m : ℕ, MemLp (fun x => (rho x * fderiv ℝ (boundaryCutoff (E := E) m) x v) • u x)
      2 (μ.restrict (Metric.ball 0 1))) ∧
      Tendsto (fun m : ℕ => ∫ x in Metric.ball (0 : E) 1,
        ‖(rho x * fderiv ℝ (boundaryCutoff (E := E) m) x v) • u x‖ ^ 2 ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_scaled_fderiv_boundaryCutoff (E := E)
  apply tendsto_integral_norm_sq_of_dominated (C := C * ‖v‖) _ hu
  · intro m
    have hd : Continuous (fun x => fderiv ℝ (boundaryCutoff (E := E) m) x v) :=
      ((contDiff_boundaryCutoff m).continuous_fderiv (by simp)).clm_apply continuous_const
    exact ((contDiff_rho (E := E)).continuous.mul hd).aestronglyMeasurable.smul hu.aestronglyMeasurable
  · positivity
  · intro m
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hcoeff : ‖rho x * fderiv ℝ (boundaryCutoff (E := E) m) x v‖ ≤ C * ‖v‖ := by
      change ‖(rho x • fderiv ℝ (boundaryCutoff (E := E) m) x) v‖ ≤ _
      exact ((rho x • fderiv ℝ (boundaryCutoff (E := E) m) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hbound m x hx) (norm_nonneg v))
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have he : (fun m : ℕ => (rho x * fderiv ℝ (boundaryCutoff (E := E) m) x v) • u x) =ᶠ[atTop]
        (fun _ => 0) := by
      filter_upwards [eventually_fderiv_boundaryCutoff_eq_zero hx] with m hm
      simp only [hm, _root_.zero_apply, mul_zero, zero_smul]
    exact tendsto_const_nhds.congr' he.symm

end Yau.LeafProofs.L21Aux
