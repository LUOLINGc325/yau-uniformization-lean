import Yau.LeafProofs.L08
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- The exponential logarithmic kernel is defined also at zero; its value
there is one. Its area integrability is always proved independently. -/
def expLogKernel (q : ℝ) (z : ℂ) : ℝ := Real.exp (-q * Real.log ‖z‖)

theorem expLogKernel_pos (q : ℝ) (z : ℂ) : 0 < expLogKernel q z := Real.exp_pos _

theorem expLogKernel_measurable (q : ℝ) : Measurable (expLogKernel q) := by
  exact Real.measurable_exp.comp ((measurable_const.mul (Real.measurable_log.comp measurable_norm)))

/-- The two-dimensional singularity is area integrable precisely in the
range needed below. The exceptional value at zero has zero ordinary area. -/
theorem expLogKernel_integrableOn_ball {q : ℝ} (hq : q < 2) (T : ℝ) :
    IntegrableOn (expLogKernel q) (Metric.ball 0 T) volume := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := q) (by simp [Complex.finrank_real_complex])
    (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hq)
  · have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae hne] with z hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_def_of_pos hn, one_mul, Real.norm_eq_abs,
      abs_of_pos (expLogKernel_pos q z)]
    unfold expLogKernel
    apply le_of_eq
    congr 1
    ring
  · exact (expLogKernel_measurable q).aestronglyMeasurable

/-- A fixed larger exponent dominates all smaller nonnegative exponents,
with a constant one covering distances at least one and the zero value. -/
theorem expLogKernel_le_one_add {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (z : ℂ) :
    expLogKernel a z ≤ 1 + expLogKernel b z := by
  by_cases hz : ‖z‖ ≤ 1
  · have hl : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg z) hz
    have hm : -a * Real.log ‖z‖ ≤ -b * Real.log ‖z‖ := by nlinarith
    calc
      _ ≤ expLogKernel b z := Real.exp_le_exp.mpr hm
      _ ≤ 1 + expLogKernel b z := by linarith
  · have hl : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (le_of_not_ge hz)
    have hm : -a * Real.log ‖z‖ ≤ 0 := by nlinarith
    have he : expLogKernel a z ≤ 1 := by simpa [expLogKernel] using Real.exp_le_exp.mpr hm
    exact he.trans (by linarith [expLogKernel_pos b z])

/-- Translation of a radial integration ball by the genuine area-preserving
reflection. This is used for both logarithmic and exponential kernels. -/
theorem integral_kernel_translate_ball (k : ℂ → ℝ) (w : ℂ) (T : ℝ) :
    (∫ z in Metric.ball w T, k (w - z)) = ∫ z in Metric.ball 0 T, k z := by
  have h := ((volume : Measure ℂ).measurePreserving_sub_left w).setIntegral_preimage_emb
    (MeasurableEquiv.subLeft w).measurableEmbedding k (Metric.ball 0 T)
  simpa [Function.comp_def, Metric.ball, dist_eq_norm, norm_sub_rev] using h

/-- A translated nonnegative kernel has one uniform integral bound on a
fixed disc when its singularities range over a second bounded disc. -/
theorem integral_kernel_disc_bound {k : ℂ → ℝ} {T r R : ℝ} {z₀ w : ℂ}
    (hk : IntegrableOn k (Metric.ball 0 T) volume) (hk0 : ∀ z, 0 ≤ k z)
    (hT : r + R ≤ T) (hw : w ∈ Metric.ball z₀ R) :
    IntegrableOn (fun z ↦ k (w - z)) (Metric.ball z₀ r) volume ∧
      (∫ z in Metric.ball z₀ r, k (w - z)) ≤ ∫ z in Metric.ball 0 T, k z := by
  have htrans : IntegrableOn (fun z ↦ k (w - z)) (Metric.ball w T) volume := by
    have h := ((volume : Measure ℂ).measurePreserving_sub_left w).integrableOn_comp_preimage
      (MeasurableEquiv.subLeft w).measurableEmbedding |>.mpr hk
    simpa [Function.comp_def, Metric.ball, dist_eq_norm, norm_sub_rev] using h
  have hsub : Metric.ball z₀ r ⊆ Metric.ball w T := by
    intro z hz
    have hdist := dist_triangle z z₀ w
    have hzw : dist z w < r + R := by
      rw [Metric.mem_ball, dist_comm w z₀] at hw
      rw [Metric.mem_ball] at hz
      linarith
    exact hzw.trans_le hT
  refine ⟨htrans.mono_set hsub, ?_⟩
  rw [← integral_kernel_translate_ball k w T]
  exact setIntegral_mono_set htrans (Filter.Eventually.of_forall fun z ↦ hk0 (w - z)) hsub.eventuallyLE

end Yau.NodeProofs.D02JensenAux
