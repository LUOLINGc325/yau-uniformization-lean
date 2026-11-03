import Yau.Proofs.D02JensenFubini
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- Jensen with the actual finite mass displayed. The mass factor on the
right is retained until after integrating over the evaluation variable. -/
theorem exp_logPotential_le_average {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν ≠ 0) (p : ℝ) (z : ℂ)
    (hlog : Integrable (fun w ↦ Real.log ‖w - z‖) ν)
    (hexp : Integrable (fun w ↦ expLogKernel (p * (ν univ).toReal) (w - z)) ν) :
    Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν) ≤
      (ν univ).toReal⁻¹ * ∫ w, expLogKernel (p * (ν univ).toReal) (w - z) ∂ν := by
  let m := (ν univ).toReal
  have hm : m ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr hν,
    measure_ne_top ν univ⟩
  letI : NeZero ν := ⟨hν⟩
  have h := convexOn_exp.map_average_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    (hlog.const_mul (-p * m)) (by simpa only [Function.comp_def, expLogKernel, neg_mul, m] using hexp)
  simp only [average_eq, integral_const_mul, smul_eq_mul, measureReal_def] at h
  have heq : m⁻¹ * ((-p * m) * ∫ w, Real.log ‖w - z‖ ∂ν) =
      -p * ∫ w, Real.log ‖w - z‖ ∂ν := by field_simp
  change Real.exp (m⁻¹ * ((-p * m) * ∫ w, Real.log ‖w - z‖ ∂ν)) ≤ _ at h
  rw [heq] at h
  simpa only [expLogKernel, neg_mul, m] using h

/-- The zero-measure branch is an exact identity, independent of any
probability normalization or logarithmic singularity convention. -/
theorem exp_logPotential_zero (p : ℝ) (z : ℂ) :
    Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂(0 : Measure ℂ)) = 1 := by simp

/-- Exponentials of finite logarithmic potentials have one uniform area
bound whenever the total mass stays strictly below the planar critical value.
The constant is chosen before the varying measure. -/
theorem exists_uniform_exp_logPotential_bound (z₀ : ℂ) (R r : ℝ) (p b : ℝ)
    (hp : 0 ≤ p) (hpb : p * b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Measure ℂ, IsFiniteMeasure ν →
      (∀ᵐ w ∂ν, w ∈ Metric.ball z₀ R) → (ν univ).toReal ≤ b →
      (∀ z ∈ Metric.ball z₀ r, Integrable (fun w ↦ Real.log ‖w - z‖) ν) →
      IntegrableOn (fun z ↦ Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν))
        (Metric.ball z₀ r) volume ∧
      (∫ z in Metric.ball z₀ r, Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν)) ≤ C := by
  let S := Metric.ball z₀ r
  let T := max (r + R) 1
  let k := fun z ↦ 1 + expLogKernel (p * b) z
  have hk : Measurable k := measurable_const.add (expLogKernel_measurable _)
  have hk0 : ∀ z, 0 ≤ k z := fun z ↦ add_nonneg zero_le_one (expLogKernel_pos _ _).le
  have hki : IntegrableOn k (Metric.ball 0 T) volume := by
    exact ((continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) T)).mono_set
      Metric.ball_subset_closedBall).add (expLogKernel_integrableOn_ball hpb T)
  let B := ∫ z in Metric.ball 0 T, k z
  have hB : 0 ≤ B := integral_nonneg hk0
  let C := volume.real S + B
  have hC : 0 ≤ C := add_nonneg ENNReal.toReal_nonneg hB
  refine ⟨C, hC, ?_⟩
  intro ν hν hνD hmass hlog
  letI : IsFiniteMeasure ν := hν
  by_cases hzero : ν = 0
  · subst ν
    have hi : IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) S volume :=
      (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall z₀ r)).mono_set
        Metric.ball_subset_closedBall
    constructor
    · simpa only [integral_zero_measure, mul_zero, Real.exp_zero] using hi
    · simp only [integral_zero_measure, mul_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
      simpa only [C, S, measureReal_def, Measure.restrict_apply_univ] using
        (le_add_of_nonneg_right hB : volume.real S ≤ volume.real S + B)
  · let m := (ν univ).toReal
    have hm : 0 < m := ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hzero)
      (measure_ne_top ν univ)
    have hpa : 0 ≤ p * m := mul_nonneg hp hm.le
    have hpab : p * m ≤ p * b := mul_le_mul_of_nonneg_left hmass hp
    have hkw : ∀ w ∈ Metric.ball z₀ R,
        IntegrableOn (fun z ↦ k (w - z)) S volume ∧
          (∫ z in S, k (w - z)) ≤ B := fun w hw ↦
      integral_kernel_disc_bound hki hk0 (le_max_left _ _) hw
    have hiK := integrable_pair_kernel hk hk0 hνD hkw
    have hmeas : Measurable (fun q : ℂ × ℂ ↦ expLogKernel (p * m) (q.2 - q.1)) :=
      (expLogKernel_measurable _).comp (measurable_snd.sub measurable_fst)
    have hiA : Integrable (fun q : ℂ × ℂ ↦ expLogKernel (p * m) (q.2 - q.1))
        ((volume.restrict S).prod ν) := by
      apply hiK.mono' hmeas.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro q
      rw [Real.norm_of_nonneg (expLogKernel_pos _ _).le]
      exact expLogKernel_le_one_add hpa hpab _
    have hPmeas : StronglyMeasurable (fun z : ℂ ↦ ∫ w, Real.log ‖w - z‖ ∂ν) := by
      have hj : Measurable (fun q : ℂ × ℂ ↦ Real.log ‖q.2 - q.1‖) :=
        Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm
      exact hj.stronglyMeasurable.integral_prod_right'
    have hpoint : ∀ᵐ z ∂volume.restrict S,
        Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν) ≤
          m⁻¹ * ∫ w, expLogKernel (p * m) (w - z) ∂ν := by
      filter_upwards [ae_restrict_mem measurableSet_ball, hiA.prod_right_ae] with z hz hzi
      exact exp_logPotential_le_average hzero p z (hlog z hz) hzi
    have hiExp : IntegrableOn (fun z ↦ Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν)) S volume := by
      apply (hiA.integral_prod_left.const_mul m⁻¹).mono'
        (Real.continuous_exp.comp_stronglyMeasurable (hPmeas.const_mul (-p))).aestronglyMeasurable.restrict
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint
    refine ⟨hiExp, ?_⟩
    have hcomp : (∫ z in S, ∫ w, expLogKernel (p * m) (w - z) ∂ν) ≤ B * m := by
      apply le_trans (integral_mono_ae hiA.integral_prod_left hiK.integral_prod_left ?_)
        (integral_pair_kernel_le hk hk0 hνD hkw)
      filter_upwards [hiA.prod_right_ae, hiK.prod_right_ae] with z hza hzk
      exact integral_mono hza hzk (fun w ↦ expLogKernel_le_one_add hpa hpab _)
    have hbound : (∫ z in S, Real.exp (-p * ∫ w, Real.log ‖w - z‖ ∂ν)) ≤ m⁻¹ * (B * m) := by
      calc
        _ ≤ ∫ z in S, m⁻¹ * (∫ w, expLogKernel (p * m) (w - z) ∂ν) :=
          integral_mono_ae hiExp (hiA.integral_prod_left.const_mul m⁻¹) hpoint
        _ = m⁻¹ * (∫ z in S, ∫ w, expLogKernel (p * m) (w - z) ∂ν) := integral_const_mul _ _
        _ ≤ m⁻¹ * (B * m) := mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hm.le)
    have heq : m⁻¹ * (B * m) = B := by field_simp
    rw [heq] at hbound
    exact hbound.trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)

end Yau.NodeProofs.D02JensenAux
