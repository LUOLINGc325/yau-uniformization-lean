import Yau.Proofs.V03BallIntegral
import Yau.Proofs.V03Radial
import Yau.Proofs.V03AmbientSmooth

/-! Finiteness and radial convergence of the actual Euclidean area, obtained
from the derivative on the original closed disc. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem uniqueDiffOn_complex_closedDisc : UniqueDiffOn ℂ (Metric.closedBall (0 : ℂ) 1) := by
  have hr : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : ℂ) 1) (by
      rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      exact ⟨0, by simp⟩)
  exact hr.mono_field

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def closedDiscDerivative (H : ℂ → E) (z : ℂ) : E :=
  fderivWithin ℂ H (Metric.closedBall 0 1) z 1

def radialEuclideanDensity (H : ℂ → E) (r : ℝ) (z : ℂ) : ℝ :=
  2 * ‖(r : ℂ) • closedDiscDerivative H ((r : ℂ) * z)‖ ^ 2

def normDiscArea (H : ℂ → E) : ENNReal :=
  ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (2 * ‖fderiv ℂ H z 1‖ ^ 2)

theorem continuousOn_closedDiscDerivative {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) :
    ContinuousOn (closedDiscDerivative H) (Metric.closedBall 0 1) :=
  (hH.continuousOn_fderivWithin uniqueDiffOn_complex_closedDisc (by simp)).clm_apply
    continuousOn_const

theorem radialEuclideanDensity_continuousOn {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) :
    ContinuousOn (fun p : ℝ × ℂ => radialEuclideanDensity H p.1 p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) := by
  have hm : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 hp.2
  have hd := (continuousOn_closedDiscDerivative hH).comp hm.continuousOn hmap
  exact continuousOn_const.mul
    (((Complex.continuous_ofReal.comp continuous_fst).continuousOn.smul hd).norm.pow 2)

theorem radialEuclideanDensity_eq {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ Metric.ball 0 1) :
    2 * ‖fderiv ℂ (fun w => H ((r : ℂ) * w)) z 1‖ ^ 2 =
      radialEuclideanDensity H r z := by
  have hz' : (r : ℂ) * z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) hr.2).trans_lt hz
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ((r : ℂ) * z) :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz') Metric.ball_subset_closedBall
  have hd : DifferentiableAt ℂ H ((r : ℂ) * z) :=
    (hH.differentiableOn (by simp) _ (Metric.ball_subset_closedBall hz')).differentiableAt hnhds
  have hdilate : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) * w) z :=
    differentiableAt_id.const_mul _
  have hc : fderiv ℂ (fun w => H ((r : ℂ) * w)) z =
      (fderiv ℂ H ((r : ℂ) * z)).comp ((r : ℂ) • ContinuousLinearMap.id ℂ ℂ) := by
    have hcomp := fderiv_comp z hd hdilate
    have hdil : fderiv ℂ (fun w : ℂ => (r : ℂ) * w) z =
        (r : ℂ) • ContinuousLinearMap.id ℂ ℂ :=
      ((hasFDerivAt_id z).const_mul (r : ℂ)).fderiv
    simpa only [Function.comp_def, hdil] using hcomp
  unfold radialEuclideanDensity closedDiscDerivative
  rw [hc, fderivWithin_of_mem_nhds hnhds]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  rw [map_smul]

theorem normDiscArea_radial_eq_integral {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    normDiscArea (fun z => H ((r : ℂ) * z)) =
      ENNReal.ofReal (∫ z in Metric.ball (0 : ℂ) 1, radialEuclideanDensity H r z) := by
  have hiota : Continuous (fun z : ℂ => (r, z)) := continuous_const.prodMk continuous_id
  have hmap : Set.MapsTo (fun z : ℂ => (r, z)) (Metric.closedBall 0 1)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) := fun z hz => ⟨hr, hz⟩
  have hc : ContinuousOn (radialEuclideanDensity H r) (Metric.closedBall 0 1) :=
    (radialEuclideanDensity_continuousOn hH).comp hiota.continuousOn hmap
  have hi := (hc.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set
    Metric.ball_subset_closedBall
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall
    (fun z => mul_nonneg (by norm_num) (sq_nonneg _)))]
  apply setLIntegral_congr_fun measurableSet_ball
  intro z hz
  exact congrArg ENNReal.ofReal (radialEuclideanDensity_eq hH hr hz)

theorem normDiscArea_ne_top_of_closedDisc {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) : normDiscArea H ≠ ⊤ := by
  have he := normDiscArea_radial_eq_integral hH (r := 1) (by simp)
  simpa only [Complex.ofReal_one, one_mul] using he.trans_ne ENNReal.ofReal_ne_top

theorem normDiscArea_radial_tendsto {H : ℂ → E}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) :
    Tendsto (fun r : ℝ => normDiscArea (fun z => H ((r : ℂ) * z)))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (normDiscArea H)) := by
  have hc := continuousWithinAt_ballIntegral_of_joint_compact isCompact_Icc
    (x := (1 : ℝ)) (by simp) (radialEuclideanDensity_continuousOn hH)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  have he := normDiscArea_radial_eq_integral hH (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul] at he
  rw [← he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (normDiscArea_radial_eq_integral hH hr).symm

theorem euclideanArea_ne_top_of_closedDisc {q : ℕ} {H : ℂ → ComplexVector q}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) : euclideanArea H ≠ ⊤ :=
  normDiscArea_ne_top_of_closedDisc hH

theorem euclideanArea_radial_tendsto {q : ℕ} {H : ℂ → ComplexVector q}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) :
    Tendsto (fun r : ℝ => euclideanArea (fun z => H ((r : ℂ) * z)))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (euclideanArea H)) :=
  normDiscArea_radial_tendsto hH

end Yau.Blueprint.V03Proof
