import Yau.Proofs.V03BaseDensity

/-! Finiteness and radial convergence of the original base metric area,
using its actual closed-disc density and the native manifold derivative. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def radialBaseDensity (h : HermitianField M) (f : ℂ → CotangentPoint M)
    (r : ℝ) (ζ : ℂ) : ℝ := r ^ 2 * baseDensityWithin h f ((r : ℂ) * ζ)

theorem baseDensityWithin_radial (h : HermitianField M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) :
    baseDensityWithin h (fun η => f ((r : ℂ) * η)) ζ = radialBaseDensity h f r ζ := by
  have hpt : (r : ℂ) * ζ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hζ ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg ζ) hr.2).trans_lt hζ
  have hζnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ζ :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hζ) Metric.ball_subset_closedBall
  have hptnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ((r : ℂ) * ζ) :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hpt) Metric.ball_subset_closedBall
  let y := (f ((r : ℂ) * ζ)).1
  let H : ℂ → ComplexVector n := fun η => chartPt y (f η).1
  have hself : f ((r : ℂ) * ζ) ∈ cotangentSource y := mem_extChartAt_source _
  have hHc := (cotangentDisc_coords_contDiffWithinAt hf (Metric.ball_subset_closedBall hpt) y hself).fst
  have hH : DifferentiableAt ℂ H ((r : ℂ) * ζ) :=
    (hHc.contDiffAt hptnhds).differentiableAt (by simp)
  have hcomp : fderiv ℂ (fun η => H ((r : ℂ) * η)) ζ 1 =
      (r : ℂ) • fderiv ℂ H ((r : ℂ) * ζ) 1 := by
    have hc := (hH.hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).const_mul (r : ℂ))).fderiv
    have hv := congrArg (fun L : ℂ →L[ℂ] ComplexVector n => L 1) hc
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul] using hv
  have hdir : fderivWithin ℂ (fun η => H ((r : ℂ) * η)) (Metric.closedBall 0 1) ζ 1 =
      (r : ℂ) • fderivWithin ℂ H (Metric.closedBall 0 1) ((r : ℂ) * ζ) 1 := by
    rw [fderivWithin_of_mem_nhds hζnhds, fderivWithin_of_mem_nhds hptnhds]
    exact hcomp
  change 2 * hermitianNormSq (h y) (chartVec y y
    (fderivWithin ℂ (fun η => H ((r : ℂ) * η)) (Metric.closedBall 0 1) ζ 1)) =
    r ^ 2 * (2 * hermitianNormSq (h y) (chartVec y y
      (fderivWithin ℂ H (Metric.closedBall 0 1) ((r : ℂ) * ζ) 1)))
  rw [hdir, chartVec_smul, hermitianNormSq_ofReal_smul]
  ring

theorem radialBaseDensity_continuousOn (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContinuousOn (fun p : ℝ × ℂ => radialBaseDensity g.form f p.1 p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) := by
  have hm : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 hp.2
  exact (continuous_fst.pow 2).continuousOn.mul
    ((baseDensityWithin_continuousOn g hf).comp hm.continuousOn hmap)

theorem discArea_radial_eq_integral (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    discArea g.form (fun ζ => (f ((r : ℂ) * ζ)).1) =
      ENNReal.ofReal (∫ ζ in Metric.ball (0 : ℂ) 1, radialBaseDensity g.form f r ζ) := by
  have hrad : CotangentDisc (fun ζ => f ((r : ℂ) * ζ)) :=
    ((cotangentDisc_holomorphicOn hf).comp (contDiff_const.mul contDiff_id)
      (radial_maps_closedBall hr.1 hr.2)).cotangentDisc
  rw [discArea_eq_ofReal_integral g hrad]
  apply congrArg ENNReal.ofReal
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  exact baseDensityWithin_radial g.form hf hr hζ

theorem discArea_radial_tendsto (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    Tendsto (fun r : ℝ => discArea g.form (fun ζ => (f ((r : ℂ) * ζ)).1))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (discArea g.form (fun ζ => (f ζ).1))) := by
  have hc := continuousWithinAt_ballIntegral_of_joint_compact isCompact_Icc
    (x := (1 : ℝ)) (by simp) (radialBaseDensity_continuousOn g hf)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  have he := discArea_radial_eq_integral g hf (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul] at he
  rw [← he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (discArea_radial_eq_integral g hf hr).symm

end Yau.Blueprint.V03Proof
