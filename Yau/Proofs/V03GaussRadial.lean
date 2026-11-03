import Yau.Proofs.V03GaussDensity

/-! Radial convergence of the original computed Gauss area. Domination is
derived from the continuous closed-disc density, including at r=1. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realLeviValue_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (r : ℝ) (v : E) :
    realLeviValue f z (r • v) = r ^ 2 * realLeviValue f z v := by
  dsimp only [realLeviValue]
  rw [mixedWirt_real_diagonal hf, mixedWirt_real_diagonal hf]
  simp only [smul_comm Complex.I r, map_smul, smul_apply, smul_eq_mul]
  ring

variable {n q : ℕ} {M : ComplexManifold n}

def radialGaussDensity (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (r : ℝ) (ζ : ℂ) : ℝ :=
  r ^ 2 * gaussDensityWithin G f ((r : ℂ) * ζ)

theorem gaussDensityWithin_radial {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) :
    gaussDensityWithin G (fun η => f ((r : ℂ) * η)) ζ = radialGaussDensity G f r ζ := by
  have hpt : (r : ℂ) * ζ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hζ ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_of_le_one_left (norm_nonneg ζ) hr.2).trans_lt hζ
  have hζnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ζ :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hζ) Metric.ball_subset_closedBall
  have hptnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ((r : ℂ) * ζ) :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hpt) Metric.ball_subset_closedBall
  let y := f ((r : ℂ) * ζ)
  let H : ℂ → CotangentCoord n := fun η => cotangentChart y.1 (f η)
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hHc := cotangentDisc_coords_contDiffWithinAt hf (Metric.ball_subset_closedBall hpt) y.1 hself
  have hH : DifferentiableAt ℂ H ((r : ℂ) * ζ) :=
    (hHc.contDiffAt hptnhds).differentiableAt (by simp)
  have hcomp : fderiv ℂ (fun η => H ((r : ℂ) * η)) ζ 1 =
      (r : ℂ) • fderiv ℂ H ((r : ℂ) * ζ) 1 := by
    have hc := (hH.hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).const_mul (r : ℂ))).fderiv
    have hv := congrArg (fun L : ℂ →L[ℂ] CotangentCoord n => L 1) hc
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul] using hv
  have hdir : fderivWithin ℂ (fun η => H ((r : ℂ) * η)) (Metric.closedBall 0 1) ζ 1 =
      (r : ℂ) • fderivWithin ℂ H (Metric.closedBall 0 1) ((r : ℂ) * ζ) 1 := by
    rw [fderivWithin_of_mem_nhds hζnhds, fderivWithin_of_mem_nhds hptnhds]
    exact hcomp
  have hP : ContDiffAt ℝ 2 (gaussPotential G y.1) (cotangentChart y.1 y) :=
    (gaussPotential_contDiffAt hG y.1 (cotangentChart_mapsTo y.1 hself)).of_le (by simp)
  change 2 * realLeviValue (gaussPotential G y.1) (cotangentChart y.1 y)
    (fderivWithin ℂ (fun η => H ((r : ℂ) * η)) (Metric.closedBall 0 1) ζ 1) =
    r ^ 2 * (2 * realLeviValue (gaussPotential G y.1) (cotangentChart y.1 y)
      (fderivWithin ℂ H (Metric.closedBall 0 1) ((r : ℂ) * ζ) 1))
  have hrsmul (v : CotangentCoord n) : (r : ℂ) • v = r • v := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      (RCLike.real_smul_eq_coe_smul (K := ℂ) r v).symm
  rw [hdir, hrsmul, realLeviValue_real_smul hP]
  ring

theorem radialGaussDensity_continuousOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContinuousOn (fun p : ℝ × ℂ => radialGaussDensity G f p.1 p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) := by
  have hm : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
      (Set.Icc 0 1 ×ˢ Metric.closedBall 0 1) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 hp.2
  exact (continuous_fst.pow 2).continuousOn.mul
    ((gaussDensityWithin_continuousOn hG hf).comp hm.continuousOn hmap)

theorem gaussArea_radial_eq_integral {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    gaussArea G (fun ζ => f ((r : ℂ) * ζ)) =
      ∫ ζ in Metric.ball (0 : ℂ) 1, radialGaussDensity G f r ζ := by
  rw [gaussArea_eq_integral_densityWithin]
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  exact gaussDensityWithin_radial hG hf hr hζ

theorem gaussArea_radial_tendsto {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    Tendsto (fun r : ℝ => gaussArea G (fun ζ => f ((r : ℂ) * ζ)))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (gaussArea G f)) := by
  have hc := continuousWithinAt_ballIntegral_of_joint_compact isCompact_Icc
    (x := (1 : ℝ)) (by simp) (radialGaussDensity_continuousOn hG hf)
  have ht : Tendsto (fun r => ∫ ζ in Metric.ball (0 : ℂ) 1, radialGaussDensity G f r ζ)
      (𝓝[Set.Icc 0 1] 1) (𝓝 (∫ ζ in Metric.ball (0 : ℂ) 1, radialGaussDensity G f 1 ζ)) := hc
  have he := gaussArea_radial_eq_integral hG hf (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul] at he
  rw [← he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (gaussArea_radial_eq_integral hG hf hr).symm

end Yau.Blueprint.V03Proof
