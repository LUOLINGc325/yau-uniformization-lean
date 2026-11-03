import Yau.Proofs.V03BaseDifferential
import Yau.Proofs.V03MetricQuadratic

/-! A continuous nonnegative representative of the original base-area
density on the closed disc, with exact finite integral conversion. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def baseDensityWithin (h : HermitianField M) (f : ℂ → CotangentPoint M) (ζ : ℂ) : ℝ :=
  2 * hermitianNormSq (h (f ζ).1) (baseVelocityWithin f ζ)

theorem baseDensityWithin_eq_fixed_chart (h : HermitianField M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : M.Carrier)
    (hx : f ζ ∈ cotangentSource x) :
    baseDensityWithin h f ζ = 2 * hermitianChartNormSq h x (chartPt x (f ζ).1)
      (fderivWithin ℂ (fun η => chartPt x (f η).1) (Metric.closedBall 0 1) ζ 1) := by
  dsimp only [baseDensityWithin]
  rw [baseVelocityWithin_eq_fixed_chart hf hζ x hx, hermitianChartNormSq_at_point h x _ hx]

theorem baseDensityWithin_continuousOn (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContinuousOn (baseDensityWithin g.form f) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hc : ContDiffOn ℂ ∞ (fun η => chartPt (f ζ).1 (f η).1) (Metric.closedBall 0 1 ∩ V) :=
    hcoord.fst
  have hu : UniqueDiffOn ℂ (Metric.closedBall (0 : ℂ) 1 ∩ V) :=
    fun η hη => (uniqueDiffOn_complex_closedDisc η hη.1).inter (hV.mem_nhds hη.2)
  have hderiv := (hc.continuousOn_fderivWithin hu (by simp)).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  have hparam := hc.continuousOn.prodMk hderiv
  have hNorm := (hermitianChartNormSq_contDiffOn g (f ζ).1).continuousOn
  have hmodel := (continuousOn_const (c := (2 : ℝ))).mul (hNorm.comp hparam
    (fun η hη => ⟨(extChartAt (ComplexModel n) (f ζ).1).map_source (hsource η hη),
      Set.mem_univ _⟩))
  apply (continuousWithinAt_inter (hV.mem_nhds hζV)).mp
  apply (hmodel ζ ⟨hζ, hζV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [baseDensityWithin_eq_fixed_chart g.form hf hη.1 (f ζ).1 (hsource η hη)]
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [fderivWithin_inter (hV.mem_nhds hη.2)]

theorem baseDensityWithin_nonneg (h : HermitianField M)
    (f : ℂ → CotangentPoint M) (ζ : ℂ) : 0 ≤ baseDensityWithin h f ζ :=
  mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)

theorem baseDensityWithin_integrableOn (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    IntegrableOn (baseDensityWithin g.form f) (Metric.ball 0 1) volume :=
  ((baseDensityWithin_continuousOn g hf).integrableOn_compact
    (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

theorem discArea_eq_lintegral_baseDensity (h : HermitianField M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    discArea h (fun ζ => (f ζ).1) = ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (baseDensityWithin h f ζ) := by
  unfold discArea
  rw [← lintegral_const_mul' (2 : ENNReal) _ (by norm_num)]
  apply setLIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  dsimp only [baseDensityWithin]
  rw [baseVelocityWithin_eq_mfderiv hf hζ, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem discArea_eq_ofReal_integral (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    discArea g.form (fun ζ => (f ζ).1) =
      ENNReal.ofReal (∫ ζ in Metric.ball (0 : ℂ) 1, baseDensityWithin g.form f ζ) := by
  rw [discArea_eq_lintegral_baseDensity g.form hf]
  exact (ofReal_integral_eq_lintegral_ofReal (baseDensityWithin_integrableOn g hf)
    (Eventually.of_forall (baseDensityWithin_nonneg g.form f))).symm

theorem discArea_ne_top_of_cotangentDisc (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    discArea g.form (fun ζ => (f ζ).1) ≠ ⊤ := by
  rw [discArea_eq_ofReal_integral g hf]
  exact ENNReal.ofReal_ne_top

end Yau.Blueprint.V03Proof
