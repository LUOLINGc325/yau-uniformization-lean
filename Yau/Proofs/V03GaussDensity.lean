import Yau.Proofs.V03GaussTransport
import Yau.Proofs.V03DiscDifferential
import Yau.Proofs.V03LeviSmooth

/-! The actual interior Gauss density has a continuous nonnegative
closed-disc representative, derived by fixed-chart differential transport. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def gaussDensityWithin (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (ζ : ℂ) : ℝ :=
  2 * realLeviValue (gaussPotential G (f ζ).1) (cotangentChart (f ζ).1 (f ζ))
    (fderivWithin ℂ (fun η => cotangentChart (f ζ).1 (f η)) (Metric.closedBall 0 1) ζ 1)

theorem gaussDensityWithin_eq_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : M.Carrier)
    (hx : f ζ ∈ cotangentSource x) :
    gaussDensityWithin G f ζ = 2 * realLeviValue (gaussPotential G x)
      (cotangentChart x (f ζ))
      (fderivWithin ℂ (fun η => cotangentChart x (f η)) (Metric.closedBall 0 1) ζ 1) := by
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have hbase : chartInv (f ζ).1 (cotangentChart (f ζ).1 (f ζ)).1 = (f ζ).1 :=
    (extChartAt (ComplexModel n) (f ζ).1).left_inv hself
  have hD := congrArg (fun L : ℂ →L[ℂ] CotangentCoord n => L 1)
    (cotangentDisc_fderivWithin_coords_change hf hζ (f ζ).1 x hself hx)
  simp only [ContinuousLinearMap.comp_apply] at hD
  have hL := gaussPotential_levi_chart_change hG (f ζ).1 x
    (cotangentChart_mapsTo (f ζ).1 hself) (by rw [hbase]; exact hx)
    (fderivWithin ℂ (fun η => cotangentChart (f ζ).1 (f η)) (Metric.closedBall 0 1) ζ 1)
  rw [cotangentChart_left_inv (f ζ).1 hself, ← hD] at hL
  exact congrArg (fun t : ℝ => 2 * t) hL

theorem gaussDensityWithin_continuousOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContinuousOn (gaussDensityWithin G f) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hu : UniqueDiffOn ℂ (Metric.closedBall (0 : ℂ) 1 ∩ V) :=
    fun η hη => (uniqueDiffOn_complex_closedDisc η hη.1).inter (hV.mem_nhds hη.2)
  have hderiv := (hcoord.continuousOn_fderivWithin hu (by simp)).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  have hparam := hcoord.continuousOn.prodMk hderiv
  have hopen : IsOpen (cotangentTarget (f ζ).1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) (f ζ).1).prod isOpen_univ
  have hpot : ContDiffOn ℝ ∞ (gaussPotential G (f ζ).1) (cotangentTarget (f ζ).1) :=
    fun z hz => (gaussPotential_contDiffAt hG (f ζ).1 hz).contDiffWithinAt
  have hLevi := (realLeviValue_contDiffOn hopen hpot).continuousOn
  have hmodel := (continuousOn_const (c := (2 : ℝ))).mul (hLevi.comp hparam
    (fun η hη => ⟨cotangentChart_mapsTo (f ζ).1 (hsource η hη), Set.mem_univ _⟩))
  apply (continuousWithinAt_inter (hV.mem_nhds hζV)).mp
  apply (hmodel ζ ⟨hζ, hζV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [gaussDensityWithin_eq_fixed_chart hG hf hη.1 (f ζ).1 (hsource η hη)]
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [fderivWithin_inter (hV.mem_nhds hη.2)]

theorem gaussDensityWithin_nonneg {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (f : ℂ → CotangentPoint M) (ζ : ℂ) :
    0 ≤ gaussDensityWithin G f ζ :=
  mul_nonneg (by norm_num) (gaussPotential_levi_nonneg hG (f ζ) _)

theorem gaussArea_eq_integral_densityWithin {G : CotangentPoint M → ComplexVector q}
    (f : ℂ → CotangentPoint M) :
    gaussArea G f = ∫ ζ in Metric.ball (0 : ℂ) 1, gaussDensityWithin G f ζ := by
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ζ :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hζ) Metric.ball_subset_closedBall
  dsimp only [gaussDensityWithin, realLeviValue]
  rw [fderivWithin_of_mem_nhds hnhds]

theorem gaussDensityWithin_integrableOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    IntegrableOn (gaussDensityWithin G f) (Metric.ball 0 1) volume :=
  ((gaussDensityWithin_continuousOn hG hf).integrableOn_compact
    (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

end Yau.Blueprint.V03Proof
