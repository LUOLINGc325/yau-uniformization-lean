import Yau.Proofs.V03BoundaryCostSmooth
import Yau.Proofs.V03Envelope

/-! The actual boundary integral splits into norm and wall averages because
both traces are integrable. Strict contact then gives the localization lower
bound without discarding the complete energy penalty. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_normTrace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => let y := F.f (circlePoint θ)
      dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) := by
  have hf (θ : ℝ) : ContDiffWithinAt ℝ ∞
      (fun ζ => dualNorm (d.h (discTime F ζ)) (F.f ζ).1 (F.f ζ).2)
      (Metric.closedBall 0 1) (((1 : ℝ) : ℂ) * circlePoint θ) := by
    simpa only [Complex.ofReal_one, one_mul] using
      admissible_metricNorm_contDiffOn hd hF (circlePoint θ) (circlePoint_mem_closedBall θ)
  have hc := radial_trace_contDiff (r := 1) (by simp) hf
  simpa only [Complex.ofReal_one, one_mul] using hc

theorem admissible_wallTrace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => wallCost d j (F.f (circlePoint θ))
      (discTime F (circlePoint θ)) F.s) := by
  have hb := admissible_boundaryDensity_circle_contDiff hd hF
  have hn := admissible_normTrace_contDiff hd hF
  convert hb.sub hn using 1
  funext θ
  dsimp only [boundaryDensity]
  ring

theorem admissible_boundaryCost_split {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    boundaryCost d j F =
      circleAverage (fun θ => let y := F.f (circlePoint θ)
        dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) +
      circleAverage (fun θ => wallCost d j (F.f (circlePoint θ))
        (discTime F (circlePoint θ)) F.s) := by
  have hn := (admissible_normTrace_contDiff hd hF).continuous.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hw := (admissible_wallTrace_contDiff hd hF).continuous.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  unfold boundaryCost circleAverage
  rw [intervalIntegral.integral_add hn hw, mul_add]

theorem penalizedFunctional_lower_wall_energy {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (ε : ℝ) :
    circleAverage (fun θ => wallCost d j (F.f (circlePoint θ))
      (discTime F (circlePoint θ)) F.s) + ε * (variationEnergy d j F).toReal ≤
      penalizedFunctional d j ε F := by
  have hn := contact_test_le_disc_average hd hF
  unfold penalizedFunctional
  rw [admissible_boundaryCost_split hd hF]
  linarith

theorem penalizedFunctional_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ penalizedFunctional d j ε F :=
  (add_nonneg (admissible_wallAverage_nonneg hd hF)
    (mul_nonneg hε ENNReal.toReal_nonneg)).trans (penalizedFunctional_lower_wall_energy hd hF ε)

theorem localizedInfimum_nonneg {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ localizedInfimum d j ε := by
  apply le_iInf
  intro F
  apply le_iInf
  intro hF
  exact EReal.coe_le_coe_iff.mpr (penalizedFunctional_nonneg hd hF hε)

end Yau.Blueprint.V03Proof
