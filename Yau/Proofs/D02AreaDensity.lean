import Yau.Proofs.D02PhysicalScaling
import Yau.Proofs.V03BaseDensity

/-! The actual base disc has a continuous closed-disc density, computed
with the within derivative. Its interior value is the original mfderiv
density, including the factor two for the same real metric. -/

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

def zeroCotangentLift (f : ℂ → M.Carrier) (z : ℂ) : CotangentPoint M := (f z, 0)

theorem zeroCotangentLift_isDisc {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    CotangentDisc (zeroCotangentLift f) := by
  refine ⟨hf, fun z hz => ?_⟩
  have he : (fun w => covectorCoords (f z) (f w) (0 : Covector n)) =
      (fun _ : ℂ => (0 : ComplexVector n)) := by
    funext w
    ext i
    change (0 : Covector n) (chartVec (f z) (f w) (stdVec i)) = 0
    rfl
  change ContDiffWithinAt ℂ ∞ (fun w => covectorCoords (f z) (f w) (0 : Covector n)) _ _
  rw [he]
  exact contDiffWithinAt_const

def closedDiscDensity (g : HermitianField M) (f : ℂ → M.Carrier) : ℂ → ℝ :=
  baseDensityWithin g (zeroCotangentLift f)

theorem closedDiscDensity_nonneg (g : HermitianField M) (f : ℂ → M.Carrier) (z : ℂ) :
    0 ≤ closedDiscDensity g f z := baseDensityWithin_nonneg g (zeroCotangentLift f) z

theorem closedDiscDensity_continuousOn (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    ContinuousOn (closedDiscDensity g.form f) (Metric.closedBall (0 : ℂ) 1) :=
  baseDensityWithin_continuousOn g (zeroCotangentLift_isDisc hf)

/-- Interior equality uses the original global manifold derivative, not a new velocity. -/
theorem closedDiscDensity_eq_physical (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    closedDiscDensity g f z =
      2 * hermitianNormSq (g (f z)) (physicalCurveDerivative f z) := by
  unfold closedDiscDensity baseDensityWithin
  rw [baseVelocityWithin_eq_mfderiv (zeroCotangentLift_isDisc hf) hz]
  rfl

theorem closedDiscDensity_integrableOn (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    IntegrableOn (closedDiscDensity g.form f) (Metric.ball (0 : ℂ) 1) :=
  baseDensityWithin_integrableOn g (zeroCotangentLift_isDisc hf)

theorem discArea_eq_closedDiscDensity (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    discArea g f = ∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (closedDiscDensity g f z) :=
  discArea_eq_lintegral_baseDensity g (zeroCotangentLift_isDisc hf)

theorem discArea_eq_closedDiscIntegral (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    discArea g.form f = ENNReal.ofReal
      (∫ z in Metric.ball (0 : ℂ) 1, closedDiscDensity g.form f z) :=
  discArea_eq_ofReal_integral g (zeroCotangentLift_isDisc hf)

/-- A globally measurable extension by zero of the actual interior density. -/
def discEnergyDensity (g : HermitianField M) (f : ℂ → M.Carrier) : ℂ → ℝ≥0∞ :=
  (Metric.ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal (closedDiscDensity g f z))

theorem discEnergyDensity_measurable (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    Measurable (discEnergyDensity g.form f) := by
  classical
  have hc := ENNReal.continuous_ofReal.comp_continuousOn
    ((closedDiscDensity_continuousOn g hf).mono Metric.ball_subset_closedBall)
  exact hc.measurable_piecewise continuousOn_const measurableSet_ball

theorem discEnergyDensity_eq_physical (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyDensity g f z = ENNReal.ofReal
      (2 * hermitianNormSq (g (f z)) (physicalCurveDerivative f z)) := by
  rw [discEnergyDensity, Set.indicator_of_mem hz, closedDiscDensity_eq_physical g hf hz]

theorem discEnergyDensity_integral (g : HermitianField M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1, discEnergyDensity g f z) = discArea g f := by
  rw [discArea_eq_closedDiscDensity g hf]
  apply setLIntegral_congr_fun measurableSet_ball
  intro z hz
  exact Set.indicator_of_mem hz _

end Yau.NodeProofs.D02Aux
