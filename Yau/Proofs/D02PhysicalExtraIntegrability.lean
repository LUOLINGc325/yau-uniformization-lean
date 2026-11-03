import Yau.Proofs.D02PhysicalWeighted
import Yau.Proofs.D02PullbackPositive
import Yau.Proofs.D02DualCauchy
import Yau.Proofs.D03

/-! Applying the exact original D03 to the actual pullback tangent bundle.
The energy and actual u bound are the preceding physical estimates in the
source argument; no choice of curvature, frame, or measure is supplied. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal Bundle
open MeasureTheory
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

theorem physicalCurve_extraIntegrability {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {B : ComplexManifold 1} (h : ℂ → Pt X)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ puncturedUnitDisc, immersionDifferentialNormSq X.metric.form F (h z) ≤ C)
    (henergy : (∫⁻ z in puncturedUnitDisc, ENNReal.ofReal
      (hermitianNormSq (X.metric.form (h z)) (physicalCurveDerivative h z)) ∂volume) < ⊤) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < σ ∧ physicalWeightedEnergy X.metric.form h ρ σ < ⊤ := by
  let f := puncturedCurveMap h hh c hc
  let E := tangentPullbackFiber f
  let k := tangentPullbackMetric X.metric.form f
  let A := tangentPullbackMap F f
  let s := puncturedDerivativeSection h hh c hc
  have hk : BundleDbar.SmoothMetric (r := n) E k := tangentPullbackMetric_smooth X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) f
  have hBound : BundlePresentation.BoundedMap E k A :=
    tangentPullbackMap_bounded X.metric.form F f hC
      (fun x => hbound (c x) (Yau.Proofs.B01Aux.disc_mem c hc x))
  have hsInt : BundlePresentation.sectionIntegral E c k s < ⊤ := by
    rw [puncturedDerivativeSection_integral X.metric.form h hh c hc]
    exact henergy
  obtain ⟨ρ, σ, hρ0, hρ1, hσ0, hExtra⟩ :=
    Yau.NodeProofs.D03_proved B c hc n N E k A (tangentPullback_holomorphic f) hk
      (tangentPullbackMetric_griffithsNonnegative X f) (tangentPullbackMap_holomorphic hF f)
      (tangentPullbackMap_pointwiseInjective hImm f) hBound s
      (puncturedDerivativeSection_holomorphic h hh c hc) hsInt
  refine ⟨ρ, σ, hρ0, hρ1, hσ0, ?_⟩
  rw [puncturedDerivativeSection_weightedIntegral X.metric.form h hh c hc ρ σ hρ1.le] at hExtra
  exact hExtra

end Yau.NodeProofs.D02Aux
