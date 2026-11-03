import Yau.Proofs.V02CoronaTraceVector
import Yau.Proofs.V02DampingChoice

/-! A common outer damping for all actual canonical corona corrections on
original discs with fixed compact image and energy bound. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {X : KahlerManifold n}

def spanningDamping (P : ℝ) (G : CotangentPoint X.manifold → ComplexVector q)
    (Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint X.manifold) : ℂ → ℂ :=
  outerDamping P (spanningCorrectionTrace G Z f)

theorem exists_uniform_spanningDamping
    {d : VariationData X q} (hd : VariationSetup d)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (E₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ P B : ℝ, 0 < P ∧ 0 ≤ B ∧ ∀ (j : ℕ) (F : VariationDisc X),
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F.f z ∈ K) →
      ContDiffOn ℂ ∞ (spanningDamping P d.G Z F.f) (Metric.closedBall (0 : ℂ) 1) ∧
      (spanningDamping P d.G Z F.f 0).im = 0 ∧
      0 < (spanningDamping P d.G Z F.f 0).re ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖spanningDamping P d.G Z F.f z‖ ≤ 1) ∧
      boundaryDSq (fun θ (_ : Unit) => spanningDamping P d.G Z F.f (circlePoint θ)) ≤ 1 ∧
      -Real.log (spanningDamping P d.G Z F.f 0).re ≤ η ∧
      circleAverage (fun θ => 1 - ‖spanningDamping P d.G Z F.f (circlePoint θ)‖ ^ 2) ≤ η ∧
      (∀ p θ, ‖spanningDamping P d.G Z F.f (circlePoint θ) *
        spanningCorrectionTrace d.G Z F.f θ p‖ ≤ Real.sqrt P / 2) ∧
      (∀ p, boundaryDSq (fun θ (_ : Unit) => spanningDamping P d.G Z F.f (circlePoint θ) *
        spanningCorrectionTrace d.G Z F.f θ p) ≤ ENNReal.ofReal B) := by
  obtain ⟨B₀, hB₀, hbound⟩ := spanningCorrectionTrace_uniform_bound hd hZ hspan hK E₀
  obtain ⟨P, hP, hPu⟩ := exists_uniform_outerDamping_parameter
    (ι := SpanningMinorIndex n q b × SpanningMinorIndex n q b) hB₀ hη
  refine ⟨P, 20 * B₀, hP, mul_nonneg (by norm_num) hB₀, fun j F hF hE hfK => ?_⟩
  exact hPu (spanningCorrectionTrace d.G Z F.f)
    (spanningCorrectionTrace_contDiff hd.2.2.2.2.1 hZ hspan hF.1)
    (spanningCorrectionTrace_periodic d.G Z F.f) (hbound j F hF hE hfK).1
    (hbound j F hF hE hfK).2

end Yau.Blueprint.V02Proof
