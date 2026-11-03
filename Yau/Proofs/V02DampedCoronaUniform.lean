import Yau.Proofs.V02CoronaDampingUniform
import Yau.Proofs.V02CoronaBoundaryControl
import Yau.Proofs.V02SpanningCoefficientBounds
import Yau.Proofs.V02SpanningCorona

/-! The same actual damping makes all holomorphic corona coefficients
uniformly bounded on the closed disc and in the original Fourier seminorm. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {X : KahlerManifold n}

def dampedSpanningCorona (P : ℝ) (G : CotangentPoint X.manifold → ComplexVector q)
    (Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint X.manifold) (k : SpanningMinorIndex n q b) (z : ℂ) : ℂ :=
  spanningDamping P G Z f z * spanningCorona G Z f k z

theorem exists_uniform_dampedSpanningCorona
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (E₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ P M₀ D₀ : ℝ, 0 < P ∧ 0 ≤ M₀ ∧ 0 ≤ D₀ ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F.f z ∈ K) →
      ContDiffOn ℂ ∞ (spanningDamping P d.G Z F.f) (Metric.closedBall (0 : ℂ) 1) ∧
      (spanningDamping P d.G Z F.f 0).im = 0 ∧
      0 < (spanningDamping P d.G Z F.f 0).re ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖spanningDamping P d.G Z F.f z‖ ≤ 1) ∧
      boundaryDSq (fun θ (_ : Unit) => spanningDamping P d.G Z F.f (circlePoint θ)) ≤ 1 ∧
      -Real.log (spanningDamping P d.G Z F.f 0).re ≤ η ∧
      circleAverage (fun θ => 1 - ‖spanningDamping P d.G Z F.f (circlePoint θ)‖ ^ 2) ≤ η ∧
      ∀ k : SpanningMinorIndex n q b,
        ContDiffOn ℂ ∞ (dampedSpanningCorona P d.G Z F.f k) (Metric.closedBall (0 : ℂ) 1) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖dampedSpanningCorona P d.G Z F.f k z‖ ≤ M₀) ∧
        boundaryDSq (fun θ (_ : Unit) => dampedSpanningCorona P d.G Z F.f k (circlePoint θ)) ≤
          ENNReal.ofReal D₀ := by
  let ι := SpanningMinorIndex n q b
  obtain ⟨P, B, hP, hB, hαall⟩ := exists_uniform_spanningDamping hd hZ hspan hK E₀ hη
  obtain ⟨M, D, hM, hD, hcoeff⟩ := spanningMinorSigma_uniform_boundary_control hd j hZ hspan E₀
  let M₀ := coronaCoefficientSupBound ι M (Real.sqrt P / 2)
  let D₀ := coronaCoefficientDSqBound ι M D (Real.sqrt P / 2) B
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀, coronaCoefficientSupBound]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀, coronaCoefficientDSqBound]; positivity
  refine ⟨P, M₀, D₀, hP, hM₀, hD₀, fun F hF hE hfK => ?_⟩
  obtain ⟨hα, hphase, hpos, hsup, hDα, hcenter, hloss, hQN, hQD⟩ := hαall j F hF hE hfK
  have ha := fun k => spanningMinor_disc_contDiffOn hd.2.2.2.2.1.1 hZ hF.1 k
  have hσ := fun k => spanningSigma_disc_contDiffOn hd.2.2.2.2.1 hZ hspan hF.1 k
  have hc := coronaSolution_damped_uniform_control ha hσ
    (fun z _ => spanningSigma_sum_eq_one hd.2.2.2.2.1 hspan (F.f z)) hα
    hM hD (by positivity : 0 ≤ Real.sqrt P / 2) hB
    (fun k => (hcoeff F hF hE k).1) (fun k => (hcoeff F hF hE k).2.1)
    (fun k => (hcoeff F hF hE k).2.2.1) (fun k => (hcoeff F hF hE k).2.2.2)
    (fun θ => hsup _ (V03Proof.circlePoint_mem_closedBall θ)) hDα
    (fun i k θ => hQN (i, k) θ) (fun i k => hQD (i, k))
  refine ⟨hα, hphase, hpos, hsup, hDα, hcenter, hloss, fun k => ?_⟩
  exact ⟨hα.mul (spanningCorona_contDiffOn hd.2.2.2.2.1 hZ hspan hF.1 k),
    (hc.2.2 k).1, (hc.2.2 k).2⟩

end Yau.Blueprint.V02Proof
