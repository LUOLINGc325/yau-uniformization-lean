import Yau.Proofs.V02WallTaylorIncrementSmooth

/-! A genuine common open domain for both literal cleared increments. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

def nativeIncrementDomain (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (x : Pt X) (A : CotangentCoord n) (δ R : ℝ) : Set (ℂ × ChartFactorAux n b) :=
  chartFactorDomain Ψ (fun u => wallPower d j a (cotangentChartInv x u)) x A δ R ∩
    (fun p : ℂ × ChartFactorAux n b => (p.2.1,
      (‖wallPower d j a (cotangentChartInv x p.2.1) • chartFactorDirection p‖,
        (|chartBaseFactor d j a Ψ x p|, |chartFiberFactor d j a Ψ x p|)))) ⁻¹'
      (Metric.ball A δ ×ˢ (Set.Iio (R / 2) ×ˢ (Set.Iio (1 / 2) ×ˢ Set.Iio (1 / 2))))

theorem isOpen_nativeIncrementDomain {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {x : Pt X} {A : CotangentCoord n} {δ R : ℝ}
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R)) :
    IsOpen (nativeIncrementDomain d j a Ψ x A δ R) := by
  let m : CotangentCoord n → ℝ := fun u => wallPower d j a (cotangentChartInv x u)
  have hm : ContDiffOn ℝ ∞ m (Metric.ball A (2 * δ)) :=
    (wallPower_chart_contDiffOn hd j a x).mono hvalid
  have hdom := isOpen_chartFactorDomain hΨ hm
  have hm' : ContinuousOn (fun p : ℂ × ChartFactorAux n b => m p.2.1)
      (chartFactorDomain Ψ m x A δ R) :=
    hm.continuousOn.comp (continuous_fst.comp continuous_snd).continuousOn (fun _ hp => hp.1)
  have hb := (chartSprayFactor_contDiffOn hΨ (B := fun y => deltaBase d j y.1)
    (deltaBase_chart_contDiffOn hd j x) hm).continuousOn.abs
  have hf := (chartSprayFactor_contDiffOn hΨ (B := deltaFiber d j)
    (deltaFiber_chart_contDiffOn hd j x) hm).continuousOn.abs
  have ht := (hm'.smul chartFactorDirection_contDiff.continuous.continuousOn).norm
  exact ((continuous_fst.comp continuous_snd).continuousOn.prodMk
    (ht.prodMk (hb.prodMk hf))).isOpen_inter_preimage hdom
      (isOpen_ball.prod (isOpen_Iio.prod (isOpen_Iio.prod isOpen_Iio)))

theorem native_wall_increments_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ChartFactorAux n b =>
      nativeInverseIncrement d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2))
      (nativeIncrementDomain d j a Ψ x A δ R) ∧
    ContDiffOn ℝ ∞ (fun p : ℂ × ChartFactorAux n b =>
      nativeLogIncrement d j a Ψ (cotangentChartInv x p.2.1) (p.1, p.2.2))
      (nativeIncrementDomain d j a Ψ x A δ R) := by
  constructor <;> intro p hp
  · exact (native_wall_increments_contDiffAt hd j a ha hzero x hδ hR hvalid hΨ hsource
      hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2).1.contDiffWithinAt
  · exact (native_wall_increments_contDiffAt hd j a ha hzero x hδ hR hvalid hΨ hsource
      hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2).2.contDiffWithinAt

end Yau.Blueprint.V02WallTaylorProof
