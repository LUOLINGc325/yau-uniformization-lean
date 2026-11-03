import Yau.Proofs.D02SmoothPsh
import Yau.Proofs.D02DiscLevi

/-! The actual disc potentials satisfy the original coordinate-domain psh
predicate on the open unit disc used for D04 extraction. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem smoothLevi_holomorphicPullback_isPshOn {m n : ℕ} {M : ComplexManifold n}
    {D : Set (ComplexVector m)} (hD : IsOpen D)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    (f : ComplexVector m → M.Carrier)
    (hf : ContMDiffOn (ComplexModel m) (ComplexModel n) ∞ f D) :
    IsPshOn (fun z => (u (f z) : EReal)) D := by
  apply isPshOn_of_complexLinePshOn
  apply P02Aux.complexLinePshOn_of_lower_supports D (fun z => u (f z))
  · intro z hz
    exact (smoothLevi_holomorphicPullback hD u hu hL f hf z hz).1.continuousAt.continuousWithinAt
  · intro z hz
    obtain ⟨hc, hpos⟩ := smoothLevi_holomorphicPullback hD u hu hL f hf z hz
    exact ⟨fun w => u (f w), hc, rfl, Filter.Eventually.of_forall (fun _ => le_rfl), hpos⟩

theorem smoothLevi_disc_isPshOn {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    IsPshOn (fun z => (u (discModelMap f z) : EReal)) (Metric.ball (0 : ComplexVector 1) 1) :=
  smoothLevi_holomorphicPullback_isPshOn Metric.isOpen_ball u hu hL (discModelMap f)
    (discModelMap_contMDiffOn hf)

theorem immersionPotential_disc_isPshOn {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {f : ℂ → Pt X} (hf : IsHolomorphicDisc f) :
    IsPshOn (fun z => (immersionPotential X.metric.form F (discModelMap f z) : EReal))
      (Metric.ball (0 : ComplexVector 1) 1) :=
  smoothLevi_disc_isPshOn (immersionPotential_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
    (immersionPotential_levi_posSemidef X hF hImm) hf

theorem immersionDifferentialNormSq_disc_isPshOn {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F)
    {f : ℂ → Pt X} (hf : IsHolomorphicDisc f) :
    IsPshOn (fun z => (immersionDifferentialNormSq X.metric.form F (discModelMap f z) : EReal))
      (Metric.ball (0 : ComplexVector 1) 1) :=
  smoothLevi_disc_isPshOn (immersionDifferentialNormSq_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF)
    (immersionDifferentialNormSq_levi_posSemidef X hF) hf

end Yau.NodeProofs.D02Aux
