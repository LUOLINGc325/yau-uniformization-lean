import Yau.Proofs.D02ImmersionBoundary
import Yau.Proofs.D02DiscMaximum

/-! The same actual F, u and ψ have three constants selected before every
varying disc in the original compact-boundary family. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem uniformImmersionConstants {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ B_F B_u B_ψ : ℝ, 0 < B_F ∧ 0 < B_u ∧ 0 < B_ψ ∧
      ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
        (∀ ζ : ℂ, ‖ζ‖ = 1 → f ζ ∈ K) → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
          ‖F (f ζ)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (f ζ) ≤ B_u ∧
            immersionPotential X.metric.form F (f ζ) ≤ B_ψ := by
  have hg := L12Aux.metricSmooth_of_smoothMetric X.metric
  obtain ⟨B_F, hBF, hFbound⟩ := immersion_uniformDisc_bound hF hK
  obtain ⟨B_u, hBu, hubound⟩ := smoothLevi_uniformDisc_bound
    (immersionDifferentialNormSq_smooth X.metric.form hg hF)
    (immersionDifferentialNormSq_levi_posSemidef X hF) hK
  obtain ⟨B_ψ, hBψ, hψbound⟩ := smoothLevi_uniformDisc_bound
    (immersionPotential_smooth X.metric.form hg hF hImm)
    (immersionPotential_levi_posSemidef X hF hImm) hK
  exact ⟨B_F, B_u, B_ψ, hBF, hBu, hBψ, fun f hf hb ζ hζ =>
    ⟨hFbound f hf hb ζ hζ, hubound f hf hb ζ hζ, hψbound f hf hb ζ hζ⟩⟩

end Yau.NodeProofs.D02Aux
