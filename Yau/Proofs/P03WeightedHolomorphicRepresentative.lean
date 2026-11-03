import Yau.Proofs.P03WeakTopRepresentative

open scoped Manifold Topology ContDiff
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The representative is one intrinsic global tensor and retains every
original weighted norm, including weights with singularities. -/
theorem weakDbar_zero_weighted_holomorphic_representative
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hE : Holomorphic (r := r) E)
    (u : NQForm E 0) (hu : WeakDbar (r := r) E u (zeroForm E 1)) :
    ∃ v : NQForm E 0, HolomorphicTopForm (r := r) E v ∧
      (∀ᵐ x ∂μ, v x = u x) ∧
      ∀ (h : Metric E) (φ : M.Carrier → ℝ),
        weightedNormSq (r := r) E g.form h μ φ v =
          weightedNormSq (r := r) E g.form h μ φ u ∧
        (WeightedL2 (r := r) E g.form h μ φ u →
          WeightedL2 (r := r) E g.form h μ φ v) := by
  obtain ⟨v, hv, heq⟩ := weakDbar_zero_holomorphic_top_representative E g μ hμ hE u hu
  refine ⟨v, hv, heq, ?_⟩
  intro h φ
  exact ⟨weightedNormSq_congr_ae E g.form h μ φ v u heq,
    fun hL2 => weightedL2_of_ae_eq E g μ hμ h φ u v hL2 (heq.mono fun _ hx => hx.symm)⟩

end Yau.NodeProofs.P03Aux
