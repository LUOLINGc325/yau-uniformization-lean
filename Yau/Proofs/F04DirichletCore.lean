import Yau.Proofs.F03DirichletClosure

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual supported smooth core embeds into the certified common
energy space, using its original scalar energy completion. -/
def dirichletCoreEmbedding (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    dirichletCore g μ hμ O →ₗ[ℝ] DirichletEnergy g μ hμ O where
  toFun := dirichletCoreToEnergy g μ hμ O
  map_add' f k := by
    apply Subtype.ext
    change ((f.val + k.val : ScalarEnergyDomain g μ hμ) : ScalarEnergySpace g μ hμ) =
      (f.val : ScalarEnergySpace g μ hμ) + (k.val : ScalarEnergySpace g μ hμ)
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c f := by
    apply Subtype.ext
    change ((c • f.val : ScalarEnergyDomain g μ hμ) : ScalarEnergySpace g μ hμ) =
      c • (f.val : ScalarEnergySpace g μ hμ)
    exact UniformSpace.Completion.coe_smul _ _

theorem dirichletCoreEmbedding_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    DenseRange (dirichletCoreEmbedding g μ hμ O) := by
  intro v
  obtain ⟨fs, hfs⟩ := exists_dirichletCore_tendsto g μ hμ O v
  apply mem_closure_of_tendsto hfs
  exact Filter.Eventually.of_forall (fun j => ⟨fs j, rfl⟩)

theorem dirichletCoreEmbedding_norm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : dirichletCore g μ hμ O) :
    ‖dirichletCoreEmbedding g μ hμ O f‖ = ‖f.val‖ := by
  change ‖(f.val : ScalarEnergySpace g μ hμ)‖ = ‖f.val‖
  exact UniformSpace.Completion.norm_coe _

end Yau.F04Proof
