import Yau.Proofs.F04DirichletCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarEnergy_mem_dirichlet_univ (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (q : ScalarEnergySpace g μ hμ) :
    q ∈ dirichletEnergySubmodule g μ hμ Set.univ := by
  change q ∈ closure ((dirichletCore g μ hμ Set.univ).map
    (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ]
      ScalarEnergySpace g μ hμ).toLinearMap : Set (ScalarEnergySpace g μ hμ))
  apply closure_mono _ (UniformSpace.Completion.denseRange_coe q)
  rintro _ ⟨f, rfl⟩
  exact ⟨f, Set.subset_univ _, rfl⟩

/-- The supported space for the whole manifold is the original scalar energy
completion, with its actual norm. -/
def scalarEnergyUnivEquiv (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    ScalarEnergySpace g μ hμ ≃ₗᵢ[ℝ] DirichletEnergy g μ hμ Set.univ where
  toFun q := ⟨q, scalarEnergy_mem_dirichlet_univ g μ hμ q⟩
  invFun q := q.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

theorem dirichletL2_univ_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (q : ScalarEnergySpace g μ hμ) :
    (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ q) : M.Carrier → ℝ)
      =ᵐ[μ] scalarEnergyL2 g μ hμ q := by
  change restrictL2 μ Set.univ (scalarEnergyL2 g μ hμ q) =ᵐ[μ] scalarEnergyL2 g μ hμ q
  simpa only [Measure.restrict_univ] using
    restrictL2_coe μ Set.univ (scalarEnergyL2 g μ hμ q)

end Yau.F04Proof
