import Yau.Proofs.F04EnergyRestriction

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The narrow inclusion comes directly from the literal supported closed
submodule of the original scalar energy completion. -/
def dirichletUnivInclusion (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ Set.univ :=
  (scalarEnergyUnivEquiv g μ hμ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (dirichletEnergySubmodule g μ hμ O).subtypeL

theorem dirichletUnivInclusion_norm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u : DirichletEnergy g μ hμ O) : ‖dirichletUnivInclusion g μ hμ O u‖ = ‖u‖ :=
  (scalarEnergyUnivEquiv g μ hμ).norm_map u.val

theorem dirichletUnivInclusion_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u : DirichletEnergy g μ hμ O) :
    (dirichletL2 g μ hμ Set.univ (dirichletUnivInclusion g μ hμ O u) : M.Carrier → ℝ)
      =ᵐ[μ] scalarEnergyL2 g μ hμ u.val :=
  dirichletL2_univ_ae g μ hμ u.val

theorem dirichletUnivInclusion_D (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u : DirichletEnergy g μ hμ O) :
    formMeasureRestriction g (μ.restrict Set.univ) (μ.restrict O)
      (by simpa only [Measure.restrict_univ] using Measure.restrict_le_self)
      (dirichletD g μ hμ Set.univ (dirichletUnivInclusion g μ hμ O u)) =
      dirichletD g μ hμ O u :=
  scalarEnergyD_restrict_univ g μ hμ O u.val

end Yau.F04Proof
