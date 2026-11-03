import Yau.Proofs.F04AmbientEnergy
import Yau.Proofs.F04NonnegativeCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Actual globally nonnegative compact smooth cores approximate every
nonnegative element of the ambient scalar energy completion. -/
theorem exists_nonnegative_scalarEnergyDomain_tendsto
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    ∃ f : ℕ → ScalarEnergyDomain g μ hμ,
      (∀ j x, 0 ≤ f j x) ∧
      Tendsto (fun j => (f j : ScalarEnergySpace g μ hμ)) atTop (𝓝 q) := by
  let v := scalarEnergyUnivEquiv g μ hμ q
  have hv : ∀ᵐ x ∂μ.restrict Set.univ, 0 ≤ dirichletL2 g μ hμ Set.univ v x := by
    filter_upwards [ae_restrict_of_ae (dirichletL2_univ_ae g μ hμ q),
      ae_restrict_of_ae hq] with x hx hp
    exact hx.symm ▸ hp
  obtain ⟨fs, hfn, hfs⟩ := exists_nonnegative_dirichletCore_tendsto
    g hK μ hμ Set.univ MeasurableSet.univ v hv
  refine ⟨fun j => (fs j).val, hfn, ?_⟩
  exact ((dirichletEnergySubmodule g μ hμ Set.univ).subtypeL.continuous.tendsto v).comp hfs

end Yau.F04Proof
