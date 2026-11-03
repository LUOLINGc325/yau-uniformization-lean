import Yau.Proofs.F03DirichletEnergy

/-! Actual supported smooth core sequences for the closed energy space. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_dirichletCore_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (v : DirichletEnergy g μ hμ O) :
    ∃ fs : ℕ → dirichletCore g μ hμ O,
      Tendsto (fun j => dirichletCoreToEnergy g μ hμ O (fs j)) atTop (𝓝 v) := by
  classical
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp v.property
  have hseq : ∀ j, ∃ f : ScalarEnergyDomain g μ hμ,
      f ∈ dirichletCore g μ hμ O ∧ (f : ScalarEnergySpace g μ hμ) = s j := by
    intro j
    exact hs j
  choose fs hfs heq using hseq
  refine ⟨fun j => ⟨fs j, hfs j⟩, tendsto_subtype_rng.mpr ?_⟩
  convert hlim using 1
  funext j
  exact heq j

end Yau.Proofs.F03Aux
