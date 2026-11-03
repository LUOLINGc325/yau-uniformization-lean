import Yau.Proofs.F04EnergyRepresentatives

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletCore_scalarEnergyClosure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : dirichletCore g μ hμ O) :
    ScalarEnergyClosure g.form μ O f.val (scalarExterior f.val) := by
  have hf := dirichletCore_scalarL2 g μ hμ O f
  have hdf := scalarExterior_l2_restrict g μ hμ O f.val.2.1 f.val.2.2
  apply (scalarEnergyClosure_iff g μ hμ O f.val (scalarExterior f.val) hf hdf).mpr
  exact ⟨dirichletCoreToEnergy g μ hμ O f,
    dirichletL2_core_eq_scalarToLp g μ hμ O f hf, dirichletD_core g μ hμ O f⟩

theorem energyRepresentative_core (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (f : dirichletCore g μ hμ O) :
    energyRepresentative g μ hμ O f.val (scalarExterior f.val) = dirichletCoreEmbedding g μ hμ O f := by
  have hc := dirichletCore_scalarEnergyClosure g μ hμ O f
  apply energyRepresentative_eq g hK μ hμ O hO f.val (scalarExterior f.val) hc
  exact dirichletL2_core_eq_scalarToLp g μ hμ O f hc.1

theorem scalarTest_energyClosure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : M.Carrier → ℝ) (hf : ScalarTest O f) :
    MemLp f 2 (μ.restrict O) ∧ ∃ df, SmoothRealForm df ∧
      RepresentsExterior (scalarZeroForm f) df ∧ ScalarEnergyClosure g.form μ O f df := by
  let cf : dirichletCore g μ hμ O := ⟨⟨f, hf.1, hf.2.1⟩, hf.2.2⟩
  refine ⟨(scalarL2_iff_memLp _ _).mp (dirichletCore_scalarL2 g μ hμ O cf),
    scalarExterior f, scalarExterior_smooth hf.1, scalarExterior_represents hf.1, ?_⟩
  exact dirichletCore_scalarEnergyClosure g μ hμ O cf

theorem energyRepresentative_core_dense (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) :
    Dense {v : DirichletEnergy g μ hμ O | ∃ f df,
      ScalarTest O f ∧ SmoothRealForm df ∧ RepresentsExterior (scalarZeroForm f) df ∧
      ScalarEnergyClosure g.form μ O f df ∧ v = energyRepresentative g μ hμ O f df} := by
  apply (dirichletCoreEmbedding_denseRange g μ hμ O).mono
  rintro v ⟨f, rfl⟩
  exact ⟨f.val, scalarExterior f.val, ⟨f.val.2.1, f.val.2.2, f.property⟩,
    scalarExterior_smooth f.val.2.1, scalarExterior_represents f.val.2.1,
    dirichletCore_scalarEnergyClosure g μ hμ O f,
    (energyRepresentative_core g hK μ hμ O hO f).symm⟩

end Yau.F04Proof
