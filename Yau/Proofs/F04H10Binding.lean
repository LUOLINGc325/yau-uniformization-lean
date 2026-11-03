import Yau.Proofs.F04GraphAlgebra
import Yau.Proofs.F04EnergyPairing
import Yau.Proofs.F04EnergyCoreTests
import spec.WORKPACKAGES.STATEMENTS.MASS.EnergyBindings

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.MassTargetStatements

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- The literal original H10 binding is realized by the certified actual
supported scalar d-graph, its genuine L2 inclusion and its graph representatives. -/
theorem scalarH10Binding (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) :
    ScalarH10Binding g.form μ O (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) := by
  refine ⟨dirichletL2_injective g hK μ hμ O hO.measurableSet,
    scalarTest_energyClosure g μ hμ O, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f df v dv hf hv
    exact energyRepresentative_add g hK μ hμ O hO.measurableSet hf hv
  · intro c f df hf
    exact energyRepresentative_smul g hK μ hμ O hO.measurableSet hf c
  · exact energyRepresentative_surjective g hK μ hμ O hO.measurableSet
  · exact energyRepresentative_coe g μ hμ O
  · intro f df v dv hf hv
    exact energyRepresentative_inner g μ hμ O hf hv
  · intro f df v dv hf hv
    exact energyRepresentative_eq_iff g hK μ hμ O hO.measurableSet hf hv
  · exact energyRepresentative_core_dense g hK μ hμ O hO.measurableSet

end Yau.F04Proof
