import Yau.Proofs.F04DirichletCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletEnergy_representatives (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (v : DirichletEnergy g μ hμ O) :
    ∃ (f : M.Carrier → ℝ) (df : RealForm M 1) (hf : ScalarL2 (μ.restrict O) f)
      (hdf : L2RealForm g.form (μ.restrict O) df),
      ScalarEnergyClosure g.form μ O f df ∧ dirichletL2 g μ hμ O v = scalarToLp hf ∧
        dirichletD g μ hμ O v = realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection df hdf) := by
  let f : M.Carrier → ℝ := dirichletL2 g μ hμ O v
  have hf : ScalarL2 (μ.restrict O) f :=
    (scalarL2_iff_memLp _ _).mpr (Lp.memLp (dirichletL2 g μ hμ O v))
  have hJ : dirichletL2 g μ hμ O v = scalarToLp hf := by
    apply Lp.ext
    filter_upwards [scalarToLp_coe hf] with x hx
    exact hx.symm
  obtain ⟨df, hdf, hD⟩ := l2FormHilbert_exists_section g (μ.restrict O) (dirichletD g μ hμ O v)
  refine ⟨f, df, hf, hdf, ?_, hJ, hD.symm⟩
  exact (scalarEnergyClosure_iff g μ hμ O f df hf hdf).mpr ⟨v, hJ, hD.symm⟩

/-- This map is selected from the literal actual scalar d-graph, rather
than from independent function or gradient data. -/
def energyRepresentative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : M.Carrier → ℝ) (df : RealForm M 1) : DirichletEnergy g μ hμ O := by
  classical
  exact if hc : ScalarEnergyClosure g.form μ O f df then
    Classical.choose ((scalarEnergyClosure_iff g μ hμ O f df hc.1 hc.2.1).mp hc) else 0

theorem energyRepresentative_spec (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : M.Carrier → ℝ) (df : RealForm M 1) (hc : ScalarEnergyClosure g.form μ O f df) :
    dirichletL2 g μ hμ O (energyRepresentative g μ hμ O f df) = scalarToLp hc.1 ∧
      dirichletD g μ hμ O (energyRepresentative g μ hμ O f df) =
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection df hc.2.1) := by
  classical
  unfold energyRepresentative
  rw [dite_eq_left hc]
  exact Classical.choose_spec ((scalarEnergyClosure_iff g μ hμ O f df hc.1 hc.2.1).mp hc)

theorem energyRepresentative_eq (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    (f : M.Carrier → ℝ) (df : RealForm M 1) (hc : ScalarEnergyClosure g.form μ O f df)
    (v : DirichletEnergy g μ hμ O) (hv : dirichletL2 g μ hμ O v = scalarToLp hc.1) :
    energyRepresentative g μ hμ O f df = v := by
  apply dirichletL2_injective g hK μ hμ O hO
  exact (energyRepresentative_spec g μ hμ O f df hc).1.trans hv.symm

end Yau.F04Proof
