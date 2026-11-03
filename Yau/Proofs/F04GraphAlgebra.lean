import Yau.Proofs.F04GraphLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarEnergyClosure_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {f v : M.Carrier → ℝ} {df dv : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (hv : ScalarEnergyClosure g.form μ O v dv) :
    ScalarEnergyClosure g.form μ O (f + v) (df + dv) := by
  have hfv := scalarL2_add hf.1 hv.1
  have hdfv := l2RealForm_add g (μ.restrict O) df dv hf.2.1 hv.2.1
  have hfs := energyRepresentative_spec g μ hμ O f df hf
  have hvs := energyRepresentative_spec g μ hμ O v dv hv
  apply (scalarEnergyClosure_iff g μ hμ O (f + v) (df + dv) hfv hdfv).mpr
  refine ⟨energyRepresentative g μ hμ O f df + energyRepresentative g μ hμ O v dv, ?_, ?_⟩
  · simpa only [map_add, hfs.1, hvs.1] using (scalarToLp_add hf.1 hv.1 hfv).symm
  · simpa only [map_add, hfs.2, hvs.2] using
      (realize_section_add g (μ.restrict O) df dv hf.2.1 hv.2.1 hdfv).symm

theorem scalarEnergyClosure_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {f : M.Carrier → ℝ} {df : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (c : ℝ) :
    ScalarEnergyClosure g.form μ O (c • f) (c • df) := by
  have hcf := scalarL2_smul hf.1 c
  have hcdf := l2RealForm_smul g (μ.restrict O) c df hf.2.1
  have hfs := energyRepresentative_spec g μ hμ O f df hf
  apply (scalarEnergyClosure_iff g μ hμ O (c • f) (c • df) hcf hcdf).mpr
  refine ⟨c • energyRepresentative g μ hμ O f df, ?_, ?_⟩
  · simpa only [map_smul, hfs.1] using (scalarToLp_smul hf.1 c hcf).symm
  · simpa only [map_smul, hfs.2] using
      (realize_section_smul g (μ.restrict O) c df hf.2.1 hcdf).symm

theorem energyRepresentative_add (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    {f v : M.Carrier → ℝ} {df dv : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (hv : ScalarEnergyClosure g.form μ O v dv) :
    energyRepresentative g μ hμ O (f + v) (df + dv) =
      energyRepresentative g μ hμ O f df + energyRepresentative g μ hμ O v dv := by
  have hsum := scalarEnergyClosure_add g μ hμ O hf hv
  apply energyRepresentative_eq g hK μ hμ O hO (f + v) (df + dv) hsum
  simpa only [map_add, (energyRepresentative_spec g μ hμ O f df hf).1,
    (energyRepresentative_spec g μ hμ O v dv hv).1] using (scalarToLp_add hf.1 hv.1 hsum.1).symm

theorem energyRepresentative_smul (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    {f : M.Carrier → ℝ} {df : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (c : ℝ) :
    energyRepresentative g μ hμ O (c • f) (c • df) = c • energyRepresentative g μ hμ O f df := by
  have hsmul := scalarEnergyClosure_smul g μ hμ O hf c
  apply energyRepresentative_eq g hK μ hμ O hO (c • f) (c • df) hsmul
  simpa only [map_smul, (energyRepresentative_spec g μ hμ O f df hf).1] using
    (scalarToLp_smul hf.1 c hsmul.1).symm

theorem energyRepresentative_surjective (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (v : DirichletEnergy g μ hμ O) :
    ∃ f df, ScalarEnergyClosure g.form μ O f df ∧ energyRepresentative g μ hμ O f df = v := by
  obtain ⟨f, df, _, _, hc, hJ, _⟩ := dirichletEnergy_representatives g μ hμ O v
  exact ⟨f, df, hc, energyRepresentative_eq g hK μ hμ O hO f df hc v hJ⟩

end Yau.F04Proof
