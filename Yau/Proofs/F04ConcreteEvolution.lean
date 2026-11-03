import Yau.Proofs.F04IntrinsicEnergy

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements

/-- The concrete actual V/J/B evolution remains available before any
 source or chart is chosen. This exposes the already constructed supported
 energy witness needed by subsequent genuine chart transport. -/
theorem flow_dirichlet_evolution_output
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S : ℝ} (hS : 0 < S) :
    ∃ (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ]
        EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (C shift E : ℝ),
      IntrinsicFormBinding X.metric.form μ Ω h S C (1/2) shift
        (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B ∧
      VariationalEvolutionOutput μ Ω S E (dirichletL2 X.metric μ hμ Ω) B := by
  letI := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite X.metric μ hμ
  letI : IsFiniteMeasure (μ.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono hΩK) hK.measure_lt_top)⟩
  let V := DirichletEnergy X.metric μ hμ Ω
  letI : NormedAddCommGroup V := inferInstance
  letI : InnerProductSpace ℝ V := inferInstance
  letI : CompleteSpace V := dirichletEnergy_completeSpace X.metric μ hμ Ω
  letI : SeparableSpace V := dirichletEnergy_separable_on_finite_domain X.metric X.kahler_metric μ hμ Ω hΩ.measurableSet
  let j : V →L[ℝ] FixedPivot μ Ω := dirichletL2 X.metric μ hμ Ω
  have hj : ‖j‖ ≤ 1 := by
    apply j.opNorm_le_bound zero_le_one
    intro v
    simpa only [one_mul] using dirichletL2_norm_le X.metric μ hμ Ω v
  have hH10 := scalarH10Binding X.metric X.kahler_metric μ hμ Ω hΩ
  obtain ⟨B,C,shift,hForm,hProduct,hContinuous⟩ :=
    flow_intrinsic_form_profiles X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS
  have hGlobal : ∀ t, ‖B t‖ ≤ C := fun t =>
    (B t).opNorm_le_bound₂ hForm.1.le (hProduct t)
  obtain ⟨E,hEvolution⟩ := variationalEvolutionOutput_of_constructed_form μ Ω hS hForm.1.le
    hForm.2.1 hForm.2.2.1 j hj hH10.1
    (dirichletL2_denseRange X.metric μ hμ Ω hΩ) B hGlobal hContinuous
    (fun t ht => (hForm.2.2.2.2 t ht).2.1)
  exact ⟨B,C,shift,E,hForm,hEvolution⟩

end Yau.F04Proof
