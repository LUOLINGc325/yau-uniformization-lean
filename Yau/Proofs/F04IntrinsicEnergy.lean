import Yau.Proofs.F04IntrinsicFormProfiles
import Yau.Proofs.F04VariationalEvolution
import Yau.Proofs.F04EnergySeparability
import Yau.Proofs.F03DirichletDensity

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements

/-- The original intrinsic-energy producer: the actual supported scalar graph,
 true fixed-volume nonsymmetric form, and actual zero-initial evolution are
 all constructed from the same supplied localized flow. -/
theorem flow_intrinsic_energy_target
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X) :
    IntrinsicEnergyTarget X o h U P ρ := by
  intro hloc μ hμ O hO T hT
  letI := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite X.metric μ hμ
  letI : IsFiniteMeasure (μ.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono subset_closure) hO.2.2.2.1.measure_lt_top)⟩
  let V := DirichletEnergy X.metric μ hμ O
  letI : NormedAddCommGroup V := inferInstance
  letI : InnerProductSpace ℝ V := inferInstance
  letI : CompleteSpace V := dirichletEnergy_completeSpace X.metric μ hμ O
  letI : SeparableSpace V := dirichletEnergy_separable_on_finite_domain X.metric X.kahler_metric μ hμ O hO.1.measurableSet
  let j : V →L[ℝ] FixedPivot μ O := dirichletL2 X.metric μ hμ O
  let e := energyRepresentative X.metric μ hμ O
  have hH10 : ScalarH10Binding X.metric.form μ O j e :=
    scalarH10Binding X.metric X.kahler_metric μ hμ O hO.1
  have hj : ‖j‖ ≤ 1 := by
    apply j.opNorm_le_bound zero_le_one
    intro v
    simpa only [one_mul] using dirichletL2_norm_le X.metric μ hμ O v
  have hjd : DenseRange j := dirichletL2_denseRange X.metric μ hμ O hO.1
  obtain ⟨B, C, shift, hForm, hProduct, hContinuous⟩ :=
    flow_intrinsic_form_profiles X o h U P ρ hloc μ hμ O (closure O) hO.1 hO.2.2.2.1 subset_closure hT
  have hGlobal : ∀ t, ‖B t‖ ≤ C := by
    intro t
    exact (B t).opNorm_le_bound₂ hForm.1.le (hProduct t)
  obtain ⟨E, hEvolution⟩ := variationalEvolutionOutput_of_constructed_form μ O hT hForm.1.le
    hForm.2.1 hForm.2.2.1 j hj hH10.1 hjd B hGlobal hContinuous
    (fun t ht => (hForm.2.2.2.2 t ht).2.1)
  exact ⟨V, inferInstance, inferInstance, inferInstance, j, e, B, C, (1 / 2 : ℝ), shift, E, hH10, hForm, hEvolution⟩

end Yau.F04Proof
