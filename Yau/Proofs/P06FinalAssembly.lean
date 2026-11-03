import Yau.Proofs.P06FinalAssemblyVolumes
import Yau.Proofs.P06Geometry
import Yau.Proofs.P06HodgeResolvent
import Yau.Proofs.P06PDETypeTrace
import Yau.Proofs.P06L2HeatExistence
import Yau.Proofs.P06BoundedOrderAssembly
import Yau.Proofs.P06ClosedPotential
import Yau.Proofs.P06ScalarSmoothHeatFromHodge
import Yau.Proofs.P06LipschitzHessianHeat
import Yau.Proofs.G02GluedVolume
import Yau.Blueprint.ConcreteExtensions

/-! Internal final composition of the original P06 conclusions. The
parent supplies the original cutoff construction; no proof is registered
under the final node names here. -/
noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux.FinalAssembly
open Yau Yau.Blueprint
variable {n : ℕ}

theorem hodgeSmoothing_of_cutoffConstruction (X : KahlerManifold n)
    (μ : Measure X.manifold.Carrier) (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ) : HodgeSmoothBoundedTarget X := by
  intro _
  have hg := hodgeGeometry X
  have hh := BoundedOrder.hodgeHeatExistenceUniqueness_of_cutoffConstruction X μ hμ hc
  refine ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hh,
    ScalarSmooth.scalarHeatExistenceUniqueness_of_hodge X hh,
    BoundedOrder.hodgeTypeAndOrder_of_cutoffConstruction X μ hμ hc,
    P06_trace_commutation_proved n X,P06_semigroup_law_proved n X,
    ClosedPotential.closedPotential_of_cutoffConstruction X μ hμ hc,?_⟩
  intro ν hν
  exact ⟨hodgeFormDomain X.metric ν hν,P06_L2_Hodge_heat_proved n X ν hν,
    cutoffConstruction_all_volumes X.metric.form μ hμ hc ν hν⟩

theorem p06_of_cutoffConstruction_at_volume (X : KahlerManifold n)
    (μ : Measure X.manifold.Carrier) (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ) :
    HodgeSmoothBoundedTarget X ∧ LipschitzHessianHeatTarget X :=
  ⟨hodgeSmoothing_of_cutoffConstruction X μ hμ hc,P06_Lipschitz_Hessian_heat_proved n X⟩

/-- The parent's sole remaining internal input gives both unchanged
original P06 clauses, preserving every dimension and all original quantifiers. -/
theorem p06_of_cutoffConstruction (X : KahlerManifold n)
    (hc : ∀ μ, IsRiemannianVolume X.metric.form μ → HodgeCutoffConstruction X.metric.form μ) :
    HodgeSmoothBoundedTarget X ∧ LipschitzHessianHeatTarget X := by
  obtain ⟨μ,hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  exact p06_of_cutoffConstruction_at_volume X μ hμ (hc μ hμ)

theorem p06_of_cutoffConstructions
    (hc : ∀ (n : ℕ) (X : KahlerManifold n) μ,
      IsRiemannianVolume X.metric.form μ → HodgeCutoffConstruction X.metric.form μ) : P06 := by
  intro n X
  exact p06_of_cutoffConstruction X (hc n X)

end Yau.NodeProofs.P06Aux.FinalAssembly
