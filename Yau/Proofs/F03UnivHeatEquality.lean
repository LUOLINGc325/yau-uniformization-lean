import Yau.Proofs.F03ExhaustionEuler
import Yau.Proofs.F04AmbientEnergy

/-! The constructed whole-domain heat is the native scalar variational heat. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau F04Proof LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletStepResolventEnergy_univ (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) :
    (dirichletStepResolventEnergy g μ hμ Set.univ h hh (l2Restriction μ Set.univ f)).val=
      scalarResolventEnergy g μ hμ h hh f := by
  apply scalarResolventEnergy_unique g μ hμ h hh f
  intro v
  have he := dirichlet_step_ambient_equation g μ hμ Set.univ MeasurableSet.univ hh f
    (scalarEnergyUnivEquiv g μ hμ v)
  rw [scalarResolventForm_apply] at he
  exact he

theorem dirichletAmbientStep_univ (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) {h : ℝ} (hh : 0 < h) :
    dirichletAmbientStep g μ hμ Set.univ MeasurableSet.univ h hh=scalarResolvent g μ hμ h hh := by
  ext f
  rw [dirichletAmbientStep_eq_energy,dirichletStepResolventEnergy_univ]
  rfl

theorem dirichletHeatEuler_univ (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (t : ℝ) (ht : 0 < t) (k : ℕ) (f : Lp ℝ 2 μ) :
    l2ZeroExtension μ Set.univ MeasurableSet.univ
      (dirichletHeatEuler g μ hμ Set.univ t ht k (l2Restriction μ Set.univ f))=
      scalarHeatEuler g μ hμ t ht k f := by
  rw [dirichletHeatEuler_ambient_eq,dirichletAmbientStep_univ]
  rfl

theorem dirichletHeat_univ (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    l2ZeroExtension μ Set.univ MeasurableSet.univ
      (dirichletHeat g μ hμ Set.univ t (l2Restriction μ Set.univ f))=
      scalarHeatFamily g μ hμ t f := by
  have hlim := ((l2ZeroExtension μ Set.univ MeasurableSet.univ).continuous.tendsto
    (dirichletHeat g μ hμ Set.univ t (l2Restriction μ Set.univ f))).comp
      (dirichletHeat_euler_apply_tendsto g μ hμ Set.univ t ht (l2Restriction μ Set.univ f))
  simp only [Function.comp_def,dirichletHeatEuler_univ] at hlim
  exact tendsto_nhds_unique hlim (scalarHeatFamily_euler_apply_tendsto g μ hμ t ht f)

end Yau.Proofs.F03Aux
