import Yau.Proofs.F03DirichletStepDomination
import Yau.Proofs.F03ResolventOrder
import Yau.Proofs.F03OrderPowers
import Yau.Proofs.F03ExhaustionEuler

/-! Actual supported heat is dominated by native ambient heat via genuine Euler powers. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletHeat_le_ambient (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    l2ZeroExtension μ Ω hΩ.measurableSet
      (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f)) ≤ scalarHeatFamily g μ hμ t f := by
  have heuler : ∀ k : ℕ, l2ZeroExtension μ Ω hΩ.measurableSet
      (dirichletHeatEuler g μ hμ Ω t ht k (l2Restriction μ Ω f)) ≤ scalarHeatEuler g μ hμ t ht k f := by
    intro k
    have hh := div_pos ht (scalarEulerCount_cast_pos k)
    let A := dirichletAmbientStep g μ hμ Ω hΩ.measurableSet (t/scalarEulerCount k) hh
    let B := scalarResolvent g μ hμ (t/scalarEulerCount k) hh
    have hAB : ∀ v : Lp ℝ 2 μ, 0 ≤ v → A v ≤ B v := by
      intro v hv
      exact l2_le_of_ae μ _ _ (dirichletAmbientStep_le_scalarResolvent g hK μ hμ Ω hΩ hh v
        ((Lp.coeFn_nonneg _).mpr hv))
    have hB : ∀ v : Lp ℝ 2 μ, 0 ≤ v → 0 ≤ B v := by
      intro v hv
      exact (Lp.coeFn_nonneg _).mp (scalarResolvent_nonneg g μ hμ hh v ((Lp.coeFn_nonneg _).mpr hv))
    have hp := l2_powers_le_of_step μ A B (dirichletAmbientStep_monotone g μ hμ Ω hΩ.measurableSet hh)
      hB hAB (scalarEulerCount k) f hf
    simpa only [A,B,dirichletHeatEuler_ambient_eq,scalarHeatEuler] using hp
  have hlim := ((l2ZeroExtension μ Ω hΩ.measurableSet).continuous.tendsto
    (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f))).comp
      (dirichletHeat_euler_apply_tendsto g μ hμ Ω t ht (l2Restriction μ Ω f))
  exact le_of_tendsto_of_tendsto hlim (scalarHeatFamily_euler_apply_tendsto g μ hμ t ht f)
    (Eventually.of_forall heuler)

end Yau.Proofs.F03Aux
