import Yau.Proofs.F03ExhaustionEuler

/-! Actual L2 heat convergence along every original smooth exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletHeat_exhaustion_strong_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Tendsto (fun j => l2ZeroExtension μ (O j) (hO.1 j).1.measurableSet
      (dirichletHeat g μ hμ (O j) t (l2Restriction μ (O j) f))) atTop
      (𝓝 (scalarHeatFamily g μ hμ t f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε/3 := by positivity
  have herror : Tendsto (fun k => scalarEulerUniformError t ht k*‖f‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using (scalarEulerUniformError_tendsto t ht).mul_const ‖f‖
  have hwhole := tendsto_iff_norm_sub_tendsto_zero.mp (scalarHeatFamily_euler_apply_tendsto g μ hμ t ht f)
  obtain ⟨k,hkerr,hkwhole⟩ := ((herror.eventually (eventually_lt_nhds hthird)).and
    (hwhole.eventually (eventually_lt_nhds hthird))).exists
  have hfixed := tendsto_iff_norm_sub_tendsto_zero.mp (dirichletHeatEuler_exhaustion_tendsto g μ hμ hO t ht k f)
  filter_upwards [hfixed.eventually (eventually_lt_nhds hthird)] with j hj
  let a := l2ZeroExtension μ (O j) (hO.1 j).1.measurableSet
    (dirichletHeat g μ hμ (O j) t (l2Restriction μ (O j) f))
  let b := l2ZeroExtension μ (O j) (hO.1 j).1.measurableSet
    (dirichletHeatEuler g μ hμ (O j) t ht k (l2Restriction μ (O j) f))
  let c := scalarHeatEuler g μ hμ t ht k f
  let d := scalarHeatFamily g μ hμ t f
  have hab : dist a b ≤ scalarEulerUniformError t ht k*‖f‖ := by
    rw [dist_eq_norm,norm_sub_rev]
    exact dirichletHeatEuler_ambient_error g μ hμ (O j) (hO.1 j).1.measurableSet t ht k f
  have hbc : dist b c < ε/3 := by simpa only [dist_eq_norm] using hj
  have hcd : dist c d < ε/3 := by simpa only [dist_eq_norm] using hkwhole
  have htri : dist a d ≤ dist a b+dist b c+dist c d := by
    linarith only [dist_triangle a c d,dist_triangle a b c]
  exact htri.trans_lt (by linarith only [hab,hkerr,hbc,hcd])

end Yau.Proofs.F03Aux
