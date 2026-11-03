import Yau.Proofs.F03DirichletStepDomination
import Yau.Proofs.F03DirichletInclusion
import Yau.Proofs.F03ResolventOrder
import Yau.Proofs.F03OrderPowers
import Yau.Proofs.F03ExhaustionEuler

/-! Actual supported resolvents and heat increase with the actual domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletAmbientStep_mono_domain (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω Γ : Set M.Carrier) (hΩ : IsOpen Ω) (hΓ : IsOpen Γ) (hΩΓ : Ω ⊆ Γ)
    {h : ℝ} (hh : 0 < h) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    ∀ᵐ x ∂μ, dirichletAmbientStep g μ hμ Ω hΩ.measurableSet h hh f x ≤
      dirichletAmbientStep g μ hμ Γ hΓ.measurableSet h hh f x := by
  let q := dirichletStepResolventEnergy g μ hμ Γ h hh (l2Restriction μ Γ f)
  have hqLp : 0 ≤ scalarEnergyL2 g μ hμ q.val := by
    rw [← dirichletAmbientStep_eq_energy g μ hμ Γ hΓ.measurableSet hh f]
    simpa only [map_zero] using (dirichletAmbientStep_monotone g μ hμ Γ hΓ.measurableSet hh) hf
  have hq := (Lp.coeFn_nonneg _).mpr hqLp
  have hqe (v : DirichletEnergy g μ hμ Ω) : scalarResolventForm g μ hμ h q.val v.val=
      inner ℝ f (scalarEnergyL2 g μ hμ v.val) := by
    have he := dirichlet_step_ambient_equation g μ hμ Γ hΓ.measurableSet hh f
      (dirichletInclusion g μ hμ hΩΓ v)
    simpa only [dirichletInclusion_val] using he
  rw [dirichletAmbientStep_eq_energy,dirichletAmbientStep_eq_energy]
  exact dirichlet_step_le_ambient_weak_solution g hK μ hμ Ω hΩ hh f q.val hq hqe

theorem dirichletHeat_mono_domain (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω Γ : Set M.Carrier) (hΩ : IsOpen Ω) (hΓ : IsOpen Γ) (hΩΓ : Ω ⊆ Γ)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f)) ≤
      l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeat g μ hμ Γ t (l2Restriction μ Γ f)) := by
  have heuler : ∀ k : ℕ,
      l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeatEuler g μ hμ Ω t ht k (l2Restriction μ Ω f)) ≤
        l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeatEuler g μ hμ Γ t ht k (l2Restriction μ Γ f)) := by
    intro k
    have hh := div_pos ht (scalarEulerCount_cast_pos k)
    let A := dirichletAmbientStep g μ hμ Ω hΩ.measurableSet (t/scalarEulerCount k) hh
    let B := dirichletAmbientStep g μ hμ Γ hΓ.measurableSet (t/scalarEulerCount k) hh
    have hAB : ∀ v : Lp ℝ 2 μ, 0 ≤ v → A v ≤ B v := by
      intro v hv
      exact l2_le_of_ae μ _ _ (dirichletAmbientStep_mono_domain g hK μ hμ Ω Γ hΩ hΓ hΩΓ hh v hv)
    have hB : ∀ v : Lp ℝ 2 μ, 0 ≤ v → 0 ≤ B v := by
      intro v hv
      simpa only [map_zero] using (dirichletAmbientStep_monotone g μ hμ Γ hΓ.measurableSet hh) hv
    have hp := l2_powers_le_of_step μ A B (dirichletAmbientStep_monotone g μ hμ Ω hΩ.measurableSet hh)
      hB hAB (scalarEulerCount k) f hf
    simpa only [A,B,dirichletHeatEuler_ambient_eq] using hp
  have hΩlim := ((l2ZeroExtension μ Ω hΩ.measurableSet).continuous.tendsto
    (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f))).comp
      (dirichletHeat_euler_apply_tendsto g μ hμ Ω t ht (l2Restriction μ Ω f))
  have hΓlim := ((l2ZeroExtension μ Γ hΓ.measurableSet).continuous.tendsto
    (dirichletHeat g μ hμ Γ t (l2Restriction μ Γ f))).comp
      (dirichletHeat_euler_apply_tendsto g μ hμ Γ t ht (l2Restriction μ Γ f))
  exact le_of_tendsto_of_tendsto hΩlim hΓlim (Eventually.of_forall heuler)

end Yau.Proofs.F03Aux
