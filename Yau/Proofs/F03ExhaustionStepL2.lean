import Yau.Proofs.F03ExhaustionStep
import Yau.Proofs.F03StrongPowers

/-! Actual zero-extended L2 resolvents and powers converge along the exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def dirichletAmbientStep (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (h : ℝ) (hh : 0 < h) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2ZeroExtension μ Ω hΩ).comp ((dirichletStepResolvent g μ hμ Ω h hh).comp (l2Restriction μ Ω))

theorem dirichletAmbientStep_norm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h) (f : Lp ℝ 2 μ) :
    ‖dirichletAmbientStep g μ hμ Ω hΩ h hh f‖ ≤ ‖f‖ := by
  change ‖l2ZeroExtension μ Ω hΩ (dirichletStepResolvent g μ hμ Ω h hh (l2Restriction μ Ω f))‖ ≤ _
  rw [l2ZeroExtension_norm]
  exact (dirichletStepResolvent_norm_le g μ hμ Ω h hh _).trans (restrictL2_norm_le μ Ω f)

theorem dirichletAmbientStep_eq_energy (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h) (f : Lp ℝ 2 μ) :
    dirichletAmbientStep g μ hμ Ω hΩ h hh f=
      scalarEnergyL2 g μ hμ
        (dirichletStepResolventEnergy g μ hμ Ω h hh (l2Restriction μ Ω f)).val :=
  dirichletL2_zeroExtension g μ hμ Ω hΩ _

theorem dirichletAmbientStep_exhaustion_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) {h : ℝ} (hh : 0 < h) (f : Lp ℝ 2 μ) :
    Tendsto (fun j => dirichletAmbientStep g μ hμ (O j) (hO.1 j).1.measurableSet h hh f) atTop
      (𝓝 (scalarResolvent g μ hμ h hh f)) := by
  have hlim := ((scalarEnergyL2 g μ hμ).continuous.tendsto
    (scalarResolventEnergy g μ hμ h hh f)).comp (dirichlet_step_energy_exhaustion_tendsto g μ hμ hO hh f)
  simpa only [Function.comp_def,dirichletAmbientStep_eq_energy,scalarResolvent,ContinuousLinearMap.comp_apply] using hlim

theorem dirichletAmbientStep_powers_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) {h : ℝ} (hh : 0 < h)
    (m : ℕ) (f : Lp ℝ 2 μ) :
    Tendsto (fun j => ((dirichletAmbientStep g μ hμ (O j) (hO.1 j).1.measurableSet h hh)^m) f) atTop
      (𝓝 (((scalarResolvent g μ hμ h hh)^m) f)) :=
  contraction_powers_strong_tendsto _ _
    (fun j x => dirichletAmbientStep_norm_le g μ hμ (O j) (hO.1 j).1.measurableSet hh x)
    (fun x => dirichletAmbientStep_exhaustion_tendsto g μ hμ hO hh x) m f

theorem dirichletAmbientStep_pow_succ (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h)
    (m : ℕ) (f : Lp ℝ 2 μ) :
    ((dirichletAmbientStep g μ hμ Ω hΩ h hh)^(m+1)) f=
      l2ZeroExtension μ Ω hΩ (((dirichletStepResolvent g μ hμ Ω h hh)^(m+1)) (l2Restriction μ Ω f)) := by
  induction m with
  | zero => simp only [zero_add,pow_one];rfl
  | succ m hm =>
    rw [pow_succ',mul_apply_eq_comp,hm]
    change l2ZeroExtension μ Ω hΩ (dirichletStepResolvent g μ hμ Ω h hh
      (l2Restriction μ Ω (l2ZeroExtension μ Ω hΩ _)))=_
    simp only [l2Restriction_zeroExtension,pow_succ',mul_apply_eq_comp]

end Yau.Proofs.F03Aux
