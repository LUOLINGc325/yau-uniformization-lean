import Yau.Proofs.F03GalerkinBound
import Yau.Proofs.F03ExhaustionResolvent
import Yau.Proofs.F03DirichletStepResolvent

/-! Actual positive-step resolvents converge along the given smooth exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

theorem dirichlet_inner_restriction (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 μ) (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (l2Restriction μ Ω f) (dirichletL2 g μ hμ Ω v)=
      inner ℝ f (scalarEnergyL2 g μ hμ v.val) := by
  have hp := l2ZeroExtension_inner_left μ Ω hΩ (dirichletL2 g μ hμ Ω v) f
  rw [dirichletL2_zeroExtension g μ hμ Ω hΩ v] at hp
  calc
    _ = inner ℝ (dirichletL2 g μ hμ Ω v) (l2Restriction μ Ω f) := real_inner_comm _ _
    _ = inner ℝ (scalarEnergyL2 g μ hμ v.val) f := hp.symm
    _ = _ := real_inner_comm _ _

theorem dirichlet_step_ambient_equation (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) (v : DirichletEnergy g μ hμ Ω) :
    scalarResolventForm g μ hμ h
      (dirichletStepResolventEnergy g μ hμ Ω h hh (l2Restriction μ Ω f)).val v.val=
      inner ℝ f (scalarEnergyL2 g μ hμ v.val) := by
  let u := dirichletStepResolventEnergy g μ hμ Ω h hh (l2Restriction μ Ω f)
  have hinner : inner ℝ (scalarEnergyL2 g μ hμ u.val) (scalarEnergyL2 g μ hμ v.val)=
      inner ℝ (dirichletL2 g μ hμ Ω u) (dirichletL2 g μ hμ Ω v) := by
    rw [← dirichletL2_zeroExtension g μ hμ Ω hΩ u,
      ← dirichletL2_zeroExtension g μ hμ Ω hΩ v,l2ZeroExtension_inner]
  rw [scalarResolventForm_apply,← dirichletClosedEnergy_eq_ambient g μ hμ Ω hΩ u v,hinner]
  change inner ℝ (dirichletStepResolvent g μ hμ Ω h hh (l2Restriction μ Ω f))
    (dirichletL2 g μ hμ Ω v)+h*dirichletClosedEnergy g μ hμ Ω u v=_
  rw [dirichletStepResolventEnergy_equation,dirichlet_inner_restriction g μ hμ Ω hΩ f v]

theorem dirichlet_step_energy_exhaustion_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun j => (dirichletStepResolventEnergy g μ hμ (O j) h hh
      (l2Restriction μ (O j) f)).val) atTop (𝓝 (scalarResolventEnergy g μ hμ h hh f)) := by
  let a : ScalarEnergySpace g μ hμ →L[ℝ] ScalarEnergySpace g μ hμ →L[ℝ] ℝ :=
    scalarResolventForm g μ hμ h
  let α := min 1 h
  let u := scalarResolventEnergy g μ hμ h hh f
  let C := |h|+|1-h|
  let K : ℝ := C/α
  have hα : 0 < α := lt_min zero_lt_one hh
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hK : 0 ≤ K := div_nonneg hC hα.le
  have ha : ∀ z, α*‖z‖^2 ≤ a z z := by
    intro z
    simpa only [pow_two,mul_assoc] using scalarResolventForm_lower_bound g μ hμ h z
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε/(K+1) := div_pos hε (by linarith only [hK])
  filter_upwards [smoothExhaustion_energy_approx g μ hμ hO u hη] with j hj
  obtain ⟨v,hv⟩ := hj
  let u₀ := dirichletStepResolventEnergy g μ hμ (O j) h hh (l2Restriction μ (O j) f)
  let w : DirichletEnergy g μ hμ (O j) := u₀-v
  have hu : a u w.val=inner ℝ f (scalarEnergyL2 g μ hμ w.val) := by
    simpa only [a,u,scalarResolventForm_apply,scalarResolvent,ContinuousLinearMap.comp_apply] using
      scalarResolventEnergy_equation g μ hμ h hh f w.val
  have hu₀ : a u₀.val w.val=inner ℝ f (scalarEnergyL2 g μ hμ w.val) :=
    dirichlet_step_ambient_equation g μ hμ (O j) (hO.1 j).1.measurableSet hh f w
  have horth : a (u-u₀.val) (u₀.val-v.val)=0 := by
    change a (u-u₀.val) w.val=0
    rw [map_sub,ContinuousLinearMap.sub_apply,hu,hu₀,sub_self]
  let e := u-u₀.val
  have hAe : a e e=a e (u-v.val) := by
    have hsplit : u-v.val=e+(u₀.val-v.val) := by dsimp only [e];abel
    rw [hsplit,map_add,horth,add_zero]
  have hupper : α*‖e‖^2 ≤ C*‖e‖*‖u-v.val‖ := by
    calc
      _ ≤ a e e := ha e
      _ ≤ |a e e| := le_abs_self _
      _ = |a e (u-v.val)| := congrArg abs hAe
      _ ≤ _ := scalarResolventForm_explicit_bound g μ hμ h e (u-v.val)
  have herr : ‖u-u₀.val‖ ≤ K*‖u-v.val‖ := coercive_real_error_bound
    (norm_nonneg _) (norm_nonneg _) hα hC hupper
  have hbest : ‖u-v.val‖ ≤ ε/(K+1) := by rw [norm_sub_rev];exact hv.le
  have hnorm : ‖u-u₀.val‖ ≤ K*(ε/(K+1)) :=
    herr.trans (mul_le_mul_of_nonneg_left hbest hK)
  have hηeq : (K+1)*(ε/(K+1))=ε := mul_div_cancel₀ ε (by linarith only [hK] : K+1 ≠ 0)
  rw [dist_eq_norm,norm_sub_rev]
  exact hnorm.trans_lt (by nlinarith only [hηeq,hη])

end Yau.Proofs.F03Aux
