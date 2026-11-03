import Yau.Proofs.F03DirichletHeatDerivative

/-! Actual derivative semigroup factors and a uniform later-time L2 bound. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def dirichletHeatDerivativeOperator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (t : ℝ) :
    Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  dirichletHeat g μ hμ Ω t-dirichletHeatInverse g μ hμ Ω t

theorem dirichletHeatDerivative_right_factor (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    dirichletHeatDerivativeOperator g μ hμ Ω (s+r) =
      dirichletHeatDerivativeOperator g μ hμ Ω s*dirichletHeat g μ hμ Ω r := by
  have hd₁ : HasDerivAt (fun a => dirichletHeat g μ hμ Ω (a+r))
      (dirichletHeatDerivativeOperator g μ hμ Ω (s+r)) s := by
    have hclock : HasDerivAt (fun a : ℝ => a+r) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const r
    have h := (dirichletHeat_hasDerivAt g μ hμ Ω (add_pos_of_pos_of_nonneg hs hr)).scomp s hclock
    simpa only [dirichletHeatDerivativeOperator,Function.comp_def,one_smul] using h
  have hd₂ := (dirichletHeat_hasDerivAt g μ hμ Ω hs).mul_const (dirichletHeat g μ hμ Ω r)
  have hEq : (fun a => dirichletHeat g μ hμ Ω (a+r)) =ᶠ[𝓝 s]
      (fun a => dirichletHeat g μ hμ Ω a*dirichletHeat g μ hμ Ω r) := by
    filter_upwards [eventually_gt_nhds hs] with a ha
    exact dirichletHeat_add g μ hμ Ω ha.le hr
  exact hd₁.unique (hd₂.congr_of_eventuallyEq hEq)

theorem dirichletHeatDerivative_left_factor (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    dirichletHeatDerivativeOperator g μ hμ Ω (s+r) =
      dirichletHeat g μ hμ Ω r*dirichletHeatDerivativeOperator g μ hμ Ω s := by
  have hd₁ : HasDerivAt (fun a => dirichletHeat g μ hμ Ω (a+r))
      (dirichletHeatDerivativeOperator g μ hμ Ω (s+r)) s := by
    have hclock : HasDerivAt (fun a : ℝ => a+r) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const r
    have h := (dirichletHeat_hasDerivAt g μ hμ Ω (add_pos_of_pos_of_nonneg hs hr)).scomp s hclock
    simpa only [dirichletHeatDerivativeOperator,Function.comp_def,one_smul] using h
  have hd₂ := (dirichletHeat_hasDerivAt g μ hμ Ω hs).const_mul (dirichletHeat g μ hμ Ω r)
  have hEq : (fun a => dirichletHeat g μ hμ Ω (a+r)) =ᶠ[𝓝 s]
      (fun a => dirichletHeat g μ hμ Ω r*dirichletHeat g μ hμ Ω a) := by
    filter_upwards [eventually_gt_nhds hs] with a ha
    simpa only [add_comm] using dirichletHeat_add g μ hμ Ω hr ha.le
  exact hd₁.unique (hd₂.congr_of_eventuallyEq hEq)

theorem dirichletHeatDerivative_uniform_later_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, τ ≤ t → ∀ f : Lp ℝ 2 (μ.restrict Ω),
      ‖dirichletHeatDerivativeOperator g μ hμ Ω t f‖ ≤ B*‖f‖ := by
  let D := dirichletHeatDerivativeOperator g μ hμ Ω (τ/2)
  refine ⟨max 1 ‖D‖,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro t ht f
  have hr : 0 ≤ t-τ/2 := by linarith only [hτ,ht]
  have htime : τ/2+(t-τ/2)=t := by ring
  have hf := dirichletHeatDerivative_right_factor g μ hμ Ω (half_pos hτ) hr
  have hf' : dirichletHeatDerivativeOperator g μ hμ Ω t = D*dirichletHeat g μ hμ Ω (t-τ/2) := by
    simpa only [htime] using hf
  rw [hf',mul_apply_eq_comp]
  exact ((D.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (dirichletHeat_norm_le g μ hμ Ω (t-τ/2) f) (norm_nonneg D))).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f))

end Yau.Proofs.F03Aux
