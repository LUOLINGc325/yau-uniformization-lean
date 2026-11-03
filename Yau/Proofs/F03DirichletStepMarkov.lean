import Yau.Proofs.F03DirichletNormalContraction
import Yau.Proofs.F03DirichletStepRelations
import Yau.LeafProofs.L19ScalarMarkovBounds

/-! Supported positive-step resolvents preserve the actual bounded Markov intervals. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletEnergy_normalClip (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) (K : ℝ) (hK : 0 < K) :
    ∃ v : DirichletEnergy g μ hμ O,
      (dirichletL2 g μ hμ O v : M.Carrier → ℝ) =ᵐ[μ.restrict O]
        (fun x => normalClip K ((dirichletL2 g μ hμ O u) x)) ∧
      ‖v‖ ^ 2 - ‖dirichletL2 g μ hμ O v‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖dirichletL2 g μ hμ O u‖ ^ 2 := by
  obtain ⟨v, hv, hE⟩ := dirichletEnergy_normalClip_L2 g μ hμ O hO u K hK.le
  exact ⟨v, hv ▸ normalClipL2_coe (μ.restrict O) K hK.le (dirichletL2 g μ hμ O u), hE⟩

/-- Actual scalar resolvents preserve every bounded normal interval.
Both the projection into the energy space and the strict minimization
argument have been proved for the fixed metric and volume. -/
theorem dirichletStepResolvent_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O) (h : ℝ) (hh : 0 < h)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 (μ.restrict O))
    (hf : ∀ᵐ x ∂μ.restrict O, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ.restrict O, 0 ≤ dirichletStepResolvent g μ hμ O h hh f x ∧ dirichletStepResolvent g μ hμ O h hh f x ≤ K := by
  let u := dirichletStepResolventEnergy g μ hμ O h hh f
  obtain ⟨v, hv, hE⟩ := dirichletEnergy_normalClip g μ hμ O hO u K hK
  have hdist : ‖dirichletL2 g μ hμ O v - f‖ ≤ ‖dirichletL2 g μ hμ O u - f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hv, hf, Lp.coeFn_sub (dirichletL2 g μ hμ O v) f,
      Lp.coeFn_sub (dirichletL2 g μ hμ O u) f] with x hvx hfx hsubv hsubu
    simp only [hsubv, hsubu, Pi.sub_apply, hvx, Real.norm_eq_abs]
    exact normalClip_distance_le hfx _
  have hEnergy : dirichletClosedEnergy g μ hμ O v v ≤ dirichletClosedEnergy g μ hμ O u u := by
    simpa only [dirichletClosedEnergy, real_inner_self_eq_norm_sq] using hE
  have hobj : dirichletStepResolventObjective g μ hμ O h f v ≤ dirichletStepResolventObjective g μ hμ O h f u := by
    unfold dirichletStepResolventObjective
    have hmul := mul_le_mul_of_nonneg_left hEnergy hh.le
    have hsq : ‖dirichletL2 g μ hμ O v - f‖ ^ 2 ≤ ‖dirichletL2 g μ hμ O u - f‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist
    exact add_le_add hsq hmul
  have hstrict := dirichletStepResolventObjective_strict_minimum g μ hμ O h hh f v
  change dirichletStepResolventObjective g μ hμ O h f u + min 1 h * ‖v - u‖ ^ 2 ≤
    dirichletStepResolventObjective g μ hμ O h f v at hstrict
  have hzero : ‖v - u‖ ^ 2 = 0 := by
    have hpos : 0 < min 1 h := lt_min zero_lt_one hh
    have hle : min 1 h * ‖v - u‖ ^ 2 ≤ 0 := by linarith only [hstrict, hobj]
    have hn : ‖v - u‖ ^ 2 ≤ 0 := by nlinarith only [hle, hpos]
    exact le_antisymm hn (sq_nonneg _)
  have hvu : v = u := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  rw [hvu] at hv
  filter_upwards [hv] with x hx
  change 0 ≤ dirichletL2 g μ hμ O u x ∧ dirichletL2 g μ hμ O u x ≤ K
  rw [hx]
  exact normalClip_mem_interval hK.le _

theorem dirichletStepResolvent_pow_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O) (h : ℝ) (hh : 0 < h)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 (μ.restrict O))
    (hf : ∀ᵐ x ∂μ.restrict O, 0 ≤ f x ∧ f x ≤ K) (k : ℕ) :
    ∀ᵐ x ∂μ.restrict O, 0 ≤ ((dirichletStepResolvent g μ hμ O h hh) ^ k) f x ∧
      ((dirichletStepResolvent g μ hμ O h hh) ^ k) f x ≤ K := by
  induction k with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ k hk =>
    rw [pow_succ']
    exact dirichletStepResolvent_markov g μ hμ O hO h hh K hK _ hk

/-- Strong limits of actual Euler resolvent powers retain the bounded
Markov interval.  The heat family supplies the genuine Euler limit. -/
theorem dirichletStepResolvent_euler_limit_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O) (step : ℕ → ℝ) (hstep : ∀ j, 0 < step j)
    (power : ℕ → ℕ) (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 (μ.restrict O))
    (hf : ∀ᵐ x ∂μ.restrict O, 0 ≤ f x ∧ f x ≤ K) (v : Lp ℝ 2 (μ.restrict O))
    (hv : Tendsto (fun j => ((dirichletStepResolvent g μ hμ O (step j) (hstep j)) ^ power j) f)
      atTop (nhds v)) :
    ∀ᵐ x ∂μ.restrict O, 0 ≤ v x ∧ v x ≤ K := by
  apply (normalIntervalL2_isClosed (μ.restrict O) K hK.le).mem_of_tendsto hv
  exact Eventually.of_forall (fun j => dirichletStepResolvent_pow_markov g μ hμ O hO (step j) (hstep j) K hK f hf (power j))

end Yau.Proofs.F03Aux
