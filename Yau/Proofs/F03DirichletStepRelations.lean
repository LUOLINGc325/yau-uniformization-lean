import Yau.Proofs.F03DirichletStepResolvent

/-! Actual resolvent identities and positivity used by the Euler heat approximation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletStepResolvent_one_ident (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    dirichletStepResolvent g μ hμ O 1 zero_lt_one = dirichletResolvent g μ hμ O := by
  rw [dirichletStepResolvent_one_eq]
  rfl

theorem dirichletStepResolvent_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    ‖dirichletStepResolvent g μ hμ O h hh‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using dirichletStepResolvent_norm_le g μ hμ O h hh f

theorem dirichletStepResolvent_inner_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 (μ.restrict O)) :
    0 ≤ ⟪dirichletStepResolvent g μ hμ O h hh f, f⟫_ℝ := by
  have hvar := dirichletStepResolventEnergy_equation g μ hμ O h hh f (dirichletStepResolventEnergy g μ hμ O h hh f)
  have hE := dirichletClosedEnergy_nonneg g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f)
  change ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ +
    h * dirichletClosedEnergy g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f)
      (dirichletStepResolventEnergy g μ hμ O h hh f) = ⟪f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ at hvar
  have hcomm : ⟪dirichletStepResolvent g μ hμ O h hh f, f⟫_ℝ =
      ⟪f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ := real_inner_comm _ _
  nlinarith [mul_nonneg hh.le hE,
    (real_inner_self_nonneg : 0 ≤ ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ)]

theorem dirichletStepResolvent_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    (dirichletStepResolvent g μ hμ O h hh).adjoint = dirichletStepResolvent g μ hμ O h hh := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f k
  have hfk := dirichletStepResolventEnergy_equation g μ hμ O h hh f (dirichletStepResolventEnergy g μ hμ O h hh k)
  have hkf := dirichletStepResolventEnergy_equation g μ hμ O h hh k (dirichletStepResolventEnergy g μ hμ O h hh f)
  change ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletStepResolvent g μ hμ O h hh k⟫_ℝ +
    h * dirichletClosedEnergy g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f)
      (dirichletStepResolventEnergy g μ hμ O h hh k) = ⟪f, dirichletStepResolvent g μ hμ O h hh k⟫_ℝ at hfk
  change ⟪dirichletStepResolvent g μ hμ O h hh k, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ +
    h * dirichletClosedEnergy g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh k)
      (dirichletStepResolventEnergy g μ hμ O h hh f) = ⟪k, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ at hkf
  have hCE := dirichletClosedEnergy_symm g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh k)
    (dirichletStepResolventEnergy g μ hμ O h hh f)
  have hcomm : ⟪dirichletStepResolvent g μ hμ O h hh k, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ =
      ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletStepResolvent g μ hμ O h hh k⟫_ℝ := real_inner_comm _ _
  have hcomm' : ⟪k, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ =
      ⟪dirichletStepResolvent g μ hμ O h hh f, k⟫_ℝ := real_inner_comm _ _
  rw [hCE, hcomm, hcomm'] at hkf
  linarith only [hfk, hkf]

/-- The true Euler-step resolvent is related to the actual unit-time
resolvent by the scalar rational function used by the heat calculus. -/
theorem dirichletStepResolvent_euler_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletStepResolvent g μ hμ O h hh
      (h • f + (1 - h) • dirichletStepResolvent g μ hμ O 1 zero_lt_one f) =
      dirichletStepResolvent g μ hμ O 1 zero_lt_one f := by
  let u := dirichletStepResolventEnergy g μ hμ O 1 zero_lt_one f
  have hu : dirichletL2 g μ hμ O u = dirichletStepResolvent g μ hμ O 1 zero_lt_one f := rfl
  have heq := dirichletStepResolventEnergy_unique g μ hμ O h hh
    (h • f + (1 - h) • dirichletStepResolvent g μ hμ O 1 zero_lt_one f) u (by
      intro v
      have hvar := dirichletStepResolventEnergy_equation g μ hμ O 1 zero_lt_one f v
      change ⟪dirichletL2 g μ hμ O u, dirichletL2 g μ hμ O v⟫_ℝ +
        1 * dirichletClosedEnergy g μ hμ O u v = ⟪f, dirichletL2 g μ hμ O v⟫_ℝ at hvar
      simp only [inner_add_left, inner_smul_left, conj_trivial]
      rw [← hu]
      have hscaled := congrArg (fun r : ℝ => h * r) hvar
      nlinarith only [hscaled])
  exact (congrArg (dirichletL2 g μ hμ O) heq).symm

theorem dirichletStepResolvent_euler_operator_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    (dirichletStepResolvent g μ hμ O h hh).comp
        (h • ContinuousLinearMap.id ℝ (Lp ℝ 2 (μ.restrict O)) +
          (1 - h) • dirichletStepResolvent g μ hμ O 1 zero_lt_one) =
      dirichletStepResolvent g μ hμ O 1 zero_lt_one := by
  apply ContinuousLinearMap.ext
  intro f
  exact dirichletStepResolvent_euler_relation g μ hμ O h hh f

/-- The square bound is available directly from `B = J J*`, before
invoking any spectral theorem. -/
theorem dirichletStepResolvent_one_square_inner_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : Lp ℝ 2 (μ.restrict O)) :
    ‖dirichletStepResolvent g μ hμ O 1 zero_lt_one f‖ ^ 2 ≤
      ⟪dirichletStepResolvent g μ hμ O 1 zero_lt_one f, f⟫_ℝ := by
  rw [dirichletStepResolvent_one_eq]
  change ‖dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint f)‖ ^ 2 ≤
    ⟪dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint f), f⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hh := dirichletL2_norm_le g μ hμ O ((dirichletL2 g μ hμ O).adjoint f)
  nlinarith [norm_nonneg (dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint f)),
    norm_nonneg ((dirichletL2 g μ hμ O).adjoint f)]

end Yau.Proofs.F03Aux
