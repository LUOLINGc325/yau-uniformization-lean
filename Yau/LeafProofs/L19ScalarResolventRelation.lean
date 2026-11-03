import Yau.LeafProofs.L19ScalarResolvent

/-! Actual resolvent identities and positivity used by the Euler heat approximation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem scalarResolvent_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    ‖scalarResolvent g μ hμ h hh‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using scalarResolvent_norm_le g μ hμ h hh f

theorem scalarResolvent_inner_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 μ) :
    0 ≤ ⟪scalarResolvent g μ hμ h hh f, f⟫_ℝ := by
  have hvar := scalarResolventEnergy_equation g μ hμ h hh f (scalarResolventEnergy g μ hμ h hh f)
  have hE := scalarClosedEnergy_nonneg g μ hμ (scalarResolventEnergy g μ hμ h hh f)
  change ⟪scalarResolvent g μ hμ h hh f, scalarResolvent g μ hμ h hh f⟫_ℝ +
    h * scalarClosedEnergy g μ hμ (scalarResolventEnergy g μ hμ h hh f)
      (scalarResolventEnergy g μ hμ h hh f) = ⟪f, scalarResolvent g μ hμ h hh f⟫_ℝ at hvar
  have hcomm : ⟪scalarResolvent g μ hμ h hh f, f⟫_ℝ =
      ⟪f, scalarResolvent g μ hμ h hh f⟫_ℝ := real_inner_comm _ _
  nlinarith [mul_nonneg hh.le hE,
    (real_inner_self_nonneg : 0 ≤ ⟪scalarResolvent g μ hμ h hh f, scalarResolvent g μ hμ h hh f⟫_ℝ)]

theorem scalarResolvent_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    (scalarResolvent g μ hμ h hh).adjoint = scalarResolvent g μ hμ h hh := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f k
  have hfk := scalarResolventEnergy_equation g μ hμ h hh f (scalarResolventEnergy g μ hμ h hh k)
  have hkf := scalarResolventEnergy_equation g μ hμ h hh k (scalarResolventEnergy g μ hμ h hh f)
  change ⟪scalarResolvent g μ hμ h hh f, scalarResolvent g μ hμ h hh k⟫_ℝ +
    h * scalarClosedEnergy g μ hμ (scalarResolventEnergy g μ hμ h hh f)
      (scalarResolventEnergy g μ hμ h hh k) = ⟪f, scalarResolvent g μ hμ h hh k⟫_ℝ at hfk
  change ⟪scalarResolvent g μ hμ h hh k, scalarResolvent g μ hμ h hh f⟫_ℝ +
    h * scalarClosedEnergy g μ hμ (scalarResolventEnergy g μ hμ h hh k)
      (scalarResolventEnergy g μ hμ h hh f) = ⟪k, scalarResolvent g μ hμ h hh f⟫_ℝ at hkf
  have hCE := scalarClosedEnergy_symm g μ hμ (scalarResolventEnergy g μ hμ h hh k)
    (scalarResolventEnergy g μ hμ h hh f)
  have hcomm : ⟪scalarResolvent g μ hμ h hh k, scalarResolvent g μ hμ h hh f⟫_ℝ =
      ⟪scalarResolvent g μ hμ h hh f, scalarResolvent g μ hμ h hh k⟫_ℝ := real_inner_comm _ _
  have hcomm' : ⟪k, scalarResolvent g μ hμ h hh f⟫_ℝ =
      ⟪scalarResolvent g μ hμ h hh f, k⟫_ℝ := real_inner_comm _ _
  rw [hCE, hcomm, hcomm'] at hkf
  linarith only [hfk, hkf]

/-- The true Euler-step resolvent is related to the actual unit-time
resolvent by the scalar rational function used by the heat calculus. -/
theorem scalarResolvent_euler_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 μ) :
    scalarResolvent g μ hμ h hh
      (h • f + (1 - h) • scalarResolvent g μ hμ 1 zero_lt_one f) =
      scalarResolvent g μ hμ 1 zero_lt_one f := by
  let u := scalarResolventEnergy g μ hμ 1 zero_lt_one f
  have hu : scalarEnergyL2 g μ hμ u = scalarResolvent g μ hμ 1 zero_lt_one f := rfl
  have heq := scalarResolventEnergy_unique g μ hμ h hh
    (h • f + (1 - h) • scalarResolvent g μ hμ 1 zero_lt_one f) u (by
      intro v
      have hvar := scalarResolventEnergy_equation g μ hμ 1 zero_lt_one f v
      change ⟪scalarEnergyL2 g μ hμ u, scalarEnergyL2 g μ hμ v⟫_ℝ +
        1 * scalarClosedEnergy g μ hμ u v = ⟪f, scalarEnergyL2 g μ hμ v⟫_ℝ at hvar
      simp only [inner_add_left, inner_smul_left, conj_trivial]
      rw [← hu]
      have hscaled := congrArg (fun r : ℝ => h * r) hvar
      nlinarith only [hscaled])
  exact (congrArg (scalarEnergyL2 g μ hμ) heq).symm

theorem scalarResolvent_euler_operator_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    (scalarResolvent g μ hμ h hh).comp
        (h • ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) +
          (1 - h) • scalarResolvent g μ hμ 1 zero_lt_one) =
      scalarResolvent g μ hμ 1 zero_lt_one := by
  apply ContinuousLinearMap.ext
  intro f
  exact scalarResolvent_euler_relation g μ hμ h hh f

/-- The square bound is available directly from `B = J J*`, before
invoking any spectral theorem. -/
theorem scalarResolvent_one_square_inner_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    ‖scalarResolvent g μ hμ 1 zero_lt_one f‖ ^ 2 ≤
      ⟪scalarResolvent g μ hμ 1 zero_lt_one f, f⟫_ℝ := by
  rw [scalarResolvent_one_eq]
  change ‖scalarEnergyL2 g μ hμ ((scalarEnergyL2 g μ hμ).adjoint f)‖ ^ 2 ≤
    ⟪scalarEnergyL2 g μ hμ ((scalarEnergyL2 g μ hμ).adjoint f), f⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hh := scalarEnergyL2_norm_le g μ hμ ((scalarEnergyL2 g μ hμ).adjoint f)
  nlinarith [norm_nonneg (scalarEnergyL2 g μ hμ ((scalarEnergyL2 g μ hμ).adjoint f)),
    norm_nonneg ((scalarEnergyL2 g μ hμ).adjoint f)]

end Yau.LeafProofs.L19Aux
