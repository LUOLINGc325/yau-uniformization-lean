import Yau.Proofs.C04BoundedGeometryChartsNormalCoframe
import Yau.Proofs.C04BoundedGeometryChartsRadialIntegralEstimates
import Yau.Proofs.C04BoundedGeometryChartsCurvatureJetMax
import Yau.Proofs.C04JetAbsorption

/-! One uniform radius controls all jets of the actual exponential coframe and connection. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_uniform_normal_coframe_jet_bounds (n : ℕ) (hn : 0 < n)
    (r : ℝ) (K : ℕ → ℝ) (hr : 0 < r) (hK : ∀ m, 0 < K m) :
    ∃ R : ℝ, 0 < R ∧ ∃ J : ℕ → ℝ, (∀ m, 0 < J m) ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M) (p : M.Carrier)
        (U : ComplexVector n ≃L[ℂ] TangentVector M p),
        (∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
          (1 : Matrix (Fin n) (Fin n) ℂ) i j) →
        (∀ m x, x ∈ distBall g.form p (2 * r) → curvatureJetNorm g.form m x ≤ K m) →
        (∀ x ∈ Metric.closedBall (0 : ComplexVector n) R,
          unitaryExponential g p U x ∈ distBall g.form p (2 * r) ∧
          ‖radialCoframe g p U x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) ∧
          (realMapDeriv (unitaryExponential g p U) x).IsInvertible) ∧
        ∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R →
          ‖iteratedFDeriv ℝ m (radialCoframe g p U) x‖ ≤ J m ∧
          ‖iteratedFDeriv ℝ m (radialConnection g p U) x‖ ≤ J m ∧
          ‖iteratedFDeriv ℝ m (radialCurvatureOperator g p U) x‖ ≤ J m := by
  have hKn : ∀ j, 0 ≤ K j := fun j => (hK j).le
  obtain ⟨s, hs, hseed⟩ := exists_uniform_exponential_coframe_radius n hn r (K 0) hr (hK 0)
  let lam := curvatureTopCoefficient n K
  have hlam : 0 ≤ lam := curvatureTopCoefficient_nonneg K hKn
  let R := min s (1 / (2 * (1 + lam)))
  have hR : 0 < R := lt_min hs (by positivity)
  have hRs : R ≤ s := min_le_left _ _
  have hRd : R ≤ 1 / (2 * (1 + lam)) := min_le_right _ _
  have hprod : R * (2 * (1 + lam)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hRd
  have hRone : R ≤ 1 := by nlinarith [mul_nonneg hlam hR.le]
  have hsmall : lam * R^2 ≤ (1 / 2 : ℝ) := by
    have hsq : R^2 ≤ R := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq hlam
    nlinarith [mul_nonneg hlam hR.le]
  let F0 := curvatureZeroJetBudget n K
  have hF0 : 0 ≤ F0 := curvatureZeroJetBudget_nonneg K hKn
  let B := 2 + F0 + R * F0
  have hB : 0 ≤ B := by positivity
  obtain ⟨J, hJ, henvelope⟩ := C04Aux.exists_uniform_radial_jet_envelope
    R lam B hR.le hlam hB hsmall (curvatureLowerJetBudget n K)
    (fun m L hL => curvatureLowerJetBudget_nonneg K hKn m hL)
  refine ⟨R, hR, J, hJ, ?_⟩
  intro M g p U hU hcurv
  have hb (x : ComplexVector n) (hx : x ∈ Metric.closedBall (0 : ComplexVector n) R) :
      unitaryExponential g p U x ∈ distBall g.form p (2 * r) ∧
      ‖radialCoframe g p U x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) ∧
      (realMapDeriv (unitaryExponential g p U) x).IsInvertible := by
    apply hseed M g p U hU (fun y hy => hcurv 0 y hy) x
    have hn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hA0 (x : ComplexVector n) (hx : x ∈ Metric.closedBall (0 : ComplexVector n) R) :
      ‖radialCoframe g p U x‖ ≤ 2 := by
    have hh := (hb x hx).2.1
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ComplexVector n)
    have ht := norm_add_le (radialCoframe g p U x - ContinuousLinearMap.id ℝ (ComplexVector n))
      (ContinuousLinearMap.id ℝ (ComplexVector n))
    rw [sub_add_cancel] at ht
    linarith
  have hcurvb (j : ℕ) (x : ComplexVector n) (hx : x ∈ Metric.closedBall (0 : ComplexVector n) R) :
      curvatureJetNorm g.form j (unitaryExponential g p U x) ≤ K j :=
    hcurv j _ (hb x hx).1
  let a := closedBallJetNorm R (radialCoframe g p U)
  let w := closedBallJetNorm R (radialConnection g p U)
  let f := closedBallJetNorm R (radialCurvatureOperator g p U)
  have ha0 : a 0 ≤ 2 := by
    apply closedBallJetNorm_le hR.le _ (radialCoframe_smooth g p U) 0
    intro x hx
    simpa only [norm_iteratedFDeriv_zero] using hA0 x hx
  have hf0 : f 0 ≤ F0 :=
    radialCurvatureOperator_jetMax_zero g p U hU K hKn hR.le (hcurvb 0) hA0
  have hw0 : w 0 ≤ R * F0 := by
    have hh := radialConnection_jetMax_integral_bound g p U hU hR.le 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hf0 hR.le)
  have hbound : ∀ m, a m ≤ J m ∧ w m ≤ J m ∧ f m ≤ J m := by
    apply henvelope a w f
    · intro m
      exact ⟨closedBallJetNorm_nonneg hR.le _ (radialCoframe_smooth g p U) m,
        closedBallJetNorm_nonneg hR.le _ (radialConnection_smooth g p U) m,
        closedBallJetNorm_nonneg hR.le _ (radialCurvatureOperator_smooth g p U hU) m⟩
    · exact ha0.trans (by dsimp [B]; nlinarith [mul_nonneg hR.le hF0])
    · exact hw0.trans (by dsimp [B]; nlinarith [mul_nonneg hR.le hF0])
    · exact hf0.trans (by dsimp [B]; nlinarith [mul_nonneg hR.le hF0])
    · intro m hm
      exact radialConnection_jetMax_integral_bound g p U hU hR.le m
    · intro m hm
      exact radialCoframe_jetMax_integral_bound g p U hR.le m hm
    · intro m hm L hL hlow
      exact radialCurvatureOperator_jetMax_top g p U hU K hKn hR.le m hm hL hcurvb hA0
        (fun k hk => ⟨(hlow k hk).1, (hlow k hk).2.1⟩)
  refine ⟨hb, ?_⟩
  intro m x hx
  exact ⟨(norm_iteratedFDeriv_le_closedBallJetNorm hR.le _ (radialCoframe_smooth g p U) m hx).trans (hbound m).1,
    (norm_iteratedFDeriv_le_closedBallJetNorm hR.le _ (radialConnection_smooth g p U) m hx).trans (hbound m).2.1,
    (norm_iteratedFDeriv_le_closedBallJetNorm hR.le _ (radialCurvatureOperator_smooth g p U hU) m hx).trans (hbound m).2.2⟩

end Yau.Proofs.C04ChartsAux
