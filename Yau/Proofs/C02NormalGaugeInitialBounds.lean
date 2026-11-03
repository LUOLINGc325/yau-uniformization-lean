import Yau.Proofs.C02NormalGaugeJetSuprema
import Yau.Proofs.C02NormalGaugeLowOrder
import Yau.Proofs.C02RadialMajorantStep

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance ib_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance ib_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance ib_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance ib_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance ib_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance ib_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalGaugeJetSuprema_initial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hRm : ∀ j q, inducedDistance g.form p q ≤ 1 → curvatureJetNorm g.form j q ≤ K j) :
    (normalGaugeJetSuprema g p U hU (radialGaugeRadius (K 0)) 0).BoundedBy
      (initialGaugeJetRow K (radialGaugeRadius (K 0))) := by
  let ρ := radialGaugeRadius (K 0)
  have hImage (x : ComplexVector n) (hx : ‖x‖ ≤ ρ) :
      inducedDistance g.form p (normalRealMap g p U x) ≤ 1 :=
    (normalRealMap_distance_le g p U hU x).trans
      (hx.trans ((radialGaugeRadius_le_quarter (hK 0)).trans (by norm_num)))
  have hB (x : ComplexVector n) (hx : ‖x‖ ≤ ρ) : ‖normalDifferential g p U hU x‖ ≤ 3 / 2 :=
    (normalGauge_low_order g p U hU (hK 0) (hRm 0) x hx).2
  have hF (x : ComplexVector n) (hx : ‖x‖ ≤ ρ) :
      ‖normalConnectionCurvature g p U hU x‖ ≤ K 0 * (3 / 2) ^ 2 :=
    (normalConnectionCurvature_norm_le g p U hU x).trans
      (mul_le_mul (hRm 0 _ (hImage x hx))
        ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hB x hx)) (sq_nonneg _) (hK 0))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    apply compactJetNorm_le _ _ _ _ _ (hK j)
    intro x hx
    rw [norm_iteratedFDeriv_zero]
    have hx' : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact (normalCurvatureJet_norm_le g p U hU j x).trans (hRm j _ (hImage x hx'))
  · apply compactJetNorm_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)
    intro x hx
    rw [norm_iteratedFDeriv_zero]
    exact hB x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · apply compactJetNorm_le _ _ _ _ _ (mul_nonneg (hK 0) (sq_nonneg _))
    intro x hx
    rw [norm_iteratedFDeriv_zero]
    exact hF x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · apply compactJetNorm_le _ _ _ _ _ (mul_nonneg
      (div_nonneg (radialGaugeRadius_pos (hK 0)).le (by norm_num)) (mul_nonneg (hK 0) (sq_nonneg _)))
    intro x hx
    rw [norm_iteratedFDeriv_zero, normalConnection_homotopy]
    apply norm_radialHomotopy_le_on_ball _ (mul_nonneg (hK 0) (sq_nonneg _)) ?_ hx
    intro y hy
    exact hF y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)

end Yau.Blueprint.C02Proof
