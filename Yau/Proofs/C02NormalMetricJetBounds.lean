import Yau.Proofs.C02NormalGaugeAllOrders
import Yau.Proofs.C02NormalPullbackMetric
import Yau.Proofs.C02GramOperator
import Yau.Proofs.C02BilinearJetBound
import Yau.Proofs.C02JetProductBounds

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance mg_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance mg_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance mg_dual_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance mg_dual_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance mg_form_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance mg_form_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance

theorem normalGaugeMetric_jet_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hRm : ∀ j y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form j y ≤ K j)
    (m : ℕ) (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius (K 0)) :
    ‖iteratedFDeriv ℝ m (normalGaugeMetric g p U hU) x‖ ≤
      binomialJetProduct (fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential)
        (fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential) m := by
  let B := normalDifferential g p U hU
  have hB : ContDiff ℝ ∞ B := normalDifferential_smooth g p U hU
  have heq : normalGaugeMetric g p U hU = fun y => gramOperator (ComplexVector n) (B y) (B y) := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hbound (i : ℕ) : ‖iteratedFDeriv ℝ i B x‖ ≤
      (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential :=
    (norm_iteratedFDeriv_le_compactJetNorm _ _ i _ (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans
        (normalGaugeJetSuprema_universal g p U hU K hK hRm i).2.1
  rw [heq]
  exact (norm_iteratedFDeriv_bilinear_le (gramOperator (ComplexVector n))
    (gramOperator_norm_le_one (ComplexVector n)) hB hB x m).trans
      (binomialJetProduct_mono m (fun i hi => hbound i) (fun i hi => hbound i)
        (fun i hi => norm_nonneg _) (fun i hi =>
          (radialJetMajorant_nonnegative hK (radialGaugeRadius_pos (hK 0)).le i).2.1))

end Yau.Blueprint.C02Proof
