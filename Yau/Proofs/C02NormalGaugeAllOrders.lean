import Yau.Proofs.C02NormalGaugeInitialBounds
import Yau.Proofs.C02NormalGaugeTensorSupremum
import Yau.Proofs.C02NormalGaugeCurvatureSupremum
import Yau.Proofs.C02NormalGaugeHomotopySuprema
import Yau.Proofs.C02RadialMajorantDomination

/-! The explicit universal majorants bound every actual normal-gauge jet
on the single zeroth-curvature radius. No order-dependent radius occurs. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalGaugeJetSuprema_universal (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hRm : ∀ j q, inducedDistance g.form p q ≤ 1 → curvatureJetNorm g.form j q ≤ K j) :
    ∀ m, (normalGaugeJetSuprema g p U hU (radialGaugeRadius (K 0)) m).BoundedBy
      (radialJetMajorant K (radialGaugeRadius (K 0)) m) :=
  radialJetMajorant_dominates K hK (normalGaugeJetSuprema g p U hU (radialGaugeRadius (K 0)))
    (normalGaugeJetSuprema_nonnegative g p U hU (radialGaugeRadius (K 0)))
    (normalGaugeJetSuprema_initial g p U hU K hK hRm)
    (normalGaugeJetSuprema_tensor_succ g p U hU (radialGaugeRadius (K 0)))
    (normalGaugeJetSuprema_curvature g p U hU (radialGaugeRadius (K 0)))
    (normalGaugeJetSuprema_connection g p U hU (radialGaugeRadius_pos (hK 0)).le)
    (normalGaugeJetSuprema_differential g p U hU (radialGaugeRadius_pos (hK 0)).le)

end Yau.Blueprint.C02Proof
