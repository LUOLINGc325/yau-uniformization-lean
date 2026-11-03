import Yau.Proofs.C02NormalComplexStructure
import Yau.Proofs.C02ComplexPullbackCloseness

/-! Exact origin normalization and a uniform smallness bound for the
actual normal-gauge complex structure, on the original curvature radius. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalGaugeComplex_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    normalGaugeComplex g p U hU 0 = complexStructureCLM n := by
  have hId := actual_inverse_identities_of_close_identity
    (ContinuousLinearMap.id ℝ (ComplexVector n)) (by simp)
  have hInv : (ContinuousLinearMap.id ℝ (ComplexVector n)).inverse =
      ContinuousLinearMap.id ℝ (ComplexVector n) := by simpa using hId.1
  simp only [normalGaugeComplex, normalDifferential_zero, hInv,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

theorem normalGaugeComplex_sub_standard_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    ‖normalGaugeComplex g p U hU x - complexStructureCLM n‖ ≤ 9 / 64 := by
  have hB := (normalGauge_low_order g p U hU hK hRm x hx).1
  exact (complexPullback_sub_standard_norm_le _ (hB.trans (by norm_num))).trans
    ((mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num))

end Yau.Blueprint.C02Proof
