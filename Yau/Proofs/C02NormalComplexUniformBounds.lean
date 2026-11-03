import Yau.Proofs.C02NormalComplexJetBounds
import Yau.Proofs.C02NormalComplexIntegrability
import Yau.Proofs.C02NormalComplexNormalization
import Yau.Proofs.C02NormalMetricJetBounds

/-! All normal-coordinate constants precede the metric, centre, unitary
frame and derivative order. The fields are the actual pulled-back fields. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem exists_uniform_normalComplex_geometry (n : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ jBound hBound : ℕ → ℝ,
      ∀ (M : ComplexManifold n) (g : SmoothMetric M) (p : M.Carrier)
        (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
        (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ),
      (∀ j y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form j y ≤ K j) →
      ContDiffOn ℝ ∞ (normalGaugeComplex g p U hU) (Metric.ball 0 ρ) ∧
      normalGaugeComplex g p U hU 0 = complexStructureCLM n ∧
      ∀ (x : ComplexVector n), ‖x‖ < ρ →
        (∀ z, normalGaugeComplex g p U hU x (normalGaugeComplex g p U hU x z) = -z) ∧
        (∀ v w, LeafCandidates.nijenhuis (normalGaugeComplex g p U hU) x v w = 0) ∧
        ‖normalGaugeComplex g p U hU x - complexStructureCLM n‖ ≤ 9 / 64 ∧
        ∀ m, ‖iteratedFDeriv ℝ m (normalGaugeComplex g p U hU) x‖ ≤ jBound m ∧
          ‖iteratedFDeriv ℝ m (normalGaugeMetric g p U hU) x‖ ≤ hBound m := by
  let ρ := radialGaugeRadius (K 0)
  let b := fun i => (radialJetMajorant K ρ i).differential
  refine ⟨ρ, radialGaugeRadius_pos (hK 0),
    binomialJetProduct (inverseJetMajorant b) b, binomialJetProduct b b, ?_⟩
  intro M g p U hU hRm
  refine ⟨(normalGaugeComplex_smoothOn g p U hU (hK 0) (hRm 0)).mono
    Metric.ball_subset_closedBall, normalGaugeComplex_zero g p U hU, ?_⟩
  intro x hx
  refine ⟨fun z => normalGaugeComplex_square g p U hU (hK 0) (hRm 0) x z hx.le,
    fun v w => normalGaugeComplex_nijenhuis_zero g p U hU (hK 0) (hRm 0) x hx v w,
    normalGaugeComplex_sub_standard_norm_le g p U hU (hK 0) (hRm 0) x hx.le, ?_⟩
  intro m
  exact ⟨normalGaugeComplex_jet_norm_le g p U hU K hK hRm m x hx.le,
    normalGaugeMetric_jet_norm_le g p U hU K hK hRm m x hx.le⟩

end Yau.Blueprint.C02Proof
