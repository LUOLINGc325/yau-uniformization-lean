import Yau.Proofs.C02ParallelComplexConstant
import Yau.Proofs.C02NormalGaugeLowOrder
import Yau.Proofs.C02NormalDifferentialCoords

/-! The actual complex structure pulled back through the nonsingular
normal differential, with smoothness and exact target-chart intertwining. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalGaugeComplex (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  (normalDifferential g p U hU x).inverse.comp
    ((complexStructureCLM n).comp (normalDifferential g p U hU x))

theorem normalGaugeComplex_apply (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x z : ComplexVector n) :
    normalGaugeComplex g p U hU x z =
      (normalDifferential g p U hU x).inverse (Complex.I • normalDifferential g p U hU x z) := rfl

theorem normalGaugeComplex_smoothOn (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K) :
    ContDiffOn ℝ ∞ (normalGaugeComplex g p U hU) (Metric.closedBall (0 : ComplexVector n) (radialGaugeRadius K)) := by
  have hB : ContDiffOn ℝ ∞ (normalDifferential g p U hU)
      (Metric.closedBall (0 : ComplexVector n) (radialGaugeRadius K)) :=
    (normalDifferential_smooth g p U hU).contDiffOn
  have hInv := contDiffOn_actual_inverse_of_close_identity hB (fun x hx =>
    (normalGauge_low_order g p U hU hK hRm x (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).1.trans (by norm_num))
  exact hInv.clm_comp (contDiffOn_const.clm_comp hB)

theorem normalGaugeComplex_reconstruct (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (x z : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    normalDifferential g p U hU x (normalGaugeComplex g p U hU x z) =
      Complex.I • normalDifferential g p U hU x z := by
  have hClose := (normalGauge_low_order g p U hU hK hRm x hx).1.trans (show (9 / 256 : ℝ) ≤ 1 / 4 by norm_num)
  have h := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n =>
    L (Complex.I • normalDifferential g p U hU x z)) (actual_inverse_identities_of_close_identity _ hClose).2
  exact h

theorem normalGaugeComplex_square (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (x z : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K) :
    normalGaugeComplex g p U hU x (normalGaugeComplex g p U hU x z) = -z := by
  have hClose := (normalGauge_low_order g p U hU hK hRm x hx).1.trans (show (9 / 256 : ℝ) ≤ 1 / 4 by norm_num)
  have hLeft := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L z)
    (actual_inverse_identities_of_close_identity _ hClose).1
  rw [normalGaugeComplex_apply, normalGaugeComplex_reconstruct g p U hU hK hRm x z hx,
    smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  exact congrArg Neg.neg hLeft

theorem normalGaugeComplex_intertwines (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (c : M.Carrier) (x z : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius K)
    (hc : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    fderiv ℝ (normalCoordinateMap g p U c) x (normalGaugeComplex g p U hU x z) =
      Complex.I • fderiv ℝ (normalCoordinateMap g p U c) x z := by
  rw [← normalDifferential_coords g p U hU c x _ hc,
    normalGaugeComplex_reconstruct g p U hU hK hRm x z hx,
    normalParallelCoefficients_I g p U hU c x _ hc, normalDifferential_coords g p U hU c x z hc]

end Yau.Blueprint.C02Proof
