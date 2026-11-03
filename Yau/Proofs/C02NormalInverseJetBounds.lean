import Yau.Proofs.C02NormalGaugeAllOrders
import Yau.Proofs.C02NormalGaugeLowOrder
import Yau.Proofs.C02InverseFieldJets
import Yau.Proofs.C02InverseJetDomination

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalDifferential_inverse_jet_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hRm : ∀ j y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form j y ≤ K j)
    (m : ℕ) (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius (K 0)) :
    ‖iteratedFDeriv ℝ m (fun y => (normalDifferential g p U hU y).inverse) x‖ ≤
      inverseJetMajorant (fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential) m := by
  let B := normalDifferential g p U hU
  let b := fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential
  let a := fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖
  have hB : ContDiff ℝ ∞ B := normalDifferential_smooth g p U hU
  have hb (i : ℕ) : 0 ≤ b i :=
    (radialJetMajorant_nonnegative hK (radialGaugeRadius_pos (hK 0)).le i).2.1
  have hbound (i : ℕ) : ‖iteratedFDeriv ℝ i B x‖ ≤ b i :=
    (norm_iteratedFDeriv_le_compactJetNorm _ _ i _ (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans
        (normalGaugeJetSuprema_universal g p U hU K hK hRm i).2.1
  have hClose : ‖B x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4 :=
    (normalGauge_low_order g p U hU (hK 0) (hRm 0) x hx).1.trans (by norm_num)
  have hInv : (B x).IsInvertible := isInvertible_of_close_identity (B x) hClose
  have h0 : a 0 ≤ 2 := by
    dsimp only [a]
    rw [norm_iteratedFDeriv_zero]
    exact norm_actual_inverse_of_close_identity (B x) hClose
  apply inverseJetMajorant_dominates a b (fun i => norm_nonneg _) hb h0 _ m
  intro k
  apply (actualInverseField_jet_norm_le hB hInv k).trans
  apply binomialJetProduct_mono k
  · intro j hj
    apply binomialJetProduct_mono j
    · intro i hi; exact le_refl _
    · intro i hi; exact hbound (i + 1)
    · intro i hi; exact norm_nonneg _
    · intro i hi; exact hb (i + 1)
  · intro i hi; exact le_refl _
  · intro j hj
    exact binomialJetProduct_nonneg (fun i => norm_nonneg _) (fun i => norm_nonneg _) j
  · intro i hi; exact norm_nonneg _

end Yau.Blueprint.C02Proof
