import Yau.Proofs.C02NormalComplexStructure
import Yau.Proofs.C02NormalInverseJetBounds
import Yau.Proofs.C02ComplexPullbackOperator

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance cj_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cj_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalGaugeComplex_jet_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hRm : ∀ j y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form j y ≤ K j)
    (m : ℕ) (x : ComplexVector n) (hx : ‖x‖ ≤ radialGaugeRadius (K 0)) :
    ‖iteratedFDeriv ℝ m (normalGaugeComplex g p U hU) x‖ ≤
      binomialJetProduct
        (inverseJetMajorant (fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential))
        (fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential) m := by
  let B := normalDifferential g p U hU
  let C := fun y => (B y).inverse
  let b := fun i => (radialJetMajorant K (radialGaugeRadius (K 0)) i).differential
  let O := {y | (B y).IsInvertible}
  have hB : ContDiff ℝ ∞ B := normalDifferential_smooth g p U hU
  have hO : IsOpen O := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hB.continuous
  have hC : ContDiffOn ℝ ∞ C O := by
    intro y hy
    exact (hy.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt y (hB.contDiffOn y hy)
  have hxO : x ∈ O := isInvertible_of_close_identity (B x)
    ((normalGauge_low_order g p U hU (hK 0) (hRm 0) x hx).1.trans (by norm_num))
  have hbound (i : ℕ) : ‖iteratedFDeriv ℝ i B x‖ ≤ b i :=
    (norm_iteratedFDeriv_le_compactJetNorm _ _ i _ (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans
        (normalGaugeJetSuprema_universal g p U hU K hK hRm i).2.1
  have heq : normalGaugeComplex g p U hU = fun y => complexPullbackOperator n (C y) (B y) := rfl
  rw [heq]
  exact (norm_iteratedFDeriv_bilinearOn_le (complexPullbackOperator n)
    (complexPullbackOperator_norm_le_one n) hO hC hB.contDiffOn hxO m).trans
      (binomialJetProduct_mono m
        (fun i hi => normalDifferential_inverse_jet_norm_le g p U hU K hK hRm i x hx)
        (fun i hi => hbound i) (fun i hi => norm_nonneg _)
        (fun i hi => (radialJetMajorant_nonnegative hK (radialGaugeRadius_pos (hK 0)).le i).2.1))

end Yau.Blueprint.C02Proof
