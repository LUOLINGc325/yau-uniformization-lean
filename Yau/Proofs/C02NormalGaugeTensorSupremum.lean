import Yau.Proofs.C02NormalGaugeJetSuprema
import Yau.Proofs.C02JetProductBounds

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem normalGaugeJetSuprema_tensor_succ (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (ρ : ℝ) (j m : ℕ) :
    (normalGaugeJetSuprema g p U hU ρ (m + 1)).tensor j ≤
      binomialJetProduct (fun i => (normalGaugeJetSuprema g p U hU ρ i).tensor (j + 1))
        (fun i => (normalGaugeJetSuprema g p U hU ρ i).differential) m +
      (4 + j) * binomialJetProduct (fun i => (normalGaugeJetSuprema g p U hU ρ i).tensor j)
        (fun i => (normalGaugeJetSuprema g p U hU ρ i).connection) m := by
  let J := normalGaugeJetSuprema g p U hU ρ
  have hJ (i : ℕ) := normalGaugeJetSuprema_nonnegative g p U hU ρ i
  have hC : 0 ≤ binomialJetProduct (fun i => (J i).tensor (j + 1)) (fun i => (J i).differential) m +
      (4 + j) * binomialJetProduct (fun i => (J i).tensor j) (fun i => (J i).connection) m :=
    add_nonneg (binomialJetProduct_nonneg (fun i => (hJ i).1 _) (fun i => (hJ i).2.1) m)
      (mul_nonneg (by positivity) (binomialJetProduct_nonneg (fun i => (hJ i).1 _)
        (fun i => (hJ i).2.2.2) m))
  apply compactJetNorm_le _ _ _ _ _ hC
  intro x hx
  apply (normalCurvatureJet_succ_norm_le g p U hU j m x).trans
  apply add_le_add
  · apply binomialJetProduct_mono m
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_nonneg _
    · intro i hi; exact (hJ i).2.1
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply binomialJetProduct_mono m
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_nonneg _
    · intro i hi; exact (hJ i).2.2.2

end Yau.Blueprint.C02Proof
