import Yau.Proofs.C02NormalGaugeJetSuprema
import Yau.Proofs.C02JetProductBounds

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

local instance cs_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cs_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cs_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cs_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cs_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cs_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalGaugeJetSuprema_curvature (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (ρ : ℝ) (m : ℕ) :
    (normalGaugeJetSuprema g p U hU ρ m).curvature ≤
      binomialJetProduct (binomialJetProduct (fun i => (normalGaugeJetSuprema g p U hU ρ i).tensor 0)
        (fun i => (normalGaugeJetSuprema g p U hU ρ i).differential))
        (fun i => (normalGaugeJetSuprema g p U hU ρ i).differential) m := by
  let J := normalGaugeJetSuprema g p U hU ρ
  have hJ (i : ℕ) := normalGaugeJetSuprema_nonnegative g p U hU ρ i
  have hInner (k : ℕ) : 0 ≤ binomialJetProduct (fun i => (J i).tensor 0) (fun i => (J i).differential) k :=
    binomialJetProduct_nonneg (fun i => (hJ i).1 0) (fun i => (hJ i).2.1) k
  apply compactJetNorm_le _ _ _ _ _ (binomialJetProduct_nonneg hInner (fun i => (hJ i).2.1) m)
  intro x hx
  apply (normalConnectionCurvature_jet_norm_le g p U hU m x).trans
  apply binomialJetProduct_mono m
  · intro k hk
    apply binomialJetProduct_mono k
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
    · intro i hi; exact norm_nonneg _
    · intro i hi; exact (hJ i).2.1
  · intro i hi; exact norm_iteratedFDeriv_le_compactJetNorm _ _ i ρ hx
  · intro k hk
    exact binomialJetProduct_nonneg (fun i => norm_nonneg _) (fun i => norm_nonneg _) k
  · intro i hi; exact (hJ i).2.1

end Yau.Blueprint.C02Proof
