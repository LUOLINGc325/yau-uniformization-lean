import Yau.Proofs.C02CompactJets
import Yau.Proofs.C02NormalCurvatureJetBound
import Yau.Proofs.C02CurvatureJetRecurrence
import Yau.Proofs.C02RadialMajorants

/-! Finite actual suprema of the genuine gauge fields on the already
fixed compact ball. These are temporary unknowns for absorption, never
inputs into the choice of radius. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance sup_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance sup_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance sup_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance sup_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance sup_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance sup_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalConnectionCurvature_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    ContDiff ℝ ∞ (normalConnectionCurvature g p U hU) :=
  connectionCurvature_smooth (normalConnection g p U hU) (normalConnection_smooth g p U hU)

def normalGaugeJetSuprema (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (ρ : ℝ) (m : ℕ) : GaugeJetRow where
  tensor j := compactJetNorm (normalCurvatureJet g p U hU j) (normalCurvatureJet_smooth g p U hU j) m ρ
  differential := compactJetNorm (normalDifferential g p U hU) (normalDifferential_smooth g p U hU) m ρ
  curvature := compactJetNorm (normalConnectionCurvature g p U hU) (normalConnectionCurvature_smooth g p U hU) m ρ
  connection := compactJetNorm (normalConnection g p U hU) (normalConnection_smooth g p U hU) m ρ

theorem normalGaugeJetSuprema_nonnegative (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (ρ : ℝ) (m : ℕ) :
    (normalGaugeJetSuprema g p U hU ρ m).Nonnegative :=
  ⟨fun j => compactJetNorm_nonneg _ _ m ρ, compactJetNorm_nonneg _ _ m ρ,
    compactJetNorm_nonneg _ _ m ρ, compactJetNorm_nonneg _ _ m ρ⟩

end Yau.Blueprint.C02Proof
