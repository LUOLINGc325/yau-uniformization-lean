import Yau.Proofs.C02NormalGaugeJetSuprema
import Yau.Proofs.C02CompactHomotopyJets
import Yau.Proofs.C02CompactJetContractions
import Yau.Proofs.C02CompactJetAddConstant

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}
local instance hs_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance hs_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance hs_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance hs_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance hs_two_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance hs_two_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem normalGaugeJetSuprema_connection (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    (normalGaugeJetSuprema g p U hU ρ (m + 1)).connection ≤
      ρ / ((m : ℝ) + 3) * (normalGaugeJetSuprema g p U hU ρ (m + 1)).curvature +
      ((m : ℝ) + 1) / ((m : ℝ) + 2) * (normalGaugeJetSuprema g p U hU ρ m).curvature := by
  let F := normalConnectionCurvature g p U hU
  have hF : ContDiff ℝ ∞ F := normalConnectionCurvature_smooth g p U hU
  have heq : normalConnection g p U hU = radialHomotopy F := funext (normalConnection_homotopy g p U hU)
  have hn := compactJetNorm_congr (normalConnection_smooth g p U hU) (radialHomotopy_smooth F hF) heq (m + 1) ρ
  exact hn.le.trans (compactJetNorm_radialHomotopy_le F hF hρ m)

theorem normalGaugeJetSuprema_differential (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    (normalGaugeJetSuprema g p U hU ρ (m + 1)).differential ≤
      ρ / ((m : ℝ) + 3) * (normalGaugeJetSuprema g p U hU ρ (m + 1)).connection +
      ((m : ℝ) + 1) / ((m : ℝ) + 2) * (normalGaugeJetSuprema g p U hU ρ m).connection := by
  let A := normalConnection g p U hU
  let L := ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)
  have hA : ContDiff ℝ ∞ A := normalConnection_smooth g p U hU
  have hLA : ContDiff ℝ ∞ (L ∘ A) := L.toContinuousLinearEquiv.contDiff.comp hA
  have hH := radialHomotopy_smooth (L ∘ A) hLA
  have heq : normalDifferential g p U hU = fun y => ContinuousLinearMap.id ℝ (ComplexVector n) +
      radialHomotopy (L ∘ A) y := funext (normalDifferential_homotopy g p U hU)
  have hn := compactJetNorm_congr (normalDifferential_smooth g p U hU) (contDiff_const.add hH) heq (m + 1) ρ
  have hc := compactJetNorm_const_add_succ (ContinuousLinearMap.id ℝ (ComplexVector n))
    (radialHomotopy (L ∘ A)) hH m ρ
  have hb := compactJetNorm_radialHomotopy_le (L ∘ A) hLA hρ m
  rw [compactJetNorm_isometry L A hA (m + 1) ρ, compactJetNorm_isometry L A hA m ρ] at hb
  exact (hn.trans hc).le.trans hb

end Yau.Blueprint.C02Proof
