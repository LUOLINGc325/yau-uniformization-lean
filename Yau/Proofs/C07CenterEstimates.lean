import Yau.Proofs.C07CenterContraction
import Yau.Proofs.C07CenterDeterminant
import Yau.Proofs.C07InverseContraction
import Yau.Proofs.C07MetricTimeMonotonicity

/-! All three center estimates for the same actual flow transition germ. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem transition_center_estimates {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X} (hflow : FlowStage X o h U P ρ)
    (hjoint : JointPositivity X h)
    {Φ Ψ : ComplexVector n → Pt X} {F : ComplexVector n → ComplexVector n}
    {t u r R q c C c' C' : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (hq : 0 < q) (hR : 0 < R)
    (hΦ : UnitaryChart (h t) o Φ r c C)
    (hΨ : UnitaryChart (h u) o Ψ R c' C')
    (hF : DifferentiableOn ℂ F (Metric.ball 0 q)) (hFzero : F 0 = 0)
    (hgerm : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z) :
    ‖fderiv ℂ F 0‖ ≤ 1 ∧
      ‖LinearMap.det (fderiv ℂ F 0).toLinearMap‖ =
        Real.exp (-(ρ o u - ρ o t) / 2) ∧
      ‖(fderiv ℂ F 0).inverse‖ ≤ Real.exp ((ρ o u - ρ o t) / 2) := by
  have hnorm := transition_center_contraction hq hR hΦ hΨ hF hFzero hgerm
    (joint_metric_antitone hflow hjoint o ht htu)
  have hdet := transition_center_det_norm hflow ht (ht.trans htu) hq hR
    hΦ hΨ hF hFzero hgerm
  have hinv := centerDeriv_inverse_norm_of_det_exp F ((ρ o u - ρ o t) / 2)
    (by simpa only [neg_div] using hdet) hnorm
  exact ⟨hnorm, hdet, hinv⟩

end Yau.Proofs.C07Aux
