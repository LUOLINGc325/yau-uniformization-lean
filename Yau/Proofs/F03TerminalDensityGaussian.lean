import Yau.Proofs.F03GaussianLinearBudget
import Yau.Proofs.F03FlowTimeEnvelope

/-! The actual terminal flow density is Gaussian integrable, derived from the original supplied linear ball means. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem localizedFlow_terminal_density_gaussian_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    Integrable (fun y => Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*ρ y T) μ := by
  obtain ⟨A,hMean⟩ := hf.2.2.2.2.2.2.2.2.2.2.2.1 T hT
  have hSmooth := LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.2.1 hT
  have hNonnegative : ∀ y,0 ≤ ρ y T := fun y => (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  apply gaussian_linear_mean_integrable X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ o (fun y => ρ y T)
    (LeafProofs.L18Aux.continuous_of_smoothFn hSmooth).measurable hNonnegative
    (A := max A 1) (zero_le_one.trans (le_max_right _ _))
    (fun L hL => F02Aux.ballIntegralLE_mono_bound _ _ _ _ _
      (hMean μ hμ L hL T ⟨hT,le_rfl⟩)
      (mul_le_mul_of_nonneg_right (le_max_left A 1) (zero_le_one.trans hL))) hc hR

end Yau.Proofs.F03Aux
