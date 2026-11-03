import Yau.Proofs.F03TerminalDensityGaussian

/-! A genuine integrable Gaussian envelope controls both constants and the terminal density. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem localizedFlow_gaussian_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    Integrable (fun y => Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)) μ := by
  have hInt := gaussian_linear_mean_integrable X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ o (fun _ => (1:ℝ))
    measurable_const (fun _ => zero_le_one) (A := 1) zero_le_one
    (fun L hL => by
      unfold BallIntegralLE
      simp only [ENNReal.ofReal_one,lintegral_const,Measure.restrict_apply_univ,one_mul]
      exact le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr hL)) hc hR
  simpa only [mul_one] using hInt

theorem localizedFlow_terminal_envelope_gaussian_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    Integrable (fun y => Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*(1+ρ y T)) μ := by
  convert (localizedFlow_gaussian_integrable X o h U P ρ hf μ hμ hc hR).add
    (localizedFlow_terminal_density_gaussian_integrable X o h U P ρ hf hT μ hμ hc hR) using 1
  funext y
  change Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*(1+ρ y T)=
    Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)+
      Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*ρ y T
  ring

end Yau.Proofs.F03Aux
