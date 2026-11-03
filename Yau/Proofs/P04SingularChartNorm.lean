import Yau.Proofs.P04CanonicalChartIntegral
import Yau.Proofs.P04PolePowerLimit

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual canonical density cancellation and Fatou give the precise
singular coefficient norm, with the same uniform bound. -/
theorem singular_chart_norm_of_regularized_bounds (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p : M.Carrier)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ chartTarget p) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (chartPt p p) ρ ⊆ chartTarget p)
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1)
    {c : ℝ} (hc : 0 < c) (k : ℝ) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (u : NQForm (CanonicalCoefficients M) 0)
    (hu : LocallyL2 (r := 1) (CanonicalCoefficients M) u) (B : ℝ≥0∞)
    (hbound : ∀ j : ℕ, weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
      (regularizedPoleWeight p χ c k ψ (poleEpsilon ρ j)) u ≤ B) :
    (∫⁻ z in Metric.ball (chartPt p p) ρ, ENNReal.ofReal
      (‖coefficients (r := 1) (CanonicalCoefficients M) u p z Fin.elim0 0‖^2*
        Real.exp (-(k*inChart p ψ z))*‖z-chartPt p p‖^(-2*c)) ∂lebesgueC n) ≤ B := by
  let b := fun z => coefficients (r := 1) (CanonicalCoefficients M) u p z Fin.elim0 0
  have hb : AEMeasurable b ((lebesgueC n).restrict (Metric.ball (chartPt p p) ρ)) := by
    have H := (hu p Fin.elim0 0).1.aemeasurable
    rw [coefficient_localDomain] at H
    exact H.mono_measure (Measure.restrict_mono hball le_rfl)
  have hΦ : AEMeasurable (fun z => k*inChart p ψ z)
      ((lebesgueC n).restrict (Metric.ball (chartPt p p) ρ)) :=
    ((continuousOn_const.mul (hψ p).continuousOn).mono hball).aemeasurable
      Metric.isOpen_ball.measurableSet
  apply regularized_pole_integrals_bound_singular (chartPt p p) ρ hc
    (Metric.ball (chartPt p p) ρ) b (fun z => k*inChart p ψ z) hb hΦ B
  intro j
  have hε := poleEpsilon_pos hρ j
  let φ := regularizedPoleWeight p χ c k ψ (poleEpsilon ρ j)
  have hφ : SmoothFn φ := regularizedPoleWeight_smooth p hχ hcχ hs c k hψ hε
  calc
    _ = ∫⁻ z in Metric.ball (chartPt p p) ρ,
        ENNReal.ofReal (‖b z‖^2*Real.exp (-inChart p φ z)) ∂lebesgueC n := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      congr 1
      have he := regularizedPoleModel_exp_factor χ (chartPt p p) c hε
        (fun z => k*inChart p ψ z) z
      rw [hone z (Metric.ball_subset_closedBall hz),mul_one] at he
      rw [show inChart p φ z=k*inChart p ψ z+
        regularizedPoleModel χ (chartPt p p) c (poleEpsilon ρ j) z from
        regularizedPoleWeight_inChart p χ c k ψ _ (hball hz),he]
      ring
    _ ≤ ∫⁻ z in chartTarget p, ENNReal.ofReal (‖b z‖^2*Real.exp (-inChart p φ z)) ∂lebesgueC n :=
      lintegral_mono_set hball
    _ ≤ weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ φ u :=
      flat_weighted_top_chart_le g μ hμ φ hφ u hu p
    _ ≤ B := hbound j

end Yau.Proofs.P04Aux
