import Yau.Proofs.D02PunctureEnergy
import Yau.Proofs.D02PhysicalExtraIntegrability
import Yau.Proofs.B01Standard

/-! The actual finite-energy normal limit is rescaled at an isolated atom.
Its genuine tangent pullback and the original D03 give the weighted energy
used by the removable-singularity construction. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem regular_limit_puncture_extraIntegrability {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (f : ℂ → Pt X) (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (regularPotentialDomain (ball (0 : ℂ) 1) μ))
    (B_F B_u : ℝ) (hBu : 0 ≤ B_u)
    (hbound : ∀ z ∈ regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ‖F (f z)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (f z) ≤ B_u)
    (henergy : (∫⁻ z in regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ENNReal.ofReal (hermitianNormSq (X.metric.form (f z)) (physicalCurveDerivative f z))) < ⊤)
    {z₀ : ℂ} (hz : z₀ ∈ ball (0 : ℂ) 1) :
    ∃ R ρ σ : ℝ, 0 < R ∧ closedBall z₀ R ⊆ ball (0 : ℂ) 1 ∧
      {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < R} ⊆ regularPotentialDomain (ball (0 : ℂ) 1) μ ∧
      ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (rescaledCurve f z₀ R) puncturedUnitDisc ∧
      (∀ z ∈ puncturedUnitDisc, ‖F (rescaledCurve f z₀ R z)‖ ≤ B_F) ∧
      0 < ρ ∧ ρ < 1 ∧ 0 < σ ∧ physicalWeightedEnergy X.metric.form (rescaledCurve f z₀ R) ρ σ < ⊤ := by
  obtain ⟨R, hR, hRD, hnear⟩ := exists_regular_punctured_disc μ hμ hz
  have hcurve := rescaledCurve_contMDiffOn_punctured hf z₀ hR hnear
  have hh := hcurve.mdifferentiableOn (by simp)
  have hE : (∫⁻ z in puncturedUnitDisc, ENNReal.ofReal
      (hermitianNormSq (X.metric.form (rescaledCurve f z₀ R z))
        (physicalCurveDerivative (rescaledCurve f z₀ R) z))) < ⊤ := by
    rw [rescaledCurve_unweighted_energy X.metric.form f z₀ R hR
      ((hf.mono hnear).mdifferentiableOn (by simp))]
    exact (lintegral_mono_set hnear).trans_lt henergy
  obtain ⟨B, c, hc⟩ := Yau.Proofs.B01Aux.standardDiscRealization
  obtain ⟨ρ, σ, hρ, hρ1, hσ, hExtra⟩ := physicalCurve_extraIntegrability X hF hImm
    (rescaledCurve f z₀ R) hh c hc hBu
    (fun z hz => (hbound _ (rescaledCurve_parameter_mem z₀ hR hnear hz)).2) hE
  refine ⟨R, ρ, σ, hR, hRD, hnear, hcurve, ?_, hρ, hρ1, hσ, hExtra⟩
  intro z hz
  exact (hbound _ (rescaledCurve_parameter_mem z₀ hR hnear hz)).1

end Yau.NodeProofs.D02Aux
