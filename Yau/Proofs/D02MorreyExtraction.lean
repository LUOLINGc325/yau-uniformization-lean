import Yau.Proofs.D02LocalMorrey
import Yau.Proofs.D02ConcentrationDomain

/-! One actual extraction has the original compact L¹ limit and Riesz
measure, together with uniform local Hölder control away from its atoms. -/

open scoped Topology ContDiff ENNReal CompactlySupported
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem discFamily_riesz_morrey_subsequence {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℝ) (μ : Measure ℂ), StrictMono φ ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0)) ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → μ S < ⊤) ∧
      μ (ball (0 : ℂ) 1)ᶜ = 0 ∧
      (∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball (0 : ℂ) 1 →
        (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z) ∧
      (∀ χ : C_c(ℂ, ℝ), tsupport χ ⊆ ball (0 : ℂ) 1 →
        Tendsto (fun j => ∫ z, χ z ∂D02RieszAux.smoothRieszOn (ball (0 : ℂ) 1)
          (fun w => immersionPotential X.metric.form F (fs (φ j) w))) atTop (𝓝 (∫ z, χ z ∂μ))) ∧
      (concentrationAtoms (ball (0 : ℂ) 1) μ).Countable ∧
      IsOpen (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      IsPathConnected (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      ∀ z₀ ∈ regularPotentialDomain (ball (0 : ℂ) 1) μ,
        ∃ r H : ℝ, 0 < r ∧ closedBall z₀ (2 * r) ⊆ ball (0 : ℂ) 1 ∧ 0 ≤ H ∧
          ∀ j z, z ∈ ball z₀ r → ∀ w, w ∈ ball z₀ r →
            lengthDist X.metric.form (fs (φ j) z) (fs (φ j) w) ≤ H * ‖z - w‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨φ, u, μ, hφ, hlocal, hμ, hzero, hdist, hvague⟩ :=
    discPotential_riesz_measure X hF hImm hK A fs hfs
  refine ⟨φ, u, μ, hφ, hlocal, hμ, hzero, hdist, hvague,
    concentrationAtoms_countable isOpen_ball μ hμ,
    regularPotentialDomain_isOpen isOpen_ball μ hμ,
    regularPotentialDisc_isPathConnected μ hμ, ?_⟩
  intro z₀ hz
  exact local_uniform_disc_morrey X hF hImm hK (fun j => fs (φ j))
    (fun j => ⟨(hfs (φ j)).1, (hfs (φ j)).2.1⟩) u μ hlocal hμ hvague hz.1 hz.2

end Yau.NodeProofs.D02Aux
