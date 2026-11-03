import Yau.Proofs.D02PotentialL1
import Yau.Proofs.D02Riesz

/-! The limiting measure is constructed from the actual extracted disc
potentials. Its smooth density pairings, distribution and local finiteness
are tied to that same sequence and real local L¹ limit. -/

open scoped ENNReal Topology ContDiff CompactlySupported
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem discPotential_riesz_measure {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℝ) (μ : Measure ℂ), StrictMono φ ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ Metric.ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0)) ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ Metric.ball (0 : ℂ) 1 → μ S < ⊤) ∧
      μ (Metric.ball (0 : ℂ) 1)ᶜ = 0 ∧
      (∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Metric.ball (0 : ℂ) 1 →
        (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z) ∧
      (∀ χ : C_c(ℂ, ℝ), tsupport χ ⊆ Metric.ball (0 : ℂ) 1 →
        Tendsto (fun j => ∫ z, χ z ∂D02RieszAux.smoothRieszOn (Metric.ball (0 : ℂ) 1)
          (fun w => immersionPotential X.metric.form F (fs (φ j) w))) atTop (𝓝 (∫ z, χ z ∂μ))) := by
  obtain ⟨φ, u, hφ, hreg, hlocal⟩ := discPotential_rieszInputs X hF hImm hK A fs hfs
  obtain ⟨μ, hfinite, hzero, hdist, hvague⟩ := D02RieszAux.exists_riesz_measure Metric.isOpen_ball
    (fun j z => immersionPotential X.metric.form F (fs (φ j) z)) u
    (fun j => (hreg j).1) (fun j z hz => (hreg j).2 z hz)
    (fun S hS hSD => (hlocal S hS hSD).1) (fun S hS hSD => (hlocal S hS hSD).2)
  exact ⟨φ, u, μ, hφ, hlocal, hfinite, hzero, hdist, hvague⟩

end Yau.NodeProofs.D02Aux
