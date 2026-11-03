import Yau.Proofs.V04FactorTransport

/-! Existential spectral-factor estimates supply the same constants for
every given factor of the same boundary matrix. Constants still precede
the discs, frames, and caller-supplied factors. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem spectralFactorEstimates_all_factors {d : VariationData X q} {a : ℕ}
    (h : SpectralFactorEstimates d a) :
    ∀ (j : ℕ) (δ : ℝ), 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : VariationDisc X) (E H Hinv : ℂ → CotangentMatrix n),
        AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
        SpectralFactorFor d j a δ F E H Hinv →
        (∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) ≤ (Real.sqrt δ)⁻¹) ∧
          matrixDSq (fun θ => Hinv (circlePoint θ)) ≤
            ENNReal.ofReal C * (1 + variationEnergy d j F) := by
  intro j δ hδ
  obtain ⟨C, hC, hbound⟩ := h j δ hδ
  refine ⟨C, hC, fun F E H Hinv hF hE hH => ?_⟩
  obtain ⟨K, Kinv, hK, hKnorm, hKsemi⟩ := hbound F E hF hE
  exact spectralFactorFor_transport_inverse_estimates hH hK hKnorm hKsemi

end Yau.Blueprint.V04Proof
