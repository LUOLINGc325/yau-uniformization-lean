import Yau.Proofs.B01Positivity

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle MeasureTheory

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

theorem bundleToEmbeddedReduction : BundleToEmbeddedReduction := by
  intro hEmbedded M c hc r q E _ _ _ _ _ _ _ k A hE hk hG hHA hA hBound s hs hInt
  have hFrames := (imageLocalFrameTransport E c hc A hE hHA hA).2
  have hPositive := imagePositivityTransport E c hc k A hA hE hk hG hHA
  obtain ⟨C, hC, hBound⟩ := hBound
  have hImageBound := imageBoundTransport E c k A hA C hBound
  have hSection := imageSectionTransport E c hc A hE hHA s hs
  have hIntegral := imageIntegralTransport E c hc k A hA hE hk hHA s hs
  obtain ⟨ρ, σ, hρ, hρ1, hσ, hFin⟩ := hEmbedded q r (imageFibers E c A)
    (imageMetric E c k A hA) hFrames hPositive ⟨C, hC, hImageBound⟩
    (imageSection E c A s) hSection.1 hSection.2 (hIntegral.1 ▸ hInt)
  exact ⟨ρ, σ, hρ, hρ1, hσ, (hIntegral.2 ρ σ hρ hρ1).symm ▸ hFin⟩

end Yau.Proofs.B01Aux
