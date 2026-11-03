import Yau.Proofs.F04ZeroPastDivergence

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- Homogeneous nondivergence equations have a genuine zero-past weak
 extension with the same actual coefficients and computed energy drift. -/
theorem zeroPast_homogeneous_weakEquation {n : ℕ} {O : Set (Space n)}
    (hO : MeasurableSet O) {l s K : ℝ} (hl : l ≤ 0) (hK : 0 ≤ K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hFlux : ∀ i, MemLp (fun p => energyFlux a G p i) 2 (productVolume O (Ioo 0 s)))
    (hDrift : MemLp (fun p => ∑ i, energyDrift a b p i * G p i) 2 (productVolume O (Ioo 0 s)))
    (hGrowth : ∀ p ∈ O ×ˢ Ioo 0 s, |u p| ≤ K * p.2)
    (hWeak : WeakEquation O (Ioo 0 s) a b (fun _ => 0) u G) :
    WeakEquation O (Ioo l s) a b (fun _ => 0)
      (zeroPast u) (fun p i => zeroPast (fun q => G q i) p) := by
  have hh := zeroPast_weakDivergence hO hl hK hu hFlux hDrift hGrowth
    (weakEquation_homogeneous_divergence hWeak)
  have hP : (fun p i => zeroPast (fun q => energyFlux a G q i) p) =
      energyFlux a (fun p i => zeroPast (fun q => G q i) p) := by
    funext p i
    by_cases hp : 0 < p.2 <;> simp [zeroPast, hp, energyFlux]
  have hR : zeroPast (fun p => ∑ i, energyDrift a b p i * G p i) =
      (fun p => ∑ i, energyDrift a b p i * zeroPast (fun q => G q i) p) := by
    funext p
    by_cases hp : 0 < p.2 <;> simp [zeroPast, hp]
  rw [hP, hR] at hh
  intro φ hφ
  have he := hh φ hφ
  simpa only [zero_mul, integral_zero, energyFlux, energyDrift, Finset.sum_mul] using he

end Yau.F04Proof
