import Yau.Proofs.C02FiniteJetEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Quantitative composition on fixed open domains, with a finite
envelope at each derivative order. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_comp_on_le
    {O : Set D} {V : Set E} (hO : IsOpen O) (hV : IsOpen V)
    {f : D → E} {g : E → F} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g V)
    (hMaps : MapsTo f O V) {x : D} (hx : x ∈ O) (m : ℕ) (a b : ℕ → ℝ)
    (hOuter : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ a i)
    (hInner : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ b i) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤
      (m.factorial : ℝ) * finiteJetEnvelope a m * finiteJetEnvelope b m ^ m := by
  have hh := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := m)
    hg hf (show (m : ℕ∞ω) ≤ ∞ by simp) hV.uniqueDiffOn hO.uniqueDiffOn hMaps hx
    (C := finiteJetEnvelope a m) (D := finiteJetEnvelope b m)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hV (hMaps hx)]
      exact (hOuter i hi).trans (le_finiteJetEnvelope a hi))
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i hO hx]
      exact (hInner i hi him).trans (le_finiteJetEnvelope_pow b hi him))
  rwa [iteratedFDerivWithin_of_isOpen m hO hx] at hh

end Yau.Blueprint.C02Proof
