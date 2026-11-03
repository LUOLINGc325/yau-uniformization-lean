import Yau.LeafProofs.L17HolomorphicRegularity
import Yau.Proofs.Y01TransitionBounds

/-! The original complex-differentiability field of ShrinkingCharts gives
C-infinity regularity of that same F, using the accepted L17 regularity theorem. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint
open scoped ContDiff

variable {n : ℕ}

theorem shrinking_transition_smooth
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {t t' : ℝ} (ht : t₀ ≤ t) (htt' : t ≤ t') :
    ContDiffAt ℂ ∞ (F t t') 0 ∧ F t t' 0 = 0 := by
  obtain ⟨hr₁, hr₁r₀, hσ, hC, hunit, htransition, hcocycle, hcenter,
    hinverseCharts, hdecay, hjets, hsmall⟩ := hcharts
  obtain ⟨hDiff, hRange, hZero, hGerm, hNorm, hDet, hInv⟩ := htransition t t' ht htt'
  have hSmooth := Yau.LeafProofs.L17Holomorphic.complexVector_contDiffOn Metric.isOpen_ball hDiff
  exact ⟨hSmooth.contDiffAt (Metric.ball_mem_nhds 0 hr₁), hZero⟩

end Yau.Proofs.Y01Aux
