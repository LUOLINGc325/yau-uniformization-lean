import Yau.Proofs.C03SheetExtension
import Yau.Proofs.C03TargetPole
import Yau.Proofs.C03LeviGerms

/-! The actual target poles pull back along the same inverse sheet and
extend smoothly by zero, with no change of representative or pole order. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.NodeProofs.P03Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def sheetPole (O : Set (ComplexVector n)) (θ : ComplexVector n → ComplexVector n)
    (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (w0 : ComplexVector n) (j : ℕ) :
    ComplexVector n → ℝ :=
  sheetExtension O θ (TargetPole.translatedPole δ hδ m j w0)

theorem sheetPole_smooth_compact (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℝ ∞ θ O) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (w0 : ComplexVector n) (hsub : closedBall w0 δ ⊆ W) (j : ℕ) :
    ContDiff ℝ ∞ (sheetPole O θ δ hδ m w0 j) ∧
      HasCompactSupport (sheetPole O θ δ hδ m w0 j) ∧
      tsupport (sheetPole O θ δ hδ m w0 j) ⊆ σ '' closedBall w0 δ := by
  have hs := (TargetPole.translatedPole_tsupport_subset δ hδ m j w0).trans hsub
  have hc := TargetPole.translatedPole_hasCompactSupport δ hδ m j w0
  exact ⟨sheetExtension_contDiff O W hO σ θ hσ hσW hστ hθ _
      (TargetPole.translatedPole_contDiff δ hδ m j w0) hc hs,
    sheetExtension_compactSupport O W σ θ hσ hσW hστ _ hc hs,
    (sheetExtension_tsupport_subset O W σ θ hσ hσW hστ _ hc hs).trans
      (image_mono (TargetPole.translatedPole_tsupport_subset δ hδ m j w0))⟩

theorem sheetPole_nonpos (O : Set (ComplexVector n))
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (w0 : ComplexVector n) (j : ℕ) (z : ComplexVector n) :
    sheetPole O θ δ hδ m w0 j z ≤ 0 := by
  classical
  by_cases hz : z ∈ O
  · change (if z ∈ O then _ else _) ≤ _
    rw [if_pos hz]
    exact TargetPole.translatedPole_nonpos δ hδ m j w0 (θ z)
  · simp only [sheetPole, sheetExtension, if_neg hz, le_refl]

theorem sheetPole_antitone (O : Set (ComplexVector n))
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (w0 : ComplexVector n) (z : ComplexVector n) :
    Antitone (fun j => sheetPole O θ δ hδ m w0 j z) := by
  classical
  by_cases hz : z ∈ O
  · intro i j hij
    simpa only [sheetPole, sheetExtension, if_pos hz] using
      TargetPole.translatedPole_antitone δ hδ m w0 (θ z) hij
  · intro i j _
    simp only [sheetPole, sheetExtension, if_neg hz, le_refl]

theorem sheetPole_zero_germ (O W : Set (ComplexVector n))
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (w0 : ComplexVector n)
    (hsub : closedBall w0 δ ⊆ W) (j : ℕ) (z : ComplexVector n)
    (hz : z ∉ σ '' closedBall w0 δ) :
    sheetPole O θ δ hδ m w0 j =ᶠ[𝓝 z] fun _ => 0 := by
  apply sheetExtension_zero_germ O W σ θ hσ hσW hστ _
    (TargetPole.translatedPole_hasCompactSupport δ hδ m j w0)
    ((TargetPole.translatedPole_tsupport_subset δ hδ m j w0).trans hsub)
  exact fun H => hz (image_mono (TargetPole.translatedPole_tsupport_subset δ hδ m j w0) H)

theorem sheetPole_eq_on_inner (O : Set (ComplexVector n))
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (w0 : ComplexVector n) (j : ℕ) (z : ComplexVector n)
    (hz : z ∈ O) (hθz : θ z ∈ closedBall w0 (δ / 2)) :
    sheetPole O θ δ hδ m w0 j z =
      (m : ℝ) * (Real.log (‖θ z - w0‖ ^ 2 + poleEpsilon j) -
        Real.log (1 + δ ^ 2)) := by
  classical
  change (if z ∈ O then _ else _) = _
  rw [if_pos hz]
  exact TargetPole.translatedPole_eq_on_inner δ hδ m j w0 hθz

end Yau.Proofs.C03Aux
