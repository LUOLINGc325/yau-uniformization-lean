import Yau.LeafProofs.L10DiscRotation

/-! The remaining boundary regularity step is isolated explicitly. Its
premises are all actual facts already proved for the Green solution. -/

noncomputable section
open scoped ContDiff

namespace Yau.LeafProofs

/-- Recovering every normal derivative from Poisson's equation and genuine
C¹ angular iterates on the closed disc. This proposition is not assumed
by any unconditional smoothness statement. -/
def DiscAngularBoundaryBootstrapGap : Prop :=
  ∀ (u f : ℂ → ℂ), ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1) →
    (∀ k : ℕ, ContDiffOn ℝ ∞ (discAngularIterate k u) (Metric.ball (0 : ℂ) 1)) →
    (∀ k : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      LeafCandidates.planarLaplacian (discAngularIterate k u) z = discAngularIterate k f z) →
    (∀ k : ℕ, ContDiffOn ℝ 1 (discAngularIterate k u) (Metric.closedBall (0 : ℂ) 1)) →
    ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)

theorem discGreenSolution_contDiffOn_of_angularBootstrap
    (hbootstrap : DiscAngularBoundaryBootstrapGap) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) := by
  apply hbootstrap (discGreenSolution f) f hf
  · exact discAngularIterate_green_contDiffOn_interior hf
  · exact fun k z hz => discAngularIterate_green_laplacian hf k hz
  · exact discAngularIterate_green_contDiffOn_one hf

end Yau.LeafProofs
