import Mathlib

/-! Actual compact maxima of the jets of one smooth map. -/
noncomputable section
open scoped ContDiff Topology
namespace Yau.Proofs.C04ChartsAux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def closedBallJetNorm (R : ℝ) (f : E → F) (m : ℕ) : ℝ :=
  sSup ((fun x => ‖iteratedFDeriv ℝ m f x‖) '' Metric.closedBall (0 : E) R)

theorem closedBallJetNorm_attained {R : ℝ} (hR : 0 ≤ R) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ∃ x ∈ Metric.closedBall (0 : E) R, closedBallJetNorm R f m = ‖iteratedFDeriv ℝ m f x‖ ∧
      ∀ y ∈ Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ m f y‖ ≤ ‖iteratedFDeriv ℝ m f x‖ := by
  exact (isCompact_closedBall (0 : E) R).exists_sSup_image_eq_and_ge
    ⟨0, Metric.mem_closedBall_self hR⟩
    ((hf.continuous_iteratedFDeriv (by simp)).norm.continuousOn)

theorem closedBallJetNorm_nonneg {R : ℝ} (hR : 0 ≤ R) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) : 0 ≤ closedBallJetNorm R f m := by
  obtain ⟨x, hx, heq, hb⟩ := closedBallJetNorm_attained hR f hf m
  rw [heq]
  exact norm_nonneg _

theorem norm_iteratedFDeriv_le_closedBallJetNorm {R : ℝ} (hR : 0 ≤ R) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) {x : E} (hx : x ∈ Metric.closedBall (0 : E) R) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ closedBallJetNorm R f m := by
  obtain ⟨y, hy, heq, hb⟩ := closedBallJetNorm_attained hR f hf m
  rw [heq]
  exact hb x hx

theorem closedBallJetNorm_le {R C : ℝ} (hR : 0 ≤ R) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (hbound : ∀ x ∈ Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ m f x‖ ≤ C) :
    closedBallJetNorm R f m ≤ C := by
  obtain ⟨x, hx, heq, hb⟩ := closedBallJetNorm_attained hR f hf m
  rw [heq]
  exact hbound x hx

end Yau.Proofs.C04ChartsAux
