import Yau.Proofs.V03PositiveDisc
import Yau.Proofs.V03FourierMean

/-! A scalar outer candidate is constructed from the actual positive
Fourier power series. Its positive real center is computed exactly. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def outerExponent (q : ℝ → ℝ) (a : ℕ) (z : ℂ) : ℂ :=
  (a : ℂ) * (2 * positiveDiscProjection (fun θ => (q θ : ℂ)) z - (circleAverage q : ℂ))

def outerCandidate (q : ℝ → ℝ) (a : ℕ) (z : ℂ) : ℂ := Complex.exp (outerExponent q a z)

theorem outerExponent_zero (q : ℝ → ℝ) (a : ℕ) :
    outerExponent q a 0 = (((a : ℝ) * circleAverage q : ℝ) : ℂ) := by
  unfold outerExponent
  rw [positiveDiscProjection_zero, circleFourier_ofReal_zero]
  push_cast
  ring

theorem outerCandidate_zero (q : ℝ → ℝ) (a : ℕ) :
    outerCandidate q a 0 = (Real.exp ((a : ℝ) * circleAverage q) : ℂ) := by
  unfold outerCandidate
  rw [outerExponent_zero]
  simp only [Complex.ofReal_exp]

theorem outerCandidate_center_phase (q : ℝ → ℝ) (a : ℕ) :
    (outerCandidate q a 0).im = 0 ∧ 0 < (outerCandidate q a 0).re := by
  rw [outerCandidate_zero]
  exact ⟨Complex.ofReal_im _, Real.exp_pos _⟩

theorem outerCandidate_ne_zero (q : ℝ → ℝ) (a : ℕ) (z : ℂ) : outerCandidate q a z ≠ 0 :=
  Complex.exp_ne_zero _

theorem outerExponent_contDiffOn {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) :
    ContDiffOn ℂ ∞ (outerExponent q a) (Metric.closedBall 0 1) := by
  have hu : ContDiff ℝ ∞ (fun θ => (q θ : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hup : Function.Periodic (fun θ => (q θ : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg Complex.ofReal (hp θ)
  exact contDiffOn_const.mul
    ((contDiffOn_const.mul (positiveDiscProjection_contDiffOn hu hup)).sub contDiffOn_const)

theorem outerCandidate_contDiffOn {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℕ) :
    ContDiffOn ℂ ∞ (outerCandidate q a) (Metric.closedBall 0 1) := by
  have he : ContDiff ℂ ∞ Complex.exp := Complex.contDiff_exp
  exact he.comp_contDiffOn (outerExponent_contDiffOn hq hp a)

theorem outerCandidate_logTrace_zero {n r : ℕ} {X : KahlerManifold n}
    (d : VariationData X r) (j a : ℕ) (F : VariationDisc X) :
    outerCandidate (logTrace d j F.f) a 0 = (outerCenter d j a F : ℂ) := by
  rw [outerCandidate_zero, outerCenter_eq_exp_logTrace]

end Yau.Blueprint.V03Proof
