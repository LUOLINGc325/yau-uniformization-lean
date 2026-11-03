import Yau.Proofs.V03OuterBoundary
import Yau.Proofs.V04AverageSquares
import Yau.Proofs.V04FejerColumnBounds

/-! The clock lift is the actual positive Fourier extension of the
normalized weight minus one. Its real part obeys the closed-disc lower
bound needed by the backward clock. -/

open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

def clockLiftCandidate (γ : ℝ → ℝ) (z : ℂ) : ℂ :=
  2 * positiveDiscProjection (fun θ => ((γ θ - 1 : ℝ) : ℂ)) z

theorem clockLiftCandidate_smooth {γ : ℝ → ℝ} (hγ : ContDiff ℝ ∞ γ)
    (hp : Function.Periodic γ (2 * Real.pi)) :
    ContDiffOn ℂ ∞ (clockLiftCandidate γ) (Metric.closedBall (0 : ℂ) 1) := by
  have hq : ContDiff ℝ ∞ (fun θ => ((γ θ - 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hγ.sub contDiff_const)
  have hqp : Function.Periodic (fun θ => ((γ θ - 1 : ℝ) : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg (fun t : ℝ => ((t - 1 : ℝ) : ℂ)) (hp θ)
  exact contDiffOn_const.mul (positiveDiscProjection_contDiffOn hq hqp)

theorem clockLiftCandidate_zero_real_boundary {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ (2 * Real.pi))
    (hm : circleAverage γ = 1) :
    clockLiftCandidate γ 0 = 0 ∧ ∀ θ, (clockLiftCandidate γ (circlePoint θ)).re = γ θ - 1 := by
  let q := fun θ => γ θ - 1
  have hq : ContDiff ℝ ∞ q := hγ.sub contDiff_const
  have hqp : Function.Periodic q (2 * Real.pi) := fun θ => congrArg (fun t : ℝ => t - 1) (hp θ)
  have hqm : circleAverage q = 0 := by
    have heq : q = fun θ => γ θ + (-1 : ℝ) := by funext θ; ring
    rw [heq, circleAverage_add_of_continuous hγ.continuous continuous_const,
      hm, circleAverage_const_value]
    norm_num
  constructor
  · unfold clockLiftCandidate
    rw [positiveDiscProjection_zero, circleFourier_ofReal_zero, hqm]
    simp
  · intro θ
    have hh := positiveDisc_real_boundary hq hqp θ
    rw [hqm] at hh
    simpa [clockLiftCandidate, q, Complex.mul_re] using hh

theorem closedDisc_real_part_lower {Γ : ℂ → ℂ}
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1))
    (hboundary : ∀ θ, -1 ≤ (Γ (circlePoint θ)).re) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re := by
  have he : ContDiffOn ℂ ∞ (fun z => Complex.exp (-Γ z)) (Metric.closedBall (0 : ℂ) 1) := by
    fun_prop
  have hnorm : ∀ θ, ‖Complex.exp (-Γ (circlePoint θ))‖ ≤ Real.exp 1 := by
    intro θ
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith only [hboundary θ])
  intro z hz
  have hh := closedDisc_holomorphic_norm_le he hnorm hz
  rw [Complex.norm_exp, Complex.neg_re] at hh
  have hle := Real.exp_le_exp.mp hh
  linarith only [hle]

end Yau.Blueprint.V04Proof
