import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03FourierEnergy
import Yau.Proofs.V03Energy

/-! The original logarithmic wall trace is a smooth periodic function,
and its exact Fourier half-derivative seminorm is finite. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circlePoint_contDiff : ContDiff ℝ ∞ circlePoint := by
  unfold circlePoint
  have heC : ContDiff ℂ ∞ Complex.exp := Complex.contDiff_exp
  have he : ContDiff ℝ ∞ Complex.exp := heC.restrict_scalars ℝ
  exact he.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem circlePoint_zero : circlePoint 0 = 1 := by simp [circlePoint]

theorem circlePoint_two_pi : circlePoint (2 * Real.pi) = 1 := by
  simpa only [circlePoint, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_two_pi_mul_I

variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_logTrace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (logTrace d j F.f) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hc := (admissible_logWall_contDiffWithinAt hd hF θ).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun η (_ : η ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall η)
  exact contDiffWithinAt_univ.mp hc

theorem admissible_logTrace_period {d : VariationData X q} (j : ℕ) (F : VariationDisc X) :
    logTrace d j F.f (2 * Real.pi) = logTrace d j F.f 0 := by
  simp only [logTrace, circlePoint_two_pi, circlePoint_zero]

theorem admissible_logSeminorm_ne_top {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    scalarDSq (logTrace d j F.f) ≠ ⊤ := by
  have hq := admissible_logTrace_contDiff hd hF
  have hU : ContDiff ℝ ∞ (fun θ => (logTrace d j F.f θ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  apply boundaryDSq_ne_top_of_periodic_C1
    (u' := deriv (fun θ => (logTrace d j F.f θ : ℂ)))
  · intro θ
    exact (hU.differentiable (by simp) θ).hasDerivAt
  · exact hU.continuous_deriv (by simp)
  · exact congrArg Complex.ofReal (admissible_logTrace_period j F)

end Yau.Blueprint.V03Proof
