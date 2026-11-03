import Yau.Proofs.V03ComplexBoundaryDerivative
import Yau.Proofs.V03EuclideanRadial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Continuous derivative towers on the closed disc, holomorphic in its
interior, give the original complex C∞ regularity up to the circle. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

 theorem contDiffOn_closedDisc_of_derivative_tower (f : ℕ → ℂ → ℂ)
    (hc : ∀ k, ContinuousOn (f k) (Metric.closedBall 0 1))
    (hd : ∀ k z, z ∈ Metric.ball (0 : ℂ) 1 → HasDerivAt (f k) (f (k + 1) z) z) :
    ContDiffOn ℂ ∞ (f 0) (Metric.closedBall 0 1) := by
  have hwithin (k : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
      HasDerivWithinAt (f k) (f (k + 1) z) (Metric.closedBall 0 1) z := by
    let A : ℂ → ℂ →L[ℂ] ℂ := fun w => (1 : ℂ →L[ℂ] ℂ).smulRight (f (k + 1) w)
    have hA : ContinuousOn A (Metric.closedBall 0 1) :=
      ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ) 1).continuous.comp_continuousOn (hc (k + 1))
    have hf : DifferentiableOn ℂ (f k) (Metric.ball 0 1) :=
      fun w hw => (hd k w hw).differentiableAt.differentiableWithinAt
    exact hasFDerivWithinAt_complex_closedBall (by norm_num : (0 : ℝ) < 1) hf (hc k) hA
      (fun w hw => (hd k w hw).hasFDerivAt.fderiv) hz
  have hit : ∀ k, Set.EqOn (iteratedDerivWithin k (f 0) (Metric.closedBall 0 1)) (f k)
      (Metric.closedBall 0 1) := by
    intro k
    induction k with
    | zero => intro z hz; simp
    | succ k ih =>
        intro z hz
        rw [iteratedDerivWithin_succ]
        exact (derivWithin_congr ih (ih hz)).trans
          ((hwithin k z hz).derivWithin (uniqueDiffOn_complex_closedDisc z hz))
  apply (contDiffOn_iff_continuousOn_differentiableOn_deriv uniqueDiffOn_complex_closedDisc).mpr
  constructor
  · intro k hk
    exact (hc k).congr (hit k)
  · intro k hk
    exact (show DifferentiableOn ℂ (f k) (Metric.closedBall 0 1) from
      fun z hz => (hwithin k z hz).differentiableWithinAt).congr (hit k)

end Yau.Blueprint.V03Proof
