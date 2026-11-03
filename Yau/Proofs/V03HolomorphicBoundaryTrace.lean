import Yau.Proofs.V03EuclideanRadial
import Yau.Proofs.V03BoundaryDerivative
import Yau.Proofs.V03CirclePeriod
import Yau.Proofs.V03HolomorphicFourier

/-! The actual boundary derivative of a holomorphic closed disc is its
native within derivative times the circle tangent, including at the circle. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def holomorphicAngularTrace (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (circlePoint θ * Complex.I) * closedDiscDerivative f (circlePoint θ)

theorem hasDerivAt_holomorphic_boundary {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    HasDerivAt (fun t => f (circlePoint t)) (holomorphicAngularTrace f θ) θ := by
  have hd := ((((hf.differentiableOn (by simp)) _
    (circlePoint_mem_closedBall θ)).hasFDerivWithinAt).restrictScalars ℝ).comp_hasDerivAt θ
      (hasDerivAt_circlePoint θ)
      (Eventually.of_forall circlePoint_mem_closedBall)
  have he : fderivWithin ℂ f (Metric.closedBall 0 1) (circlePoint θ) (circlePoint θ * Complex.I) =
      holomorphicAngularTrace f θ := by
    simpa only [holomorphicAngularTrace, closedDiscDerivative, smul_eq_mul, mul_one] using
      (fderivWithin ℂ f (Metric.closedBall 0 1) (circlePoint θ)).map_smul
        (circlePoint θ * Complex.I) (1 : ℂ)
  change HasDerivAt (fun t => f (circlePoint t))
    (fderivWithin ℂ f (Metric.closedBall 0 1) (circlePoint θ) (circlePoint θ * Complex.I)) θ at hd
  rwa [he] at hd

theorem holomorphicAngularTrace_continuous {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    Continuous (holomorphicAngularTrace f) :=
  (circlePoint_contDiff.continuous.mul continuous_const).mul
    ((continuousOn_closedDiscDerivative hf).comp_continuous
      circlePoint_contDiff.continuous circlePoint_mem_closedBall)

theorem holomorphicAngularTrace_periodic (f : ℂ → ℂ) :
    Function.Periodic (holomorphicAngularTrace f) (2 * Real.pi) :=
  circleTrace_periodic (fun ζ => (ζ * Complex.I) * closedDiscDerivative f ζ)

theorem holomorphic_boundary_fourier_negative {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ∀ k : ℤ, k < 0 → circleFourier (fun θ => f (circlePoint θ)) k = 0 := by
  intro k hk
  cases k with
  | ofNat m => exact False.elim ((not_lt_of_ge (Int.natCast_nonneg m)) hk)
  | negSucc m =>
      simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using
        holomorphic_boundary_fourier_negSucc hf m

end Yau.Blueprint.V03Proof
