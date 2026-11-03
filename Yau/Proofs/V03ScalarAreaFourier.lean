import Yau.Proofs.V03NormAreaBoundary
import Yau.Proofs.V03HolomorphicBoundaryTrace
import Yau.Proofs.V03PositiveDirichletCurrent

/-! Exact area/Fourier normalization for an actual holomorphic scalar
closed disc. Its derivative and negative modes are derived natively. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem normDiscArea_scalar_eq_boundaryDSq {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    normDiscArea f = ENNReal.ofReal (2 * Real.pi) *
      boundaryDSq (fun θ (_ : Unit) => f (circlePoint θ)) := by
  have hc : Continuous (fun θ => f (circlePoint θ)) :=
    hf.continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hDSq := boundaryDSq_eq_positive_current hc (holomorphicAngularTrace_continuous hf)
    (circleTrace_periodic f) (holomorphicAngularTrace_periodic f)
    (hasDerivAt_holomorphic_boundary hf) (holomorphic_boundary_fourier_negative hf)
  have hcurrent : (fun θ => (star (f (circlePoint θ)) *
      (-Complex.I * holomorphicAngularTrace f θ)).re) = normBoundaryCurrent f := by
    funext θ
    have he : -Complex.I * ((circlePoint θ * Complex.I) * closedDiscDerivative f (circlePoint θ)) =
        circlePoint θ * closedDiscDerivative f (circlePoint θ) := by
      calc
        _ = -(Complex.I * Complex.I) * (circlePoint θ * closedDiscDerivative f (circlePoint θ)) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    simp only [holomorphicAngularTrace, normBoundaryCurrent, he, smul_eq_mul,
      RCLike.inner_apply, Complex.star_def]
    congr 1
    ring
  rw [hcurrent] at hDSq
  have harea := normDiscArea_eq_boundary_current hf
  have hp : Function.Periodic (normBoundaryCurrent f) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => (inner ℂ (f ζ) (ζ • closedDiscDerivative f ζ)).re)
  have hshift := hp.intervalIntegral_add_eq (-Real.pi) 0
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [he, zero_add] at hshift
  rw [hshift] at harea
  rw [harea, hDSq, circleAverage, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  congr 1
  have hne : 2 * Real.pi ≠ 0 := by positivity
  field_simp

theorem boundaryDSq_scalar_eq_inverse_area {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    boundaryDSq (fun θ (_ : Unit) => f (circlePoint θ)) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * normDiscArea f := by
  rw [normDiscArea_scalar_eq_boundaryDSq hf, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹),
    inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), ENNReal.ofReal_one, one_mul]

end Yau.Blueprint.V03Proof
