import Yau.Proofs.V03OuterBoundary
import Yau.Proofs.V03FourierParsevalCircle
import Mathlib.Analysis.Complex.MeanValue

open scoped Topology ContDiff
open MeasureTheory Set AddCircle
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Mean value on the original closed disc; no extension beyond it is used. -/
theorem closedDisc_fourier_zero {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    circleFourier (fun θ ↦ f (circlePoint θ)) 0 = f 0 := by
  have hD : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    simp only [abs_one]
    refine ⟨(hf.differentiableOn (by simp)).mono Metric.ball_subset_closedBall, ?_⟩
    simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hf.continuousOn
  have hh := hD.circleAverage
  simpa only [circleFourier, Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul,
    Real.circleAverage_def, circleMap_zero, circlePoint, Complex.ofReal_one, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] using hh

/-- The real part has the same exact mean, for physical clock normalization. -/
theorem closedDisc_real_average {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    circleAverage (fun θ ↦ (f (circlePoint θ)).re) = (f 0).re := by
  have hD : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    simp only [abs_one]
    refine ⟨(hf.differentiableOn (by simp)).mono Metric.ball_subset_closedBall, ?_⟩
    simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hf.continuousOn
  have hcomm := Complex.reCLM.circleAverage_comp_comm
    ((hf.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable (by norm_num))
  rw [hD.circleAverage] at hcomm
  simpa only [circleAverage, Real.circleAverage_def, circleMap_zero, circlePoint, Complex.ofReal_one,
    one_mul, smul_eq_mul, Function.comp_apply, Complex.reCLM_apply] using hcomm

/-- The zero Fourier coefficient is bounded by the exact normalized L² sum.
This includes identically zero functions and zero center values. -/
theorem closedDisc_square_submean {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ‖f 0‖ ^ 2 ≤ circleAverage (fun θ ↦ ‖f (circlePoint θ)‖ ^ 2) := by
  let u := fun θ ↦ f (circlePoint θ)
  have hp : Function.Periodic u (2 * Real.pi) := fun θ ↦ congrArg f (circlePoint_periodic θ)
  have hc : Continuous u := hf.continuousOn.comp_continuous circlePoint_contDiff.continuous
    (fun θ ↦ circlePoint_mem_closedBall θ)
  have hs := circle_parseval_continuous (periodic_lift_continuous hp hc)
  have hle := hs.summable.sum_le_tsum ({0} : Finset ℤ) (fun k hk ↦ sq_nonneg ‖fourierCoeff hp.lift k‖)
  rw [Finset.sum_singleton, hs.tsum_eq, ← circleFourier_eq_periodic_lift hp 0,
    closedDisc_fourier_zero hf] at hle
  convert hle using 1
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp only [zero_add, Function.Periodic.lift_coe, smul_eq_mul]
  rfl

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
