import Yau.Proofs.C03PoleJetsLocal

/-! The original n+1 critical pole annihilates the value and the actual
complex first derivative of the same local holomorphic function. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Yau.Proofs.C03Aux.PoleJets

open Yau
variable {n : ℕ}

theorem value_and_derivatives_zero_of_real_jets
    (f : ComplexVector n → ℂ) (hf : DifferentiableAt ℂ f 0)
    (hj : ∀ j ≤ 1, iteratedFDeriv ℝ j f 0 = 0) :
    f 0 = 0 ∧ fderiv ℂ f 0 = 0 ∧ fderiv ℝ f 0 = 0 := by
  have hval : f 0 = 0 := by
    have H := congrArg (fun T : ComplexVector n [×0]→L[ℝ] ℂ => T (fun i => Fin.elim0 i))
      (hj 0 (by norm_num))
    simpa only [iteratedFDeriv_zero_apply, zero_apply] using H
  have hr : fderiv ℝ f 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have H := congrArg (fun T : ComplexVector n [×1]→L[ℝ] ℂ => T (fun _ => v))
      (hj 1 le_rfl)
    simpa only [iteratedFDeriv_one_apply, zero_apply, zero_apply] using H
  have hc : fderiv ℂ f 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have H := congrArg (fun T : ComplexVector n →L[ℝ] ℂ => T v) (hf.fderiv_restrictScalars ℝ)
    change fderiv ℝ f 0 v = fderiv ℂ f 0 v at H
    simpa only [hr, zero_apply] using H.symm
  exact ⟨hval, hc, hr⟩

theorem critical_pole_jets_zero
    (hn : 1 ≤ n) (f : ComplexVector n → ℂ) (R : ℝ) (hR : 0 < R)
    (hH : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hfinite : (∫⁻ z in Metric.ball (0 : ComplexVector n) R,
      ENNReal.ofReal (‖f z‖ ^ 2 * ‖z‖ ^ (-2 * ((n : ℝ) + 1)))) < ∞) :
    f 0 = 0 ∧ fderiv ℂ f 0 = 0 ∧ fderiv ℝ f 0 = 0 := by
  have hdensity : (∫⁻ z in Metric.ball (0 : ComplexVector n) R,
      ENNReal.ofReal (weightedDensity (2 * (n + 1)) f z)) < ∞ := by
    simpa only [critical_density_rpow] using hfinite
  apply value_and_derivatives_zero_of_real_jets f
    ((hH 0 (Metric.mem_ball_self hR)).differentiableAt (Metric.ball_mem_nhds 0 hR))
  exact real_jets_zero_of_critical_lintegral hn f R hR hH hdensity

end Yau.Proofs.C03Aux.PoleJets
