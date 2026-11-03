import Yau.Proofs.V02FlowPicardOperator
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The radial integral is an actual complex primitive. -/

open scoped Topology ContDiff
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem HasDerivAt.radial_real {f : ℂ → V} {f' : V} {s : ℝ} {t : ℂ}
    (hf : HasDerivAt f f' ((s : ℂ) * t)) :
    HasDerivAt (fun r : ℝ => f ((r : ℂ) * t)) (t • f') s := by
  have hlin : HasDerivAt (fun r : ℝ => (r : ℂ) * t) t s := by
    simpa using Complex.ofRealCLM.hasDerivAt.mul_const t
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply] using
    (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hlin

theorem radialIntegral_hasDerivAt {g : ℂ → V} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) {t : ℂ} (ht : t ∈ ball 0 R) :
    HasDerivAt (fun z : ℂ => z • ∫ s in (0 : ℝ)..1, g ((s : ℂ) * z)) (g t) t := by
  obtain ⟨H, hH0, hH⟩ := hg.isExactOn_ball.with_val_at 0 (0 : V)
  have heq : ∀ z ∈ ball (0 : ℂ) R,
      z • (∫ s in (0 : ℝ)..1, g ((s : ℂ) * z)) = H z := by
    intro z hz
    have hr : ∀ s ∈ Set.uIcc (0 : ℝ) 1, (s : ℂ) * z ∈ ball 0 R := by
      intro s hs
      rw [mem_ball, dist_zero_right]
      exact (norm_radial_time_le (by simpa using hs) z).trans_lt (by simpa using hz)
    have hc : ContinuousOn (fun s : ℝ => g ((s : ℂ) * z)) (Set.uIcc 0 1) :=
      hg.continuousOn.comp (Complex.continuous_ofReal.mul_const z).continuousOn hr
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => HasDerivAt.radial_real (hH _ (hr s hs)))
      (hc.const_smul z).intervalIntegrable
    simpa only [intervalIntegral.integral_smul, Complex.ofReal_one, one_mul,
      Complex.ofReal_zero, zero_mul, hH0, sub_zero] using hFTC
  apply (hH t ht).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ht] with z hz
  exact heq z hz

end Yau.Blueprint.V02FlowProof
