import Yau.Proofs.V02DampingTrace
import Yau.Proofs.V02CircleQuadratic
import Yau.Proofs.V03OuterPhase
import Yau.Proofs.V03OuterUniqueness

/-! The actual outer damping constructed from a finite vector trace:
positive real center, exact reciprocal boundary modulus, loss and seminorm. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem parameterAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ θ, f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  unfold circleAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on (by positivity)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => h θ)

variable {ι : Type*} [Fintype ι]

def outerDamping (P : ℝ) (u : ℝ → ι → ℂ) : ℂ → ℂ :=
  V03Proof.outerCandidate (dampingLogTrace P u) 1

theorem outerDamping_contDiffOn {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    ContDiffOn ℂ ∞ (outerDamping P u) (Metric.closedBall (0 : ℂ) 1) :=
  V03Proof.outerCandidate_contDiffOn (dampingLogTrace_contDiff hP hu)
    (dampingLogTrace_periodic P hp) 1

theorem outerDamping_center_phase (P : ℝ) (u : ℝ → ι → ℂ) :
    (outerDamping P u 0).im = 0 ∧ 0 < (outerDamping P u 0).re :=
  V03Proof.outerCandidate_center_phase _ _

theorem outerDamping_norm_boundary {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (θ : ℝ) :
    ‖outerDamping P u (circlePoint θ)‖ = reciprocalDamping P (∑ i, ‖u θ i‖ ^ 2) := by
  rw [outerDamping, V03Proof.outerCandidate_norm_boundary
    (dampingLogTrace_contDiff hP hu) (dampingLogTrace_periodic P hp)]
  simp only [Nat.cast_one, one_mul, dampingLogTrace, reciprocalDamping, Real.exp_neg]
  rw [Real.exp_log (by
    have hs : 0 ≤ ∑ i, ‖u θ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity)]

theorem outerDamping_norm_le_one {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖outerDamping P u z‖ ≤ 1 := by
  apply V03Proof.norm_le_of_circle_bound (outerDamping_contDiffOn hP hu hp)
  intro θ
  rw [outerDamping_norm_boundary hP hu hp]
  exact reciprocalDamping_le_one hP (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem outerDamping_center_loss {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i)) :
    -Real.log (outerDamping P u 0).re ≤ circleAverage (fun θ => ∑ i, ‖u θ i‖ ^ 2) / P := by
  have hs : Continuous (fun θ => ∑ i, ‖u θ i‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => (hu i).continuous.norm.pow 2)
  have hq := dampingLogTrace_contDiff hP hu
  have he : -Real.log (outerDamping P u 0).re =
      circleAverage (fun θ => Real.log (1 + (∑ i, ‖u θ i‖ ^ 2) / P)) := by
    rw [outerDamping, V03Proof.outerCandidate_zero]
    simp only [Nat.cast_one, one_mul, Complex.ofReal_re, Real.log_exp,
      dampingLogTrace, circleAverage, intervalIntegral.integral_neg]
    ring
  rw [he]
  have hlog : Continuous (fun θ => Real.log (1 + (∑ i, ‖u θ i‖ ^ 2) / P)) := by
    simpa only [dampingLogTrace, neg_neg] using hq.neg.continuous
  have hm := parameterAverage_mono hlog (hs.div_const P)
    (fun θ => (dampingLog_bounds hP (Finset.sum_nonneg (fun i _ => sq_nonneg (‖u θ i‖)))).2)
  have he' : circleAverage (fun θ => (∑ i, ‖u θ i‖ ^ 2) / P) =
      circleAverage (fun θ => ∑ i, ‖u θ i‖ ^ 2) / P := by
    simp only [div_eq_mul_inv, circleAverage, intervalIntegral.integral_mul_const]
    ring
  exact hm.trans_eq he'

theorem outerDamping_boundary_loss {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    circleAverage (fun θ => 1 - ‖outerDamping P u (circlePoint θ)‖ ^ 2) ≤
      2 * circleAverage (fun θ => ∑ i, ‖u θ i‖ ^ 2) / P := by
  have hc := (outerDamping_contDiffOn hP hu hp).continuousOn.comp_continuous
    V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hs : Continuous (fun θ => ∑ i, ‖u θ i‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => (hu i).continuous.norm.pow 2)
  have hl : Continuous (fun θ => 1 - ‖outerDamping P u (circlePoint θ)‖ ^ 2) :=
    continuous_const.sub (hc.norm.pow 2)
  have hr : Continuous (fun θ => 2 * (∑ i, ‖u θ i‖ ^ 2) / P) :=
    (continuous_const.mul hs).div_const P
  have hm := parameterAverage_mono hl hr (fun θ => by
      rw [outerDamping_norm_boundary hP hu hp]
      exact (reciprocalDamping_loss hP (Finset.sum_nonneg (fun i _ => sq_nonneg _))).2)
  refine hm.trans_eq ?_
  simp only [circleAverage, div_eq_mul_inv, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  ring

theorem outerDamping_boundaryDSq_le {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    boundaryDSq (fun θ (_ : Unit) => outerDamping P u (circlePoint θ)) ≤
      ENNReal.ofReal (4 / P) * boundaryDSq u := by
  have hα := V03Proof.outerCandidate_boundaryDSq_le
    (dampingLogTrace_contDiff hP hu) (dampingLogTrace_periodic P hp)
    (dampingLogTrace_nonpos hP u) 1
  have hq := dampingLogTrace_boundaryDSq_le hP (fun i => (hu i).continuous) hp
  simp only [Nat.cast_one, one_pow, mul_one] at hα
  have hm := hα.trans (mul_le_mul_right hq (ENNReal.ofReal 4))
  simpa only [outerDamping, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← div_eq_mul_inv] using hm

end Yau.Blueprint.V02Proof
