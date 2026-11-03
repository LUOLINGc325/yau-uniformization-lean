import Yau.LeafProofs.L16TraceHeatPrimitive

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem normalGaussianKernel_joint_measurable :
    Measurable (fun p : ℝ × ℝ => normalGaussianKernel p.1 p.2) := by
  dsimp only [normalGaussianKernel]
  fun_prop

/-- Global measurability of the actual profile, obtained from its finite
    Gaussian integral, without assigning an artificial value at age zero. -/
theorem normalHeatProfile_time_stronglyMeasurable {a : ℝ} (ha : 0 ≤ a) :
    StronglyMeasurable (fun r : ℝ => normalHeatProfile r a) := by
  have hI := normalGaussianKernel_joint_measurable.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) a))
  have hFun : (fun r => normalHeatProfile r a) =
      fun r => 2*(∫ s in Ioc (0 : ℝ) a, normalGaussianKernel r s) := by
    funext r
    rw [normalHeatProfile,intervalIntegral.integral_of_le ha]
  rw [hFun]
  exact stronglyMeasurable_const.mul hI

theorem sourceHeatAverage_joint_stronglyMeasurable {n : ℕ} {B : Point n → ℝ}
    (hB : Continuous B) (ξ : Space n) :
    StronglyMeasurable (fun p : ℝ × ℝ => heatAverage (p.1-p.2) (fun y => B (y,p.2)) ξ) := by
  have hGm : Measurable (fun q : (ℝ × ℝ) × Space n => gaussianKernel (q.1.1-q.1.2) q.2) :=
    gaussianKernel_joint_measurable.comp
      (show Measurable (fun q : (ℝ × ℝ) × Space n => (q.1.1-q.1.2,q.2)) from by fun_prop)
  have hBm : Measurable (fun q : (ℝ × ℝ) × Space n => B (ξ-q.2,q.1.2)) :=
    hB.measurable.comp (by fun_prop)
  simpa only [heatAverage_def,Function.uncurry_apply_pair,Pi.mul_apply] using
    (hGm.mul hBm).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Space n)))

/-- The actual causal derivative kernel, indexed by absolute observation and
    source time. This is the integrand used in the triangle Fubini argument. -/
def traceTimeKernel {n : ℕ} (B : Point n → ℝ) (a : ℝ) (ξ : Space n) (p : ℝ × ℝ) : ℝ :=
  if p.2 < p.1 then
    -normalPoissonKernel a (p.1-p.2)*heatAverage (p.1-p.2) (fun y => B (y,p.2)) ξ+
    normalHeatProfile (p.1-p.2) a*heatLaplacian (heatAverage (p.1-p.2) (fun y => B (y,p.2))) ξ
  else 0

/-- Measurability of the genuine causal layer kernel follows from the actual
    Gaussian formulas, with no joint measurability assertion about derivatives
    or representatives inserted as a premise. -/
theorem traceTimeKernel_stronglyMeasurable {n : ℕ} {F a : ℝ} (ha : 0 ≤ a)
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ξ : Space n) :
    StronglyMeasurable (traceTimeKernel B a ξ) := by
  let A : (ℝ × ℝ) × Space n → ℝ := fun q =>
    (gaussianKernel (q.1.1-q.1.2) (ξ-q.2)*
      (‖ξ-q.2‖^2/(4*(q.1.1-q.1.2)^2)-(n:ℝ)/(q.1.1-q.1.2)))*B (q.2,q.1.2)
  have hGm : Measurable (fun q : (ℝ × ℝ) × Space n => gaussianKernel (q.1.1-q.1.2) (ξ-q.2)) :=
    gaussianKernel_joint_measurable.comp
      (show Measurable (fun q : (ℝ × ℝ) × Space n => (q.1.1-q.1.2,ξ-q.2)) from by fun_prop)
  have hAm : Measurable A :=
    (hGm.mul (show Measurable (fun q : (ℝ × ℝ) × Space n =>
      ‖ξ-q.2‖^2/(4*(q.1.1-q.1.2)^2)-(n:ℝ)/(q.1.1-q.1.2)) from by fun_prop)).mul
      (hB.measurable.comp (by fun_prop))
  let I : ℝ × ℝ → ℝ := fun p => ∫ y : Space n, A (p,y)
  have hIm : StronglyMeasurable I := hAm.stronglyMeasurable.integral_prod_right'
  have hKI : StronglyMeasurable (fun p : ℝ × ℝ =>
      -normalPoissonKernel a (p.1-p.2)*heatAverage (p.1-p.2) (fun y => B (y,p.2)) ξ+
        normalHeatProfile (p.1-p.2) a*I p) :=
    (((normalPoissonKernel_measurable a).comp (by fun_prop)).stronglyMeasurable.neg.mul
      (sourceHeatAverage_joint_stronglyMeasurable hB ξ)).add
      (((normalHeatProfile_time_stronglyMeasurable ha).comp_measurable (by fun_prop)).mul hIm)
  have hFun : traceTimeKernel B a ξ = ({p : ℝ × ℝ | p.2 < p.1}).indicator
      (fun p => -normalPoissonKernel a (p.1-p.2)*heatAverage (p.1-p.2) (fun y => B (y,p.2)) ξ+
        normalHeatProfile (p.1-p.2) a*I p) := by
    funext p
    by_cases hp : p.2 < p.1
    · simp only [traceTimeKernel,if_pos hp,indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.2 < q.1} from hp)]
      have hEq := ((heatAverage_hasDerivAt_of_bounded (sub_pos.mpr hp)
        (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,p.2)) ξ).unique
        (heatAverage_hasDerivAt_laplacian_of_bounded (sub_pos.mpr hp)
          (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,p.2)) ξ))
      change I p = heatLaplacian (heatAverage (p.1-p.2) (fun y => B (y,p.2))) ξ at hEq
      rw [hEq]
    · simp only [traceTimeKernel,if_neg hp,
        indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.2 < q.1} from hp)]
  rw [hFun]
  exact hKI.indicator (measurableSet_lt measurable_snd measurable_fst)

end Yau.LeafProofs.L16Aux
