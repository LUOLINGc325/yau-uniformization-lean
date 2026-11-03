import Yau.Proofs.F03ScalarHeatGradientIntegral
import Yau.Proofs.F03HeatCorrectionSize

/-! The actual correction inherits the fractional physical gradient bound by genuine differentiation and integration. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_gradient_bound (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      Real.sqrt (gradNormSq X.metric.form
        (fun y => metricDefectHeatCorrection X h μ hμ O hO L y s) x) ≤
        C*s^(heatDecayExponent n)*L^(1-heatDecayExponent n) := by
  obtain ⟨K,hK,hEstimate⟩ := flowMetricDefect_heat_quarter_majorants hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  refine ⟨K*4,by positivity,fun μ hμ O hO s hs L hL x hx => ?_⟩
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rcases eq_or_lt_of_le hs.1 with hs0|hs0
  · subst s
    have hZero : (fun y => metricDefectHeatCorrection X h μ hμ O hO L y 0)=(fun _ => 0) :=
      funext (metricDefectHeatCorrection_zero X o h U P ρ hf μ hμ O hO L)
    rw [hZero]
    have hg0 : gradNormSq X.metric.form (fun _ => 0) x=0 := by
      simp [gradNormSq,dualNormMat,wirt,inChart,Matrix.mulVec,dotProduct]
    rw [hg0,Real.sqrt_zero]
    positivity
  have hSmooth := flowMetricDefect_smooth X o h U P ρ hf hs.1
  let v := boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
    (flowMetricDefect X h s)
  have hClass : IsBoundedScalarHeat X.metric.form (flowMetricDefect X h s) v :=
    dirichletMinimalBoundedHeat_class X.metric X.kahler_metric μ hμ O hO _ hSmooth
      ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hs.1⟩
  have hTriangle := boundedScalarHeat_gradient_timeIntegral_le X.metric.form _ v hSmooth hClass x (sq_nonneg L)
  have hIntegralSmooth := boundedScalarHeat_timeIntegral_smooth X.metric.form _ v hSmooth hClass (sq_nonneg L)
  change Real.sqrt (gradNormSq X.metric.form (fun y => -(∫ b in (0:ℝ)..L^2,v b y)) x) ≤ _
  rw [sqrt_gradNormSq_negative X.metric.form _ hIntegralSmooth x]
  have hMajorInt : IntervalIntegrable
      (fun b : ℝ => K*(s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(3:ℝ)/4)))
      volume 0 (L^2) := ((quarter_heat_majorant_integrable (L^2)).2.const_mul _).const_mul K
  calc
    _ ≤ ∫ b in (0:ℝ)..L^2,Real.sqrt (gradNormSq X.metric.form (v b) x) := hTriangle.2
    _ ≤ ∫ b in (0:ℝ)..L^2,K*(s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(3:ℝ)/4)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (sq_nonneg L) hTriangle.1 hMajorInt
      intro b hb
      convert (hEstimate μ hμ O hO s ⟨hs0,hs.2⟩ L hL b hb.1 hb.2.le x hx).2 using 1 <;> ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,heat_three_quarter_majorant_scale_integral hL0]
      ring

end Yau.Proofs.F03Aux
