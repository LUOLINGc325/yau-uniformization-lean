import Yau.Proofs.F03CenteredKernelPoisson
import Yau.Proofs.F03BoundedHeatTimeIntegrable
import Yau.Proofs.F03HodgeHeatCorrection

/-! The same actual correction is an affine terminal correction plus the actual centered-potential heat. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_centered_identity
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc 0 T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L) (x : Pt X) :
    metricDefectHeatCorrection X h μ hμ O hO L x s=
      (s/T)*metricDefectHeatCorrection X h μ hμ O hO L x T+
        (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*
          centeredFlowPotential X U T y s ∂μ)-centeredFlowPotential X U T x s := by
  let H := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO
  let w : ℝ → ℝ → Pt X → ℝ := fun r => boundedKernelEvolution μ H (flowMetricDefect X h r)
  have hClass (r : ℝ) (hr : 0 ≤ r) : IsBoundedScalarHeat X.metric.form (flowMetricDefect X h r) (w r) :=
    dirichletMinimalBoundedHeat_class X.metric X.kahler_metric μ hμ O hO (flowMetricDefect X h r)
      (flowMetricDefect_smooth X o h U P ρ hf hr) ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hr⟩
  have hIntS := boundedScalarHeat_time_intervalIntegrable X.metric.form _ _ (hClass s hs.1) (sq_nonneg L) x
  have hIntT := boundedScalarHeat_time_intervalIntegrable X.metric.form _ _ (hClass T hT.le) (sq_nonneg L) x
  have hHeatLap (b : ℝ) (hb : 0 < b) :
      (∫ y,H b x y*laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y ∂μ)=
        (s/T)*w T b x-w s b x := by
    have hiS := dirichletMinimalKernelCandidate_bounded_source_integrable X.metric X.kahler_metric μ hμ O hO
      (flowMetricDefect X h s) (continuous_of_smoothFn (flowMetricDefect_smooth X o h U P ρ hf hs.1)).aestronglyMeasurable
      ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hs.1⟩ hb x
    have hiT := dirichletMinimalKernelCandidate_bounded_source_integrable X.metric X.kahler_metric μ hμ O hO
      (flowMetricDefect X h T) (continuous_of_smoothFn (flowMetricDefect_smooth X o h U P ρ hf hT.le)).aestronglyMeasurable
      ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hT.le⟩ hb x
    calc
      _ = ∫ y,(s/T)*(H b x y*flowMetricDefect X h T y)-H b x y*flowMetricDefect X h s y ∂μ := by
        apply integral_congr_ae
        apply ae_of_all μ
        intro y
        change H b x y*laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y=_
        rw [centeredFlowPotential_laplacian X o h U P ρ hf hT hs.1 y]
        ring
      _ = _ := by
        rw [integral_sub (hiT.const_mul (s/T)) hiS,integral_const_mul]
        simp only [w,boundedKernelEvolution,if_neg hb.ne']
        rfl
  have hIntegral : (∫ b in (0:ℝ)..L^2,∫ y,H b x y*
      laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y ∂μ)=
      (s/T)*(∫ b in (0:ℝ)..L^2,w T b x)-(∫ b in (0:ℝ)..L^2,w s b x) := by
    calc
      _ = ∫ b in (0:ℝ)..L^2,(s/T)*w T b x-w s b x := by
        apply intervalIntegral.integral_congr_ae
        apply ae_of_all volume
        intro b hb
        rw [uIoc_of_le (sq_nonneg L)] at hb
        exact hHeatLap b hb.1
      _ = _ := by rw [intervalIntegral.integral_sub (hIntT.const_mul (s/T)) hIntS,
        intervalIntegral.integral_const_mul]
  have hPoisson := dirichletMinimalKernel_centered_poisson X o h U P ρ hf u hu hT hs μ hμ O hO
    (sq_pos_of_pos hL) x
  change (∫ y,H (L^2) x y*centeredFlowPotential X U T y s ∂μ)-centeredFlowPotential X U T x s=_ at hPoisson
  rw [hIntegral] at hPoisson
  change -(∫ b in (0:ℝ)..L^2,w s b x)=(s/T)*(-(∫ b in (0:ℝ)..L^2,w T b x))+
    (∫ y,H (L^2) x y*centeredFlowPotential X U T y s ∂μ)-centeredFlowPotential X U T x s
  linarith

end Yau.Proofs.F03Aux
