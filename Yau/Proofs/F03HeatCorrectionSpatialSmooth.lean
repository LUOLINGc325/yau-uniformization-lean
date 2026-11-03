import Yau.Proofs.F03InitialSpatialIntegral
import Yau.Proofs.F03HodgeHeatCorrection

/-! The actual correction has smooth spatial slices from the proved scalar initial jets alone. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem boundedScalarHeat_timeIntegral_smooth
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u) {R : ℝ} (hR : 0 ≤ R) :
    SmoothFn (fun x => ∫ b in (0:ℝ)..R,u b x) := by
  intro a
  exact initial_spatial_integral_contDiffOn
    (fun p : ComplexVector n × ℝ => u p.2 (chartInv a p.1)) (inChart a f)
    (isOpen_extChartAt_target (I := ComplexModel n) a) (hu.1 a) (hf a)
    (fun z => congrFun hu.2.1.1 (chartInv a z))
    (fun K hK hKt m ε hε => hu.2.1.2 a K hK hKt m ε hε) hR

theorem metricDefectHeatCorrection_smooth
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (L : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    SmoothFn (fun x => metricDefectHeatCorrection X h μ hμ O hO L x s) := by
  have hClass := dirichletMinimalBoundedHeat_class X.metric X.kahler_metric μ hμ O hO
    (flowMetricDefect X h s) (flowMetricDefect_smooth X o h U P ρ hf hs)
    ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hs⟩
  have hSmooth := boundedScalarHeat_timeIntegral_smooth X.metric.form (flowMetricDefect X h s)
    _ (flowMetricDefect_smooth X o h U P ρ hf hs) hClass (sq_nonneg L)
  intro a
  exact (hSmooth a).neg

end Yau.Proofs.F03Aux
