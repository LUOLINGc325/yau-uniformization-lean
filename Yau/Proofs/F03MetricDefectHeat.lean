import Yau.Proofs.F03HeatMeanBudget
import Yau.Proofs.F03BoundedHeatGradient
import Yau.Proofs.F02
import Yau.Proofs.G04

/-! The original metric defect, evolved by the same actual minimal kernel, has the paper's two heat bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def flowMetricDefect (X : KahlerManifold n) (h : Flow X) (s : ℝ) : Pt X → ℝ :=
  fun y => traceWith (gMat X.metric.form y) (gMat X.metric.form y-gMat (h s) y)

theorem flowMetricDefect_smooth (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {s : ℝ} (hs : 0 ≤ s) : SmoothFn (flowMetricDefect X h s) :=
  F02Aux.metricDefect_smooth_of_G04 NodeProofs.G04_proved X o h U P ρ hf hs

theorem flowMetricDefect_bounds (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {s : ℝ} (hs : 0 ≤ s) (y : Pt X) :
    0 ≤ flowMetricDefect X h s y ∧ flowMetricDefect X h s y ≤ n :=
  F02Aux.metricDefect_trace_bounds X o h U P ρ hf hs y

theorem flowMetricDefect_abs_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {s : ℝ} (hs : 0 ≤ s) (y : Pt X) : |flowMetricDefect X h s y| ≤ n := by
  rw [abs_of_nonneg (flowMetricDefect_bounds X o h U P ρ hf hs y).1]
  exact (flowMetricDefect_bounds X o h U P ρ hf hs y).2

theorem flowMetricDefect_heat_mean_bound (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ b : ℝ,0 < b → b ≤ L^2 →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b x ≤
        min (n : ℝ) (C*s/L*(L/Real.sqrt b)^(2*n)) := by
  obtain ⟨A,hA,hAverage⟩ := (F02_of_P07_P08_G04 hP07 hP08 NodeProofs.G04_proved)
    n X o h U P ρ hf T hT
  obtain ⟨K,hK,hMean⟩ := dirichletMinimalBoundedHeat_ball_mean_bound X o h U P ρ hf C₀ hC₀
  refine ⟨K*A,mul_pos hK hA,fun μ hμ O hO s hs L hL b hb hbL x hx => ?_⟩
  have hMeas : Measurable (flowMetricDefect X h s) :=
    (LeafProofs.L18Aux.continuous_of_smoothFn (flowMetricDefect_smooth X o h U P ρ hf hs.1)).measurable
  have hBound := flowMetricDefect_abs_bound X o h U P ρ hf hs.1
  apply le_min
  · exact (le_abs_self _).trans
      (dirichletMinimalKernelCandidate_bounded_evolution_le X.metric X.kahler_metric μ hμ O hO
        (flowMetricDefect X h s) hMeas.aestronglyMeasurable n (Nat.cast_nonneg n) hBound hb x).2
  · have hh := hMean μ hμ O hO (flowMetricDefect X h s) hMeas ⟨n,hBound⟩
      (fun y => (flowMetricDefect_bounds X o h U P ρ hf hs.1 y).1)
      (A*s) (mul_nonneg hA.le hs.1)
      (fun R hR => (hAverage μ hμ R hR s hs).2) L hL b hb hbL x hx
    convert hh using 1 <;> ring

theorem flowMetricDefect_heat_gradient_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    {s : ℝ} (hs : 0 ≤ s) (x : Pt X) {b : ℝ} (hb : 0 < b) :
    Real.sqrt (gradNormSq X.metric.form (fun z => boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
      (flowMetricDefect X h s) b z) x) ≤
      LeafProofs.L24Aux.localGradientConstant n*(n : ℝ)/Real.sqrt b := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (complexManifold_dimension_pos X.manifold)
  exact dirichletMinimalBoundedHeat_gradient_bound X.metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ O hO (flowMetricDefect X h s)
    (LeafProofs.L18Aux.continuous_of_smoothFn
      (flowMetricDefect_smooth X o h U P ρ hf hs)).aestronglyMeasurable
    n hn (flowMetricDefect_abs_bound X o h U P ρ hf hs)
    (fun y => (flowMetricDefect_bounds X o h U P ρ hf hs y).1) x hb

end Yau.Proofs.F03Aux
