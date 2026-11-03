import Yau.Proofs.F03DyadicCorrectionBudgets
import Yau.Proofs.F03ComparisonWeightGradient
import Yau.Proofs.F03DyadicWeightBounds

/-! The original physical-gradient cutoff inequality for the actual dyadic weight. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

theorem metricDefectDyadicWeight_gradient_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      gradNormSq X.metric.form (fun y => metricDefectDyadicWeight X h μ hμ O hO u A k y s) x ≤
        (C*metricDefectDyadicWeight X h μ hμ O hO u A k x s/u x)^2 := by
  obtain ⟨B,hB,hBudget⟩ := metricDefectDyadicCorrection_uniform_budgets hP06 hP07 hP08 X o h U P ρ hf u hu hT
  refine ⟨1+(k:ℝ)*B+A*(B+2*B^2),by positivity,fun μ hμ O hO s hs x => ?_⟩
  have hData := (hBudget x).2.2.2 μ hμ O hO s hs
  exact comparisonWeight_gradient_bound X.metric.form u (metricDefectDyadicCorrection X h μ hμ O hO u)
    hu.1 (fun y => zero_lt_one.trans_le (hu.2.2.1 y)) A hA k s
    ((metricDefectDyadicCorrection_smoothSpaceC1Time X o h U P ρ hf u hu hT μ hμ O hO).1 s hs)
    x hB (hBudget x).2.2.1 (hBudget x).1 hData.1 hData.2.1

end Yau.Proofs.F03Aux
