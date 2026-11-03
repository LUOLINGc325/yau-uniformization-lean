import Yau.Proofs.F03MetricDefectHeatMinimum

/-! Actual integrable time majorants for the original metric-defect heat and its gradient. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def heatDecayExponent (n : ℕ) : ℝ := 1/(2*((2*n+3 : ℕ):ℝ))

theorem heatDecayExponent_pos (n : ℕ) : 0 < heatDecayExponent n := by
  dsimp [heatDecayExponent]
  positivity

theorem flowMetricDefect_heat_quarter_majorants (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Ioc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ b : ℝ,0 < b → b ≤ L^2 →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b x ≤
        C*s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(1:ℝ)/4) ∧
      Real.sqrt (gradNormSq X.metric.form (fun z => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b z) x) ≤
        C*s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(3:ℝ)/4) := by
  obtain ⟨C,hC,hBounds⟩ := flowMetricDefect_heat_common_minimum hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  refine ⟨C,hC,fun μ hμ O hO s hs L hL b hb hbL x hx => ?_⟩
  have hp : (2:ℝ) < ((2*n+3:ℕ):ℝ) := by exact_mod_cast (by omega : 2 < 2*n+3)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h := hBounds μ hμ O hO s ⟨hs.1.le,hs.2⟩ L hL b hb hbL x hx
  have hValue : min 1 ((s/L)*(L/Real.sqrt b)^(2*n+3)) ≤
      s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(1:ℝ)/4) := by
    simpa only [Real.rpow_natCast,heatDecayExponent] using heat_minimum_quarter_bound hp hs.1 hL0 hb
  have hGradient : (1/Real.sqrt b)*min 1 ((s/L)*(L/Real.sqrt b)^(2*n+3)) ≤
      s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(3:ℝ)/4) := by
    simpa only [Real.rpow_natCast,heatDecayExponent] using heat_gradient_three_quarter_bound hp hs.1 hL0 hb
  constructor
  · exact h.1.trans (by
      convert mul_le_mul_of_nonneg_left hValue hC.le using 1 <;> ring)
  · apply h.2.trans
    convert mul_le_mul_of_nonneg_left hGradient hC.le using 1 <;> ring

end Yau.Proofs.F03Aux
