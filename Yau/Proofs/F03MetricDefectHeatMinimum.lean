import Yau.Proofs.F03MetricDefectHeatGradient
import Yau.Proofs.F03HeatMinimumNumerics

/-! One common constant controls the actual heat value and gradient by the same scale minimum. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L24Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem flowMetricDefect_heat_common_minimum (hP07 : P07) (hP08 : P08)
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
        C*min 1 ((s/L)*(L/Real.sqrt b)^(2*n+3)) ∧
      Real.sqrt (gradNormSq X.metric.form (fun z => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b z) x) ≤
        C/Real.sqrt b*min 1 ((s/L)*(L/Real.sqrt b)^(2*n+3)) := by
  obtain ⟨A,hA,hMean⟩ := flowMetricDefect_heat_mean_bound hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  obtain ⟨B,hB,hGradient⟩ := flowMetricDefect_heat_gradient_mean_bound hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hG := (localGradientConstant_pos n).le
  let C := (n : ℝ)+A+localGradientConstant n*n+B+1
  have hCn : (n : ℝ) ≤ C := by dsimp [C];nlinarith [mul_nonneg hG hn]
  have hCA : A ≤ C := by dsimp [C];nlinarith
  have hCG : localGradientConstant n*n ≤ C := by dsimp [C];nlinarith
  have hCB : B ≤ C := by dsimp [C];nlinarith [mul_nonneg hG hn]
  refine ⟨C,by dsimp [C];positivity,fun μ hμ O hO s hs L hL b hb hbL x hx => ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hRoot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hRootL : Real.sqrt b ≤ L := Real.sqrt_le_iff.mpr ⟨hL0.le,hbL⟩
  have hRatio1 : 1 ≤ L/Real.sqrt b := (one_le_div hRoot).mpr hRootL
  have hPow : (L/Real.sqrt b)^(2*n) ≤ (L/Real.sqrt b)^(2*n+3) :=
    pow_le_pow_right₀ hRatio1 (by omega)
  have hq : 0 ≤ (s/L)*(L/Real.sqrt b)^(2*n+3) := by positivity
  have hm := hMean μ hμ O hO s hs L hL b hb hbL x hx
  have hg := hGradient μ hμ O hO s hs L hL b hb hbL x hx
  constructor
  · apply le_common_constant_min hq hCn hCA (hm.trans (min_le_left _ _))
    calc
      _ ≤ A*s/L*(L/Real.sqrt b)^(2*n) := hm.trans (min_le_right _ _)
      _ ≤ A*((s/L)*(L/Real.sqrt b)^(2*n+3)) := by
        have hh := mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ A*(s/L))
        convert hh using 1 <;> ring
  · apply div_sqrt_mul_le_of_scaled_bound hb
    apply le_common_constant_min hq hCG hCB
      ((le_div_iff₀ hRoot).mp (hg.trans (min_le_left _ _)))
    have hh := sqrt_scaled_le_of_fraction_bound hb (hg.trans (min_le_right _ _))
    exact hh.trans (by
      have hPow' := mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ B*(s/L))
      convert hPow' using 1 <;> ring)

end Yau.Proofs.F03Aux
