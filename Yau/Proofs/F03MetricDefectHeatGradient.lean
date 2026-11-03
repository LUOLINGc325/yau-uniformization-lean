import Yau.Proofs.F03MetricDefectHeat

/-! The small ball mean controls the actual heat gradient on the same local cylinder. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L24Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem sqrt_scale_ratio_le_twice {L b τ : ℝ} (hL : 0 ≤ L) (hb : 0 < b)
    (hτ : 0 < τ) (hbτ : b/2 ≤ τ) : L/Real.sqrt τ ≤ 2*(L/Real.sqrt b) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hSqb := Real.sq_sqrt hb.le
  have hSqτ := Real.sq_sqrt hτ.le
  have hRoot : Real.sqrt b ≤ 2*Real.sqrt τ := by nlinarith
  calc
    L/Real.sqrt τ ≤ (2*L)/Real.sqrt b :=
      (div_le_div_iff₀ hsτ hsb).mpr (by nlinarith [mul_le_mul_of_nonneg_left hRoot hL])
    _ = _ := by ring

theorem flowMetricDefect_heat_gradient_mean_bound (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ b : ℝ,0 < b → b ≤ L^2 →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      Real.sqrt (gradNormSq X.metric.form (fun z => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b z) x) ≤
        min (localGradientConstant n*(n : ℝ)/Real.sqrt b)
          (C*s/(L*Real.sqrt b)*(L/Real.sqrt b)^(2*n)) := by
  obtain ⟨K,hK,hMean⟩ := flowMetricDefect_heat_mean_bound hP07 hP08 X o h U P ρ hf hT
    (C₀+1) (by linarith)
  let C := localGradientConstant n*K*2^(2*n)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (complexManifold_dimension_pos X.manifold)
  have hGrad := localGradientConstant_pos n
  refine ⟨C,by dsimp [C];positivity,fun μ hμ O hO s hs L hL b hb hbL x hx => ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hRootL : Real.sqrt b ≤ L := Real.sqrt_le_iff.mpr ⟨hL0.le,hbL⟩
  have hMeas := (LeafProofs.L18Aux.continuous_of_smoothFn
    (flowMetricDefect_smooth X o h U P ρ hf hs.1)).aestronglyMeasurable (μ := μ)
  have hBound := flowMetricDefect_abs_bound X o h U P ρ hf hs.1
  let A := K*2^(2*n)*s/L*(L/Real.sqrt b)^(2*n)
  have hA : 0 ≤ A := by dsimp [A];positivity
  apply le_min
  · exact flowMetricDefect_heat_gradient_bound X o h U P ρ hf μ hμ O hO hs.1 x hb
  · have hh := nonnegative_heat_gradient_at_sqrt_scale X.metric X.kahler_metric
      (F02Aux.initialRicci_posSemidef X o h U P ρ hf)
      (fun z τ => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) (flowMetricDefect X h s) τ z)
      (dirichletMinimalBoundedHeat_smooth X.metric X.kahler_metric μ hμ O hO
        (flowMetricDefect X h s) hMeas n hn hBound)
      (fun z τ hτ => dirichletMinimalBoundedHeat_hasDerivAt X.metric X.kahler_metric μ hμ O hO
        (flowMetricDefect X h s) hMeas n hn hBound z hτ)
      (fun z τ hτ => dirichletMinimalBoundedHeat_nonnegative X.metric X.kahler_metric μ hμ O hO
        (flowMetricDefect X h s) (fun y => (flowMetricDefect_bounds X o h U P ρ hf hs.1 y).1) hτ.le z)
      x hb hA (fun z τ hz hτ => by
        have hτ0 : 0 < τ := (half_pos hb).trans_le hτ.1
        have hzNear : inducedDistance X.metric.form o z ≤ (C₀+1)*L := by
          have hTri := X.metric.induced_distance_triangle o x z
          nlinarith
        have hRatio := pow_le_pow_left₀ (by positivity : 0 ≤ L/Real.sqrt τ)
          (sqrt_scale_ratio_le_twice hL0.le hb hτ0 hτ.1) (2*n)
        calc
          _ ≤ K*s/L*(L/Real.sqrt τ)^(2*n) :=
            (hMean μ hμ O hO s hs L hL τ hτ0 (hτ.2.trans hbL) z hzNear).trans (min_le_right _ _)
          _ ≤ K*s/L*((2*(L/Real.sqrt b))^(2*n)) :=
            mul_le_mul_of_nonneg_left hRatio (by positivity)
          _ = A := by dsimp [A];rw [mul_pow];ring)
    convert hh using 1 <;> dsimp [A,C] <;> ring

end Yau.Proofs.F03Aux
