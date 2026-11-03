import Yau.Proofs.F03WeightMetricBounds
import Yau.Proofs.F03DyadicWeightGradient
import Yau.Proofs.F03CompactMetricComparison

/-! The actual dyadic weight has the original evolving-metric Levi bound on the whole closed slab. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ}

theorem metricDefectDyadicWeight_levi_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) (k : ℕ) :
    ∃ A : ℝ,0 < A ∧ ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      HermLE (levi (fun y => metricDefectDyadicWeight X h μ hμ O hO u A k y s) x)
        (Complex.ofReal (C*metricDefectDyadicWeight X h μ hμ O hO u A k x s) • gMat (h s) x) := by
  obtain ⟨B,hB,hBudget⟩ := metricDefectDyadicCorrection_uniform_budgets hP06 hP07 hP08 X o h U P ρ hf u hu hT
  obtain ⟨A,hA,R,hR,hFar⟩ := exists_weight_parameters hB.le (heatDecayExponent_pos n) k
  obtain ⟨D,hD,hCompact⟩ := flow_compact_hermLE X o h U P ρ hf hT
    {x | u x ≤ R} (hu.2.1 R)
  let E := weightBaseError B k+weightDecayError B A
  have hBase := weightBaseError_nonneg hB.le k
  have hDecay := weightDecayError_nonneg hB.le hA.le
  have hE : 0 ≤ E := add_nonneg hBase hDecay
  let C := 1+A+E*D
  have hC : 0 < C := by dsimp [C];positivity
  have hAC : A ≤ C := by dsimp [C];nlinarith [mul_nonneg hE hD.le]
  have hEDC : E*D ≤ C := by dsimp [C];linarith
  refine ⟨A,hA,C,hC,fun μ hμ O hO s hs x => ?_⟩
  let χ := metricDefectDyadicWeight X h μ hμ O hO u A k x s
  have hu1 := hu.2.2.1 x
  have hu0 : 0 < u x := zero_lt_one.trans_le hu1
  have hv1 := (hBudget x).2.2.1
  have hv0 : 0 < (u x)^(heatDecayExponent n) := zero_lt_one.trans_le hv1
  have hχ : 0 < χ := comparisonWeight_pos u _ A k x s hu0
  have hG : (gMat X.metric.form x).PosSemidef :=
    (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hH : (gMat (h s) x).PosSemidef :=
    (hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hData := (hBudget x).2.2.2 μ hμ O hO s hs
  have hGeneric := comparisonWeight_hessian_bound X.metric.form u
    (metricDefectDyadicCorrection X h μ hμ O hO u) hu.1
    (fun y => zero_lt_one.trans_le (hu.2.2.1 y)) A hA.le k s
    ((metricDefectDyadicCorrection_smoothSpaceC1Time X o h U P ρ hf u hu hT μ hμ O hO).1 s hs)
    x (gMat X.metric.form x-gMat (h s) x) hB hv1 (hBudget x).1 (hBudget x).2.1
    hData.1 hData.2.1 hData.2.2
  change HermLE (levi (fun y => metricDefectDyadicWeight X h μ hμ O hO u A k y s) x)
    (Complex.ofReal (C*χ) • gMat (h s) x)
  by_cases hx : R ≤ u x
  · have hAbsorbed := metric_defect_absorption _ _ _ hG hH A
      (weightBaseError B k+weightDecayError B A/(u x)^(heatDecayExponent n)) χ (u x)
      hA.le (hFar (u x) hx) hχ.le hu1 hGeneric
    exact hermLE_trans hAbsorbed (hermLE_coefficient_mono _ hH
      (mul_le_mul_of_nonneg_right hAC hχ.le))
  · have hRate : weightDecayError B A/(u x)^(heatDecayExponent n) ≤ weightDecayError B A :=
      (div_le_iff₀ hv0).mpr (by nlinarith [mul_nonneg hDecay (sub_nonneg.mpr hv1)])
    have hError : 0 ≤ weightBaseError B k+weightDecayError B A/(u x)^(heatDecayExponent n) :=
      add_nonneg hBase (div_nonneg hDecay hv0.le)
    have hErrorE : weightBaseError B k+weightDecayError B A/(u x)^(heatDecayExponent n) ≤ E := by
      dsimp [E]
      linarith
    have hDef : (gMat X.metric.form x-gMat (h s) x).PosSemidef := hf.2.2.2.2.1 s hs.1 x
    have hCoarse := metric_defect_coarse_bound _ _ _ hG hDef A
      (weightBaseError B k+weightDecayError B A/(u x)^(heatDecayExponent n)) χ (u x)
      hA.le hError hχ.le hu1 hGeneric
    have hToE := hermLE_coefficient_mono _ hG (mul_le_mul_of_nonneg_right hErrorE hχ.le)
    have hToH := hermLE_real_smul (hCompact x (le_of_not_ge hx) s hs) (mul_nonneg hE hχ.le)
    have hToH' : HermLE (Complex.ofReal (E*χ) • gMat X.metric.form x)
        (Complex.ofReal (E*D*χ) • gMat (h s) x) := by
      convert hToH using 1
      ext i j
      simp only [Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
      ring
    exact hermLE_trans (hermLE_trans (hermLE_trans hCoarse hToE) hToH')
      (hermLE_coefficient_mono _ hH (mul_le_mul_of_nonneg_right hEDC hχ.le))

end Yau.Proofs.F03Aux
