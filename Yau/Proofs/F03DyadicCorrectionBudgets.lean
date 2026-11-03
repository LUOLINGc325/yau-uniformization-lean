import Yau.Proofs.F03HeatCorrectionGluedHessian
import Yau.Proofs.F03HeatCorrectionGluedGradient

/-! One actual uniform budget supplies every scalar-calculus input for the final comparison weight. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ}

theorem metricDefectDyadicCorrection_uniform_budgets (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ,0 < B ∧ ∀ x,
      Real.sqrt (gradNormSq X.metric.form u x) ≤ B ∧
      HermAbsLE (levi u x) (gMat X.metric.form x) (B/u x) ∧
      1 ≤ (u x)^(heatDecayExponent n) ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T →
      |metricDefectDyadicCorrection X h μ hμ O hO u x s| ≤ B*(u x)^2/(u x)^(heatDecayExponent n) ∧
      Real.sqrt (gradNormSq X.metric.form
        (fun y => metricDefectDyadicCorrection X h μ hμ O hO u y s) x) ≤ B*u x/(u x)^(heatDecayExponent n) ∧
      HermLE (gMat X.metric.form x-gMat (h s) x-
        Complex.ofReal (B/(u x)^(heatDecayExponent n)) • gMat X.metric.form x)
        (levi (fun y => metricDefectDyadicCorrection X h μ hμ O hO u y s) x) := by
  obtain ⟨Q,hQ,hU⟩ := hu.2.2.2
  obtain ⟨K₀,hK₀,hSize⟩ := metricDefectDyadicCorrection_size_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT
  obtain ⟨K₁,hK₁,hGrad⟩ := metricDefectDyadicCorrection_gradient_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT
  obtain ⟨K₂,hK₂,hLevi⟩ := metricDefectDyadicCorrection_levi_lower_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT
  let C₀ := K₀*T^(heatDecayExponent n)
  let C₁ := K₁*T^(heatDecayExponent n)
  have hC₀ : 0 < C₀ := by dsimp [C₀];positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁];positivity
  let B := 1+Q+C₀+C₁+K₂
  have hB : 0 < B := by dsimp [B];positivity
  have hBQ : Q ≤ B := by dsimp [B];linarith
  have hB₀ : C₀ ≤ B := by dsimp [B];linarith
  have hB₁ : C₁ ≤ B := by dsimp [B];linarith
  have hB₂ : K₂ ≤ B := by dsimp [B];linarith
  refine ⟨B,hB,fun x => ?_⟩
  have hu1 := hu.2.2.1 x
  have hu0 : 0 < u x := zero_lt_one.trans_le hu1
  have hG : (gMat X.metric.form x).PosSemidef :=
    (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hULevi : HermAbsLE (levi u x) (gMat X.metric.form x) (Q/u x) := by
    constructor
    · simpa only [Complex.ofReal_neg,Complex.ofReal_div] using (hU x).2.2.2.1
    · exact (hU x).2.2.2.2
  refine ⟨(Real.sqrt_le_iff.mpr ⟨hQ.le,(hU x).2.2.1⟩).trans hBQ,
    hermAbsLE_mono hG hULevi (div_le_div_of_nonneg_right hBQ hu0.le),
    Real.one_le_rpow hu1 (heatDecayExponent_pos n).le,fun μ hμ O hO s hs => ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hTime : s^(heatDecayExponent n) ≤ T^(heatDecayExponent n) :=
    Real.rpow_le_rpow hs.1 hs.2 (heatDecayExponent_pos n).le
  have hPower : 0 < (u x)^(heatDecayExponent n) := Real.rpow_pos_of_pos hu0 _
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ K₀*s^(heatDecayExponent n)*(u x)^(2-heatDecayExponent n) := hSize μ hμ O hO s hs x
      _ ≤ K₀*T^(heatDecayExponent n)*(u x)^(2-heatDecayExponent n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTime hK₀.le) (by positivity)
      _ = C₀*(u x)^2/(u x)^(heatDecayExponent n) := by
        rw [Real.rpow_sub hu0 2 (heatDecayExponent n),Real.rpow_two]
        dsimp [C₀]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB₀ (sq_nonneg _)) hPower.le
  · calc
      _ ≤ K₁*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) := hGrad μ hμ O hO s hs x
      _ ≤ K₁*T^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTime hK₁.le) (by positivity)
      _ = C₁*u x/(u x)^(heatDecayExponent n) := by
        rw [Real.rpow_sub hu0 1 (heatDecayExponent n),Real.rpow_one]
        dsimp [C₁]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB₁ hu0.le) hPower.le
  · have hOriginal := hLevi μ hμ O hO s hs x
    have hError := hG.smul (Complex.zero_le_real.mpr
      (sub_nonneg.mpr (div_le_div_of_nonneg_right hB₂ hPower.le)))
    unfold HermLE at hOriginal ⊢
    convert hOriginal.add hError using 1
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
    ring

end Yau.Proofs.F03Aux
