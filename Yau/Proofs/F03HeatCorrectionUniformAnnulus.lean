import Yau.Proofs.F03HeatCorrectionGluedGradient
import Yau.Proofs.F03HeatCorrectionHessian

/-! One actual constant controls all heat corrections on their exhaustion annuli. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ}

theorem metricDefectHeatCorrection_uniform_annulus (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ,0 < B ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ j : ℕ,∀ x,
      (2:ℝ)^j/2 ≤ u x → u x ≤ 2*(2:ℝ)^j →
      |metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j) x s| ≤ B*(u x)^(2-heatDecayExponent n) ∧
      Real.sqrt (gradNormSq X.metric.form
        (fun y => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j) y s) x) ≤ B*(u x)^(1-heatDecayExponent n) ∧
      HermLE (gMat X.metric.form x-gMat (h s) x-
        Complex.ofReal (B/(u x)^(heatDecayExponent n)) • gMat X.metric.form x)
        (levi (fun y => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j) y s) x) := by
  obtain ⟨D,hD,hDistance⟩ := controlledExhaustion_distance_le X o u hu
  obtain ⟨K₀,hK₀,hSize⟩ := metricDefectHeatCorrection_size_bound hP06 hP07 hP08 X o h U P ρ hf hT (2*D) (by positivity)
  obtain ⟨K₁,hK₁,hGrad⟩ := metricDefectHeatCorrection_gradient_bound hP07 hP08 X o h U P ρ hf hT (2*D) (by positivity)
  obtain ⟨K₂,hK₂,hLevi⟩ := metricDefectHeatCorrection_hessian_bound hP06 hP07 hP08 X o h U P ρ hf hT (2*D) (by positivity)
  let C₀ := K₀*T^(heatDecayExponent n)*(2:ℝ)^(2-heatDecayExponent n)
  let C₁ := K₁*T^(heatDecayExponent n)*(2:ℝ)^(1-heatDecayExponent n)
  let C₂ := 2*K₂*T
  have hC₀ : 0 < C₀ := by dsimp [C₀];positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁];positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂];positivity
  let B := 1+C₀+C₁+C₂
  have hB : 0 < B := by dsimp [B];positivity
  have hB₀ : C₀ ≤ B := by dsimp [B];linarith
  have hB₁ : C₁ ≤ B := by dsimp [B];linarith
  have hB₂ : C₂ ≤ B := by dsimp [B];linarith
  refine ⟨B,hB,fun μ hμ O hO s hs j x hLow hHigh => ?_⟩
  have hx1 := hu.2.2.1 x
  have hx0 : 0 < u x := zero_lt_one.trans_le hx1
  have hs0 : 0 ≤ s := hs.1
  have hL : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hNear : inducedDistance X.metric.form o x ≤ (2*D)*(2:ℝ)^j := by
    have hh := hDistance x
    nlinarith
  have hTime : s^(heatDecayExponent n) ≤ T^(heatDecayExponent n) :=
    Real.rpow_le_rpow hs.1 hs.2 (heatDecayExponent_pos n).le
  have hExp₁ : 0 ≤ 1-heatDecayExponent n := by linarith [heatDecayExponent_lt_one n]
  have hExp₂ : 0 ≤ 2-heatDecayExponent n := by linarith
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ K₀*s^(heatDecayExponent n)*((2:ℝ)^j)^(2-heatDecayExponent n) := hSize μ hμ O hO s hs _ hL x hNear
      _ ≤ K₀*T^(heatDecayExponent n)*((2:ℝ)^(2-heatDecayExponent n)*(u x)^(2-heatDecayExponent n)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTime hK₀.le) (dyadicScale_rpow_le hx1 j hLow hExp₂)
          (by positivity) (by positivity)
      _ = C₀*(u x)^(2-heatDecayExponent n) := by dsimp [C₀];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB₀ (by positivity)
  · calc
      _ ≤ K₁*s^(heatDecayExponent n)*((2:ℝ)^j)^(1-heatDecayExponent n) := hGrad μ hμ O hO s hs _ hL x hNear
      _ ≤ K₁*T^(heatDecayExponent n)*((2:ℝ)^(1-heatDecayExponent n)*(u x)^(1-heatDecayExponent n)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTime hK₁.le) (dyadicScale_rpow_le hx1 j hLow hExp₁)
          (by positivity) (by positivity)
      _ = C₁*(u x)^(1-heatDecayExponent n) := by dsimp [C₁];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB₁ (by positivity)
  · have hInv := dyadicScale_inverse_le hx1 j hHigh
    have hSmall : (u x)^(heatDecayExponent n) ≤ u x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (heatDecayExponent_lt_one n).le
    have hPowerPos : 0 < (u x)^(heatDecayExponent n) := Real.rpow_pos_of_pos hx0 _
    have hDelta : K₂*s/(2:ℝ)^j ≤ B/(u x)^(heatDecayExponent n) := by
      calc
        _ = (K₂*s)*(1/(2:ℝ)^j) := by ring
        _ ≤ (K₂*T)*(2/u x) := mul_le_mul (mul_le_mul_of_nonneg_left hs.2 hK₂.le) hInv (by positivity) (by positivity)
        _ = C₂/u x := by dsimp [C₂];ring
        _ ≤ C₂/(u x)^(heatDecayExponent n) := (div_le_div_iff₀ hx0 hPowerPos).mpr
          (mul_le_mul_of_nonneg_left hSmall hC₂.le)
        _ ≤ _ := div_le_div_of_nonneg_right hB₂ hPowerPos.le
    have hOriginal := (hLevi μ hμ O hO s hs _ hL x hNear).1
    have hG : (gMat X.metric.form x).PosSemidef :=
      (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    have hError := hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hDelta))
    unfold HermLE at hOriginal ⊢
    convert hOriginal.add hError using 1
    ext a b
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
    ring

end Yau.Proofs.F03Aux
