import Yau.Proofs.F03DyadicWeightHessian
import Yau.Proofs.G02
import Yau.Proofs.HeatSmoothExhaustion

/-! The original F03 cutoff for the given flow, from exact registered scalar-heat and initial-data parents. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs
open Yau Blueprint F03Aux HeatConcreteBindings

/-- Every cutoff clause is proved for one actual weight. The only conditional inputs are the
exact registered P06, P07 and P08 statements; the volume and exhaustion are constructed internally. -/
theorem F03_of_P06_P07_P08 (hP06 : P06) (hP07 : P07) (hP08 : P08) : F03 := by
  intro n X o h U P ρ hf u hu T hT
  refine ⟨heatDecayExponent n,heatDecayExponent_pos n,2*n+1,fun k hk => ?_⟩
  have hk' : 2*n < k := by omega
  obtain ⟨A,hA,C₃,hC₃,hLevi⟩ := metricDefectDyadicWeight_levi_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT k
  obtain ⟨C₀,hC₀,hBase⟩ := metricDefectDyadicWeight_base_controls hP06 hP07 hP08 X o h U P ρ hf u hu hT hA.le k hk'
  obtain ⟨C₁,hC₁,hGrad⟩ := metricDefectDyadicWeight_gradient_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT hA.le k
  obtain ⟨C₂,hC₂,hTime⟩ := metricDefectDyadicWeight_time_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT hA.le k
  obtain ⟨μ₀,hμ₀,_⟩ := NodeProofs.G02_proved n X.manifold X.metric.form
    (LeafProofs.L18Aux.metricSmooth_of_smoothMetric X.metric)
  obtain ⟨O,hO⟩ := SmoothExhaustionAux.smoothExhaustion_exists X.manifold
  let χ := metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k
  let C := 1+C₀+C₁+C₂+C₃
  have hC : 0 < C := by dsimp [C];linarith
  have hC₀C : C₀ ≤ C := by dsimp [C];linarith
  have hC₁C : C₁ ≤ C := by dsimp [C];linarith
  have hC₂C : C₂ ≤ C := by dsimp [C];linarith
  have hC₃C : C₃ ≤ C := by dsimp [C];linarith
  have hActualBase := hBase μ₀ hμ₀ O hO
  refine ⟨χ,C,hC,hActualBase.1,hActualBase.2.1,fun x t ht => ?_⟩
  obtain ⟨hχ,hLower,hUpper⟩ := hActualBase.2.2 x t ht
  have hu0 : 0 < u x := zero_lt_one.trans_le (hu.2.2.1 x)
  have hp : 0 ≤ (u x)^(-(k:ℤ)) := by positivity
  refine ⟨hχ,?_,?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hC hC₀).mpr hC₀C) hp).trans hLower
  · exact hUpper.trans (mul_le_mul_of_nonneg_right hC₀C hp)
  · have hCoeff : C₁*χ x t/u x ≤ C*χ x t/u x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁C hχ.le) hu0.le
    exact (hGrad μ₀ hμ₀ O hO t ht x).trans
      (pow_le_pow_left₀ (div_nonneg (mul_nonneg hC₁.le hχ.le) hu0.le) hCoeff 2)
  · have hH : (gMat (h t) x).PosSemidef :=
      (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    exact hermLE_trans (hLevi μ₀ hμ₀ O hO t ht x)
      (hermLE_coefficient_mono _ hH (mul_le_mul_of_nonneg_right hC₃C hχ.le))
  · intro ht0
    have hCoeff : C₂*(1+t^(heatDecayExponent n-1)) ≤ C*(1+t^(heatDecayExponent n-1)) :=
      mul_le_mul_of_nonneg_right hC₂C (add_nonneg zero_le_one (Real.rpow_nonneg ht0.le _))
    exact (hTime μ₀ hμ₀ O hO t ⟨ht0,ht.2⟩ x).trans
      (mul_le_mul_of_nonneg_right hCoeff hχ.le)

end Yau.Proofs
