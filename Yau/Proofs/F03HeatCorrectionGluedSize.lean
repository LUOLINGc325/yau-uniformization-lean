import Yau.Proofs.F03HeatCorrectionGluing
import Yau.Proofs.F03DyadicConvexBudget

/-! The actual dyadic correction has the global fractional size bound at the given exhaustion scale. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

theorem controlledExhaustion_distance_le
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ C : ℝ,0 < C ∧ ∀ x,inducedDistance X.metric.form o x ≤ C*u x := by
  obtain ⟨C,hC,hBound⟩ := hu.2.2.2
  refine ⟨C,hC,fun x => ?_⟩
  have hLower : (1+inducedDistance X.metric.form o x)/C ≤ u x := by
    simpa only [distFrom,div_eq_mul_inv,mul_comm] using (hBound x).1
  have hh := (div_le_iff₀ hC).mp hLower
  nlinarith

theorem metricDefectDyadicCorrection_size_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      |metricDefectDyadicCorrection X h μ hμ O hO u x s| ≤
        C*s^(heatDecayExponent n)*(u x)^(2-heatDecayExponent n) := by
  obtain ⟨D,hD,hDist⟩ := controlledExhaustion_distance_le X o u hu
  obtain ⟨K,hK,hBound⟩ := metricDefectHeatCorrection_size_bound hP06 hP07 hP08
    X o h U P ρ hf hT (2*D) (by positivity)
  have hα : 0 ≤ 2-heatDecayExponent n := by linarith [heatDecayExponent_lt_one n]
  refine ⟨K*(2:ℝ)^(2-heatDecayExponent n),by positivity,fun μ hμ O hO s hs x => ?_⟩
  have hBudget := dyadicGluing_rpow_budget u
    (fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)) x (hu.2.2.1 x) s
    (mul_nonneg hK.le (Real.rpow_nonneg hs.1 _)) hα
    (fun j hj => hBound μ hμ O hO s hs ((2:ℝ)^j)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) x (by
        have hScale := (dyadicPartition_scale_support (hu.2.2.1 x) j hj).2
        have hDistance := hDist x
        nlinarith))
  change |dyadicGluing u (fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)) x s| ≤ _
  convert hBudget using 1 <;> ring

end Yau.Proofs.F03Aux
