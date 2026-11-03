import Yau.Proofs.F03HeatCorrectionGluedDerivative
import Yau.Proofs.F03WeightRegularity
import Yau.Proofs.F03PolynomialIntegrability

/-! Actual positivity, polynomial comparability, all-volume integrability and time growth of the dyadic comparison weight. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

def metricDefectDyadicWeight (X : KahlerManifold n) (h : Flow X)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (u : Pt X → ℝ) (A : ℝ) (k : ℕ) : STF X :=
  comparisonWeight u (metricDefectDyadicCorrection X h μ hμ O hO u) A k

theorem metricDefectDyadicCorrection_size_coarse (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      |metricDefectDyadicCorrection X h μ hμ O hO u x s| ≤ C*(u x)^2*s^(heatDecayExponent n) := by
  obtain ⟨C,hC,hSize⟩ := metricDefectDyadicCorrection_size_bound hP06 hP07 hP08 X o h U P ρ hf u hu hT
  refine ⟨C,hC,fun μ hμ O hO s hs x => ?_⟩
  have hPower : (u x)^(2-heatDecayExponent n) ≤ (u x)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le (hu.2.2.1 x)
      (show 2-heatDecayExponent n ≤ (2:ℝ) from by linarith [heatDecayExponent_pos n])
  calc
    _ ≤ C*s^(heatDecayExponent n)*(u x)^(2-heatDecayExponent n) := hSize μ hμ O hO s hs x
    _ ≤ C*s^(heatDecayExponent n)*(u x)^2 :=
      mul_le_mul_of_nonneg_left hPower (mul_nonneg hC.le (Real.rpow_nonneg hs.1 _))
    _ = _ := by ring

theorem metricDefectDyadicWeight_base_controls (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 0 ≤ A) (k : ℕ) (hk : 2*n < k) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ₀ : Measure (Pt X)) (hμ₀ : IsRiemannianVolume X.metric.form μ₀)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O),
      SmoothSpaceC1Time (metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k) (Icc 0 T) ∧
      (∀ μ,IsRiemannianVolume X.metric.form μ → ∀ t ∈ Icc (0:ℝ) T,
        (∫⁻ x,ENNReal.ofReal (metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k x t) ∂μ) < ⊤) ∧
      ∀ x t,t ∈ Icc (0:ℝ) T →
        0 < metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k x t ∧
        C⁻¹*(u x)^(-(k:ℤ)) ≤ metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k x t ∧
        metricDefectDyadicWeight X h μ₀ hμ₀ O hO u A k x t ≤ C*(u x)^(-(k:ℤ)) := by
  obtain ⟨K,hK,hSize⟩ := metricDefectDyadicCorrection_size_coarse hP06 hP07 hP08 X o h U P ρ hf u hu hT
  let B := K*T^(heatDecayExponent n)
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hSlab (μ₀ : Measure (Pt X)) (hμ₀ : IsRiemannianVolume X.metric.form μ₀)
      (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Pt X) :
      |metricDefectDyadicCorrection X h μ₀ hμ₀ O hO u x t| ≤ B*(u x)^2 := by
    calc
      _ ≤ K*(u x)^2*t^(heatDecayExponent n) := hSize μ₀ hμ₀ O hO t ht x
      _ ≤ K*(u x)^2*T^(heatDecayExponent n) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht.1 ht.2 (heatDecayExponent_pos n).le) (by positivity)
      _ = _ := by dsimp [B];ring
  refine ⟨Real.exp (A*B),Real.exp_pos _,fun μ₀ hμ₀ O hO => ⟨?_,?_,?_⟩⟩
  · exact comparisonWeight_smoothSpaceC1Time u hu.1 (fun x => zero_lt_one.trans_le (hu.2.2.1 x)) _
      (metricDefectDyadicCorrection_smoothSpaceC1Time X o h U P ρ hf u hu hT μ₀ hμ₀ O hO) A k
  · intro μ hμ t ht
    exact comparisonWeight_integrable_of_size X o h U P ρ hf u hu _ hA hB k hk t
      (hSlab μ₀ hμ₀ O hO t ht) μ hμ
  · intro x t ht
    exact ⟨comparisonWeight_pos u _ A k x t (zero_lt_one.trans_le (hu.2.2.1 x)),
      comparisonWeight_bounds u _ hA hB k x t (zero_lt_one.trans_le (hu.2.2.1 x)) (hSlab μ₀ hμ₀ O hO t ht x)⟩

theorem metricDefectDyadicWeight_time_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Ioc 0 T → ∀ x,
      deriv (metricDefectDyadicWeight X h μ hμ O hO u A k x) s ≤
        C*(1+s^(heatDecayExponent n-1))*metricDefectDyadicWeight X h μ hμ O hO u A k x s := by
  obtain ⟨B,hB,hSize⟩ := metricDefectDyadicCorrection_size_coarse hP06 hP07 hP08 X o h U P ρ hf u hu hT
  obtain ⟨D,hD,hTime⟩ := metricDefectDyadicCorrection_time_lower_bound X o h U P ρ hf u hu hT
  refine ⟨1+A*(B+D),by positivity,fun μ hμ O hO s hs x => ?_⟩
  have hDiff := metricDefectDyadicCorrection_differentiableAt_pos X o h U P ρ hf u hu μ hμ O hO x hs.1
  have hBound := comparisonWeight_time_bound u (metricDefectDyadicCorrection X h μ hμ O hO u)
    hA hB.le hD.le k x (hu.2.2.1 x) hs.1 hDiff.hasDerivAt
    (hSize μ hμ O hO s ⟨hs.1.le,hs.2⟩ x) (hTime μ hμ O hO s hs x)
  apply hBound.trans
  apply mul_le_mul_of_nonneg_right _ (comparisonWeight_pos u _ A k x s (zero_lt_one.trans_le (hu.2.2.1 x))).le
  apply mul_le_mul_of_nonneg_right (by linarith)
    (add_nonneg zero_le_one (Real.rpow_nonneg hs.1.le _))

end Yau.Proofs.F03Aux
