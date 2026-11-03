import Yau.Proofs.F03HeatCorrectionGluedSize
import Yau.Proofs.F03HeatCorrectionGradient
import Yau.Proofs.F03GradientLocality
import Yau.Proofs.F03FiniteDyadicBudget

/-! The actual dyadic correction has the global fractional physical-gradient bound. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

theorem metricDefectDyadicCorrection_gradient_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      Real.sqrt (gradNormSq X.metric.form
        (fun y => metricDefectDyadicCorrection X h μ hμ O hO u y s) x) ≤
        C*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) := by
  obtain ⟨D,hD,hDist⟩ := controlledExhaustion_distance_le X o u hu
  obtain ⟨Q,hQ,hU⟩ := hu.2.2.2
  obtain ⟨K₀,hK₀,hSize⟩ := metricDefectHeatCorrection_size_bound hP06 hP07 hP08
    X o h U P ρ hf hT (2*D) (by positivity)
  obtain ⟨K₁,hK₁,hGradient⟩ := metricDefectHeatCorrection_gradient_bound hP07 hP08
    X o h U P ρ hf hT (2*D) (by positivity)
  obtain ⟨B,hB,hPhi⟩ := dyadicPartition_derivative_bounds
  let A := K₁*(2:ℝ)^(1-heatDecayExponent n)
  let E := 2*B*K₀*Q*(2:ℝ)^(2-heatDecayExponent n)
  have hA : 0 < A := by dsimp [A];positivity
  have hE : 0 < E := by dsimp [E];positivity
  have hα : 0 ≤ 1-heatDecayExponent n := by linarith [heatDecayExponent_lt_one n]
  have hα' : 0 ≤ 2-heatDecayExponent n := by linarith
  refine ⟨A+3*E,by positivity,fun μ hμ O hO s hs x => ?_⟩
  let F : ℕ → Pt X → ℝ → ℝ := fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)
  have hs0 : 0 ≤ s := hs.1
  have hu1 := hu.2.2.1 x
  have huPos : 0 < u x := zero_lt_one.trans_le hu1
  have hNear (j : ℕ) (hScale : u x ≤ 2*(2:ℝ)^j) :
      inducedDistance X.metric.form o x ≤ (2*D)*(2:ℝ)^j := by
    have hh := hDist x
    nlinarith
  have hUSqrt : Real.sqrt (gradNormSq X.metric.form u x) ≤ Q :=
    Real.sqrt_le_iff.mpr ⟨hQ.le,(hU x).2.2.1⟩
  have hPow : (u x)^(2-heatDecayExponent n)/(u x)=(u x)^(1-heatDecayExponent n) := by
    calc
      _ = (u x)^((2-heatDecayExponent n)-1) :=
        (Real.rpow_sub_one huPos.ne' (2-heatDecayExponent n)).symm
      _ = _ := by congr 1 <;> ring
  have hSmooth (j : ℕ) : SmoothFn (fun y => F j y s) :=
    metricDefectHeatCorrection_smooth X o h U P ρ hf μ hμ O hO _ hs.1
  have hGlued : SmoothFn (fun y => dyadicGluing u F y s) :=
    (metricDefectDyadicCorrection_smoothSpaceC1Time X o h U P ρ hf u hu hT μ hμ O hO).1 s hs
  obtain ⟨N,hPartition,hFinite⟩ := dyadicGluing_gradient_finite_bound X.metric.form u hu.1 hu.2.2.1 F s hSmooth hGlued x
  have hMain : (∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)*
      Real.sqrt (gradNormSq X.metric.form (fun y => F j y s) x)) ≤
      A*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)*
          (A*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n)) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hZero : dyadicPartition j (u x)=0
        · rw [hZero,zero_mul,zero_mul]
        have hScale := dyadicPartition_scale_support hu1 j hZero
        apply mul_le_mul_of_nonneg_left _ (dyadicPartition_nonnegative j (zero_le_one.trans hu1))
        calc
          _ ≤ K₁*s^(heatDecayExponent n)*((2:ℝ)^j)^(1-heatDecayExponent n) :=
            hGradient μ hμ O hO s hs _ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) x (hNear j hScale.2)
          _ ≤ K₁*s^(heatDecayExponent n)*((2:ℝ)^(1-heatDecayExponent n)*(u x)^(1-heatDecayExponent n)) :=
            mul_le_mul_of_nonneg_left (dyadicScale_rpow_le hu1 j hScale.1 hα) (by positivity)
          _ = _ := by dsimp [A];ring
      _ = _ := by rw [← Finset.sum_mul,hPartition,one_mul]
  have hErrorPoint (j : ℕ) : |deriv (dyadicPartition j) (u x)| *
      (|F j x s| *Real.sqrt (gradNormSq X.metric.form u x)) ≤
      E*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) := by
    by_cases hZero : deriv (dyadicPartition j) (u x)=0
    · rw [hZero,abs_zero,zero_mul];positivity
    have hScale := dyadicPartition_deriv_scale_support hu1 j hZero
    have hSizeJ := hSize μ hμ O hO s hs ((2:ℝ)^j)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) x (hNear j hScale.2)
    have hDeriv := (dyadicScale_derivative_at_value hB.le hu1 j (hPhi j (u x)).1 (hPhi j (u x)).2).1
    calc
      _ ≤ (2*B/u x)*((K₀*s^(heatDecayExponent n)*((2:ℝ)^j)^(2-heatDecayExponent n))*Q) :=
        mul_le_mul hDeriv (mul_le_mul hSizeJ hUSqrt (Real.sqrt_nonneg _) (by positivity))
          (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
      _ ≤ (2*B/u x)*((K₀*s^(heatDecayExponent n)*
          ((2:ℝ)^(2-heatDecayExponent n)*(u x)^(2-heatDecayExponent n)))*Q) := by
        gcongr
        exact dyadicScale_rpow_le hu1 j hScale.1 hα'
      _ = E*s^(heatDecayExponent n)*((u x)^(2-heatDecayExponent n)/u x) := by dsimp [E];ring
      _ = _ := by rw [hPow]
  have hError := dyadic_firstDerivative_sum_budget hu1
    (show 0 ≤ E*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n) from by positivity)
    (Finset.range (N+1)) (fun j => |F j x s| *Real.sqrt (gradNormSq X.metric.form u x))
    (fun j _ => hErrorPoint j)
  change Real.sqrt (gradNormSq X.metric.form (fun y => dyadicGluing u F y s) x) ≤ _
  apply hFinite.trans
  rw [Finset.sum_add_distrib]
  have hError' : (∑ j ∈ Finset.range (N+1),|deriv (dyadicPartition j) (u x)| * |F j x s| *
      Real.sqrt (gradNormSq X.metric.form u x)) ≤ 3*(E*s^(heatDecayExponent n)*(u x)^(1-heatDecayExponent n)) := by
    simpa only [mul_assoc] using hError
  nlinarith

end Yau.Proofs.F03Aux
