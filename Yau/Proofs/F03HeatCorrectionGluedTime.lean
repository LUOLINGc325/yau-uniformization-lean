import Yau.Proofs.F03HeatCorrectionGluedSize
import Yau.Proofs.F03HeatCorrectionTimeLower

/-! The actual locally finite correction has the required ordinary-time lower bound. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

theorem metricDefectHeatCorrection_differentiableAt_pos
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L)
    (x : Pt X) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (metricDefectHeatCorrection X h μ hμ O hO L x) s := by
  have hT : 0 < s+1 := by linarith
  exact ((metricDefectHeatCorrection_hasDerivWithinAt X o h U P ρ hf u hu hT μ hμ O hO hL x
    ⟨hs.le,by linarith⟩).hasDerivAt (Icc_mem_nhds hs (by linarith))).differentiableAt

theorem metricDefectDyadicCorrection_time_lower_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Ioc 0 T → ∀ x,
      metricDefectDyadicCorrection X h μ hμ O hO u x s/s-C*u x ≤
        deriv (metricDefectDyadicCorrection X h μ hμ O hO u x) s := by
  obtain ⟨D,hD,hDist⟩ := controlledExhaustion_distance_le X o u hu
  obtain ⟨K,hK,hLower⟩ := metricDefectHeatCorrection_time_lower_bound X o h U P ρ hf u hu hT
    (2*D) (by positivity)
  refine ⟨2*K,by positivity,fun μ hμ O hO s hs x => ?_⟩
  let F : ℕ → Pt X → ℝ → ℝ := fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)
  let c : ℕ → ℝ := fun j => dyadicPartition j (u x)
  obtain ⟨N,hPartition,hSum⟩ := dyadicGluing_finite_partition u F x (hu.2.2.1 x)
  have hDiff (j : ℕ) : DifferentiableAt ℝ (F j x) s :=
    metricDefectHeatCorrection_differentiableAt_pos X o h U P ρ hf u hu μ hμ O hO (by positivity) x hs.1
  have hDeriv : deriv (dyadicGluing u F x) s=∑ j ∈ Finset.range (N+1),c j*deriv (F j x) s := by
    rw [show dyadicGluing u F x=(fun t => ∑ j ∈ Finset.range (N+1),c j*F j x t) from funext hSum]
    rw [deriv_fun_sum (fun j _ => (hDiff j).const_mul (c j))]
    exact Finset.sum_congr rfl (fun j _ => deriv_const_mul_field (c j))
  have hc (j : ℕ) : 0 ≤ c j := dyadicPartition_nonnegative j (zero_le_one.trans (hu.2.2.1 x))
  have hError : (∑ j ∈ Finset.range (N+1),c j*(K*(2:ℝ)^j)) ≤ 2*K*u x := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N+1),c j*(2*K*u x) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hZero : c j=0
        · rw [hZero,zero_mul,zero_mul]
        have hScale := (dyadicPartition_scale_support (hu.2.2.1 x) j hZero).1
        apply mul_le_mul_of_nonneg_left _ (hc j)
        nlinarith
      _ = _ := by
        rw [← Finset.sum_mul]
        change (∑ j ∈ Finset.range (N+1),dyadicPartition j (u x))*(2*K*u x)=_
        rw [hPartition,one_mul]
  have hSumLower : (∑ j ∈ Finset.range (N+1),c j*(F j x s/s-K*(2:ℝ)^j)) ≤
      ∑ j ∈ Finset.range (N+1),c j*deriv (F j x) s := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hZero : c j=0
    · rw [hZero,zero_mul,zero_mul]
    have hScale := (dyadicPartition_scale_support (hu.2.2.1 x) j hZero).2
    have hNear : inducedDistance X.metric.form o x ≤ (2*D)*(2:ℝ)^j := by
      have hh := hDist x
      nlinarith
    exact mul_le_mul_of_nonneg_left (hLower μ hμ O hO s hs ((2:ℝ)^j)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) x hNear) (hc j)
  have hId : (∑ j ∈ Finset.range (N+1),c j*(F j x s/s-K*(2:ℝ)^j))=
      dyadicGluing u F x s/s-∑ j ∈ Finset.range (N+1),c j*(K*(2:ℝ)^j) := by
    rw [hSum s]
    simp only [mul_sub,Finset.sum_sub_distrib,mul_div_assoc,Finset.sum_div,c]
  rw [hId] at hSumLower
  change dyadicGluing u F x s/s-(2*K)*u x ≤ deriv (dyadicGluing u F x) s
  rw [hDeriv]
  nlinarith

end Yau.Proofs.F03Aux
