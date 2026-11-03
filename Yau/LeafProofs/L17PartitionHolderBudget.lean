import Yau.LeafProofs.L17HolderOfDerivative
import Yau.LeafProofs.L17PartitionJetBounds

/-! Original geometric partition jets yield actual uniform Holder cutoff elements. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_partition_holder_budget
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ C : ℕ → ℝ, ∃ K : ℝ, (∀ k, 0 < C k) ∧ 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ 2 * P.radius < A.radius ∧
        P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2 * P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤
              C k * (P.radius⁻¹) ^ k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤
              C k * (P.radius⁻¹) ^ k) ∧
        ∀ T γ : ℝ, T ≤ P.radius ^ 2 → 0 ≤ γ → γ ≤ 1 → ∀ p : P.centers,
          ∃ η χ : HolderSpace P T γ,
            (∀ q, holderFun η q = P.weight p q.1) ∧
            (∀ q, holderFun χ q = P.localization p q.1) ∧ ‖η‖ ≤ K ∧ ‖χ‖ ≤ K := by
  obtain ⟨N, C, hC, hpart⟩ := A.exists_uniform_partition_jet_budget hg
  let K := max 1 (3 * C 1)
  refine ⟨N, C, K, hC, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro ε hε
  obtain ⟨P, hA, hρε, hρone, hρr, hN, hb⟩ := hpart ε hε
  refine ⟨P, hA, hρε, hρone, hρr, hN, hb, ?_⟩
  intro T γ hT hγ0 hγ1 p
  have hρtwo : P.radius ≤ 2 * P.radius := by have := P.radius_pos; linarith
  have hDη : ∀ q z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ C 1 / P.radius := by
    intro q z hz
    have h := (hb 1 p q z ((ball_subset_ball hρtwo) hz)).1
    simpa only [norm_iteratedFDeriv_one, pow_one, div_eq_mul_inv] using h
  have hDχ : ∀ q z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ C 1 / P.radius := by
    intro q z hz
    have h := (hb 1 p q z ((ball_subset_ball hρtwo) hz)).2
    simpa only [norm_iteratedFDeriv_one, pow_one, div_eq_mul_inv] using h
  have hη : ∀ x, |P.weight p x| ≤ 1 := fun x =>
    (abs_of_nonneg (P.weight_nonneg p x)).le.trans (P.weight_le_one p x)
  have hχ : ∀ x, |P.localization p x| ≤ 1 := by
    intro x
    have h := chartLocalization_mem_Icc (P.charts.chart p) P.radius_pos x
    exact (abs_of_nonneg h.1).le.trans h.2
  let η := timeIndependentOfDerivativeBound P hT hγ1 (hC 1).le
    (P.weight p) (P.weight_smooth p) hη hDη
  let χ := timeIndependentOfDerivativeBound P hT hγ1 (hC 1).le
    (P.localization p) (P.localization_smooth p) hχ hDχ
  have hpow : (3 : ℝ) ^ (1 - γ) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith : 1 - γ ≤ 1)
  have hnorm : max (1 : ℝ) ((3 : ℝ) ^ (1 - γ) * C 1) ≤ K :=
    max_le_max le_rfl (mul_le_mul_of_nonneg_right hpow (hC 1).le)
  exact ⟨η, χ, fun _ => rfl, fun _ => rfl,
    (timeIndependentOfDerivativeBound_norm_le P hT hγ1 zero_le_one (hC 1).le
      (P.weight p) (P.weight_smooth p) hη hDη).trans hnorm,
    (timeIndependentOfDerivativeBound_norm_le P hT hγ1 zero_le_one (hC 1).le
      (P.localization p) (P.localization_smooth p) hχ hDχ).trans hnorm⟩

end Yau.LeafProofs.L17HolderAux
