import Yau.LeafProofs.L17UnitGaussianResidual

/-! Geometry alone chooses one atlas and all small local Gaussian residual budgets. -/

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_gaussian_residual
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ C : ℝ, ∃ K R : Ioo (0 : ℝ) 1 → ℝ,
      (∀ k, 0 < B k) ∧ 0 < C ∧ (∀ γ, 0 < K γ) ∧ (∀ γ, 0 < R γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ 2 * P.radius < A.radius ∧
        P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2 * P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k) ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ P.radius ^ 2 → ∀ γ : Ioo (0 : ℝ) 1,
          ∀ (f : HolderSpace P T γ.val) (p : P.centers),
            let S := T/P.radius^2
            let v := P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p)
            let s := S^(1/2 : ℝ)+S^((1-γ.val)/2)
            HolderBound γ.val Set.univ (rescaledSource P T hT.le f p) (C*‖f‖) ∧
            SchauderBound γ.val (cylinder Set.univ 0 S) v (K γ*‖f‖) ∧
            (∀ q ∈ cylinder Set.univ 0 S, ‖spatialDD v q‖ ≤ K γ*‖f‖*S^(γ.val/2)) ∧
            HolderBound γ.val (cylinder Set.univ 0 S) (fun q => (v q,spatialD v q)) (K γ*‖f‖*s) ∧
            HolderBound γ.val (cylinder (ball (0 : Space n) 2) 0 S)
              (unitGaussianResidual P T hT.le f p) (R γ*‖f‖*(P.radius+s)) := by
  obtain ⟨N,B,C,K,hB,hC,hK,hPart⟩ := A.exists_uniform_local_gaussian hg
  let R : Ioo (0 : ℝ) 1 → ℝ := fun γ => unitGaussianResidualBudget A B γ.val (K γ)
  have hR : ∀ γ, 0 < R γ := fun γ =>
    unitGaussianResidualBudget_pos A B (fun k => (hB k).le) γ.val (hK γ).le
  refine ⟨N,B,C,K,R,hB,hC,hK,hR,?_⟩
  intro ε hε
  obtain ⟨P,hA,hρε,hρ1,hρA,hN,hJets,hG⟩ := hPart ε hε
  refine ⟨P,hA,hρε,hρ1,hρA,hN,hJets,?_⟩
  intro T hT hTR γ f p
  obtain ⟨hf,hSch,hHess,hLow,_⟩ := hG T hT hTR γ f p
  refine ⟨hf,hSch,hHess,hLow,?_⟩
  have hs : 0 ≤ (T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ.val)/2) :=
    add_nonneg (Real.rpow_nonneg (le_of_lt (div_pos hT (sq_pos_of_pos P.radius_pos))) _)
      (Real.rpow_nonneg (le_of_lt (div_pos hT (sq_pos_of_pos P.radius_pos))) _)
  have h := unitGaussianResidual_small_bound P T hT.le (by simpa only [hA] using hρA) hρ1
    γ.property.2.le (hK γ).le hs B (fun k => (hB k).le) f p
    (fun k z hz => (hJets k p p z hz).2) hSch hLow
  simpa only [R,hA] using h

end Yau.LeafProofs.L17Aux
