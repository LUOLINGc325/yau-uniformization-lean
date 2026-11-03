import Yau.LeafProofs.L17LocalizedGaussian

/-! One partition works for every exponent in (0,1); all Gaussian budgets
are selected before the spatial radius and the final time. -/

open Set Metric
noncomputable section

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_local_gaussian
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ C : ℝ, ∃ K : Ioo (0 : ℝ) 1 → ℝ,
      (∀ k, 0 < B k) ∧ 0 < C ∧ (∀ γ, 0 < K γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ 2 * P.radius < A.radius ∧
        P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2 * P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k * (P.radius⁻¹) ^ k) ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ P.radius ^ 2 → ∀ γ : Ioo (0 : ℝ) 1,
          ∀ (f : HolderSpace P T γ.val) (p : P.centers),
            HolderBound γ.val Set.univ (rescaledSource P T hT.le f p) (C * ‖f‖) ∧
            SchauderBound γ.val (cylinder Set.univ 0 (T / P.radius ^ 2))
              (P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p)) (K γ * ‖f‖) ∧
            (∀ q ∈ cylinder Set.univ 0 (T / P.radius ^ 2),
              ‖spatialDD (P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p)) q‖ ≤
                K γ * ‖f‖ * (T / P.radius ^ 2) ^ (γ.val / 2)) ∧
            HolderBound γ.val (cylinder Set.univ 0 (T / P.radius ^ 2))
              (fun q => (P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p) q,
                spatialD (P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p)) q))
              (K γ * ‖f‖ * ((T / P.radius ^ 2) ^ (1 / 2 : ℝ) +
                (T / P.radius ^ 2) ^ ((1 - γ.val) / 2))) ∧
            ∀ q ∈ cylinder Set.univ 0 T,
              linearOp (cylinder Set.univ 0 T)
                (fun _ => scalarSymbol (pullbackMatrix g (P.charts.chart p) 0)) (fun _ _ => 0)
                (localGaussian P T hT.le f p) q = localizedSource P T hT.le f p q := by
  choose H hH hHeat using fun γ : Ioo (0 : ℝ) 1 =>
    A.frozenHeatDuhamel_controlled_bounds γ.property.1 γ.property.2
  obtain ⟨N, B, C, hB, hC, hPart⟩ :=
    L17SourceLocalizationAux.BoundedChartFamily.exists_uniform_source_localization A hg
  refine ⟨N, B, C, fun γ => H γ * C, hB, hC, fun γ => mul_pos (hH γ) hC, ?_⟩
  intro ε hε
  obtain ⟨P, hA, hρε, hρ1, hρA, hN, hJets, hSource⟩ := hPart ε hε
  refine ⟨P, hA, hρε, hρ1, hρA, hN, hJets, ?_⟩
  intro T hT hTR γ f p
  obtain ⟨_, _, _, _, _, _, _, _, hf⟩ :=
    hSource T hT hTR γ.val γ.property.1 γ.property.2.le f p
  have hS : 0 < T / P.radius ^ 2 := div_pos hT (sq_pos_of_pos P.radius_pos)
  have hSone : T / P.radius ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos P.radius_pos)).mpr hTR
  have hBounds := hHeat γ p (T / P.radius ^ 2) (C * ‖f‖) hS hSone
    (rescaledSource P T hT.le f p) (L16Aux.holderBound_mono hf (subset_univ _))
  refine ⟨hf, ?_, ?_, ?_, ?_⟩
  · simpa only [hA, mul_assoc] using hBounds.1
  · simpa only [hA, mul_assoc] using hBounds.2.1
  · simpa only [hA, mul_assoc] using hBounds.2.2
  · intro q hq
    exact localGaussian_equation P T hT hTR γ.property.1 γ.property.2 f p hf hq

end Yau.LeafProofs.L17Aux
