import spec.CHAIN.CONTRACTS

/-! Spectral choices vary with δ, while the displayed master discs and
frames remain unchanged. The coefficient is chosen before every disc. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_spectral_factors_for_master
    (d : VariationData X q) (a : ℕ) (hSpec : SpectralFactorEstimates d a)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (F : ℝ → ℕ → VariationDisc X)
    (E : ℝ → ℕ → ℂ → CotangentMatrix n)
    (hFrames : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν)) :
    ∃ (C : ℝ) (H Hinv : ℝ → ℕ → ℂ → CotangentMatrix n), 0 ≤ C ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
        ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν) ∧
          SpectralFactorFor d j a δ (F ε ν) (E ε ν) (H ε ν) (Hinv ε ν) ∧
          (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
            rectOpNorm (Hinv ε ν ζ) ≤ (Real.sqrt δ)⁻¹) ∧
          matrixDSq (fun θ => Hinv ε ν (circlePoint θ)) ≤
            ENNReal.ofReal C * (1 + variationEnergy d j (F ε ν)) := by
  classical
  obtain ⟨C, hC, hEvery⟩ := hSpec j δ hδ
  let Good (ε : ℝ) := MinimizingSequence d j ε (F ε) ∧
    ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν)
  have hchoice (ε : ℝ) (ν : ℕ) : ∃ H Hinv : ℂ → CotangentMatrix n,
      Good ε → SpectralFactorFor d j a δ (F ε ν) (E ε ν) H Hinv ∧
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
          rectOpNorm (Hinv ζ) ≤ (Real.sqrt δ)⁻¹) ∧
        matrixDSq (fun θ => Hinv (circlePoint θ)) ≤
          ENNReal.ofReal C * (1 + variationEnergy d j (F ε ν)) := by
    by_cases hGood : Good ε
    · obtain ⟨H, Hinv, hH⟩ := hEvery (F ε ν) (E ε ν) (hGood.1.1 ν) (hGood.2 ν)
      exact ⟨H, Hinv, fun _ => hH⟩
    · exact ⟨fun _ => 1, fun _ => 1, fun h => (hGood h).elim⟩
  choose H Hinv hH using hchoice
  refine ⟨C, H, Hinv, hC, ?_⟩
  filter_upwards [hFrames] with ε hε
  exact ⟨hε.1, fun ν => ⟨hε.2 ν, hH ε ν hε⟩⟩

end Yau.Blueprint.V01Proof
