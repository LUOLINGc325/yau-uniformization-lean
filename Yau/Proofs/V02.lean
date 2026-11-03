import Yau.Proofs.V02DeformationRealization
import Yau.Proofs.V02MixedTestLoss
import Yau.Proofs.V02InteriorCompact

/-! The original V02 estimates and actual uniform holomorphic realization.
Only the original incoming D02 compactness node remains a parameter here. -/

open scoped Manifold Topology ContDiff Matrix
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem deformationEstimate_of_originalD02 (hD02 : DiscCompactness X)
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) :
    DeformationEstimate d j a := by
  intro L hL
  obtain ⟨C, hC, hLossAll⟩ := exists_mixed_test_loss_coefficient hd j a ha L hL
  refine ⟨C, hC, fun φ hφ => ?_⟩
  have hdφ := variationSetup_update_test hd φ hφ
  obtain ⟨Mφ, hMφ, hLoss⟩ := hLossAll φ hφ
  intro ε hε E₀ D₀ F E l hmin hCenters hdata
  obtain ⟨Kc, hKc, hKcC, hcenter⟩ := hCenters
  obtain ⟨K, hK, hFK⟩ := interiorCompact_of_originalD02 hD02 hdφ j E₀ F
    (fun ν => ⟨hmin.1 ν, (hdata ν).1⟩)
  change SeqUpperZero (fun ν =>
    outerCenter d j a (F ν) ^ 2 *
      quadValue (centerTestHessian {d with test := φ} (F ν) (E ν)) (l ν 0) -
      circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (l ν (circlePoint θ))) -
      C * ε * (1 + (variationEnergy d j (F ν)).toReal +
        (boundaryDSq (fun θ => l ν (circlePoint θ))).toReal))
  apply seqUpperZero_of_three_limits hMφ (minimizingSequence_gap_tendsto hdφ hε.le hmin)
  intro η hη
  have hfull : ∀ ν, AdmissibleVariationDisc {d with test := φ} j (F ν) ∧
      (variationEnergy {d with test := φ} j (F ν)).toReal ≤ E₀ ∧
      (∀ ζ ∈ closedBall (0 : ℂ) 1, (F ν).f ζ ∈ K) ∧
      InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc ∧
      NormalizedDiscFrame d.G (F ν).f (E ν) ∧ HolomorphicColumn (l ν) ∧
      (∀ ζ ∈ closedBall (0 : ℂ) 1, ∑ i, ‖l ν ζ i‖ ^ 2 ≤ L ^ 2) ∧
      boundaryDSq (fun θ => l ν (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2) := by
    intro ν
    exact ⟨hmin.1 ν, (hdata ν).1, hFK ν, hcenter ν,
      (hdata ν).2.1, (hdata ν).2.2.1, (hdata ν).2.2.2.1, (hdata ν).2.2.2.2⟩
  obtain ⟨r, M, hr, hM, h, α, fz, hall⟩ :=
    exists_uniform_native_deformations hdφ j a ha L E₀ D₀ ε η hL hη F E l K Kc hK hKc hKcC hfull
  refine ⟨r, M / 2, hr, div_nonneg hM (by norm_num), fun ρ hρ hρr ν => ?_⟩
  have hR := (hall ν).1
  have hJ := (hall ν).2.2.2.2.2.1
  have hD := (hall ν).2.2.2.2.2.2
  have hTaylor := parameterCircleTaylor hJ hD hρ hρr
  have hmap (θ : ℝ) : (ρ : ℂ) * circlePoint θ ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ, circlePoint_norm, mul_one] using hρr
  have hcont : Continuous (fun θ => penalizedFunctional {d with test := φ} j ε
      {(F ν) with f := fz ν ((ρ : ℂ) * circlePoint θ)}) :=
    hJ.continuousOn.comp_continuous (continuous_const.mul circlePoint_contDiff.continuous) hmap
  have hnegative := realized_negative_mixed_le_gap hdφ hε.le hR hρ hρr hcont hTaylor
  have hloss := hLoss (F ν) (E ν) (l ν) (h ν) (α ν) (fz ν) r ε η
    (hmin.1 ν) (hdata ν).2.1 (hdata ν).2.2.1 (hdata ν).2.2.2.1 hR
    (hall ν).2.1 (hall ν).2.2.1 (hall ν).2.2.2.1 (hall ν).2.2.2.2.1 hε.le
  exact hloss.trans (add_le_add hnegative (le_refl (Mφ * η)))

theorem V02_of_originalD02 (hD02 : DiscCompactness X) : V02Contract X := by
  intro q d hd
  refine ⟨4, le_rfl, fun a ha => Filter.Eventually.of_forall fun j => ?_⟩
  exact ⟨deformationEstimate_of_originalD02 hD02 hd j a ha, deformationRealization hd j a ha⟩

end Yau.Blueprint.V02Proof
