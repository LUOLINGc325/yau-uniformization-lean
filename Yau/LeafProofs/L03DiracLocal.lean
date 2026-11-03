import Yau.LeafProofs.L03DiracChart
import Mathlib.Analysis.Calculus.BumpFunction.Normed

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Actual model graph convergence on one fixed compact chart set gives
convergence in the exact original manifold Dirac graph. -/
theorem diracMinimalGraph_of_compact_chart_approximants (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j))
    (hcW : ∀ j, CompactlySupportedRealForm (W j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKO : K ⊆ chartTarget x)
    (hAK : tsupport (modelGradedChartPullbackZero A x) ⊆ K)
    (hWK : tsupport (modelGradedChartPullbackZero W x) ⊆ K)
    (G : ℕ → ComplexVector n → modelGradedFiber n)
    (hG : ∀ j, ContDiff ℝ ∞ (G j)) (hGK : ∀ j, tsupport (G j) ⊆ K)
    (htA : Tendsto (fun j => ∫ z, ‖G j z - modelGradedChartPullbackZero A x z‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0))
    (htW : Tendsto (fun j => ∫ z,
      ‖modelDiracJetCLM g.form x z (G j z, fderiv ℝ (G j) z) -
        modelGradedChartPullbackZero W x z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  let As := fun j => modelGradedChartPushforward x (G j)
  let Ws := fun j => diracRealForm g.form (As j)
  let H := fun j z => modelDiracJetCLM g.form x z (G j z, fderiv ℝ (G j) z)
  have hcG (j : ℕ) : HasCompactSupport (G j) :=
    hcK.of_isClosed_subset (isClosed_tsupport _) (hGK j)
  have hGO (j : ℕ) : tsupport (G j) ⊆ chartTarget x := (hGK j).trans hKO
  have hH (j : ℕ) := modelDiracJetCLM_compact_apply_properties g x (G j) (hG j) (hcG j) (hGO j)
  have hWs (j : ℕ) : Ws j = modelGradedChartPushforward x (H j) :=
    modelGradedChartPushforward_dirac_eq g μ hμ x (G j) (hG j) (hcG j) (hGO j)
  obtain ⟨CA, hCA, hBA⟩ := modelGradedChartPushforward_l2_distance_bound g μ hμ A hA hcA x hAx hcK hKO hAK
  obtain ⟨CW, hCW, hBW⟩ := modelGradedChartPushforward_l2_distance_bound g μ hμ W hW hcW x hWx hcK hKO hWK
  have hlimA : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
    have hupper : Tendsto (fun j => ENNReal.ofReal
        (CA * ∫ z, ‖G j z - modelGradedChartPullbackZero A x z‖ ^ 2 ∂lebesgueC n)) atTop (𝓝 0) := by
      simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (htA.const_mul CA)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => bot_le) (fun j => hBA (G j) (hG j) (hGK j))
  have hlimW : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (Ws j) W) atTop (𝓝 0) := by
    have hupper : Tendsto (fun j => ENNReal.ofReal
        (CW * ∫ z, ‖H j z - modelGradedChartPullbackZero W x z‖ ^ 2 ∂lebesgueC n)) atTop (𝓝 0) := by
      simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (htW.const_mul CW)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => bot_le)
    intro j
    change OperatorCandidates.gradedDistanceSq g.form μ (Ws j) W ≤ _
    rw [hWs j]
    exact hBW (H j) (hH j).1 ((hH j).2.2.trans (hGK j))
  refine ⟨hA, hW, As, Ws, ?_, ?_⟩
  · intro j
    exact modelGradedChartPushforward_corePair g μ hμ x (G j) (hG j) (hcG j) (hGO j)
  · simpa only [zero_add] using hlimA.add hlimW

/-- The standard Euclidean chart space has an internal smooth normalized
nonnegative compact mollifier, including in real dimension zero. -/
theorem exists_model_friedrichs_mollifier (n : ℕ) :
    ∃ ρ : ComplexVector n → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ z, 0 ≤ ρ z) ∧ (∫ z, ρ z ∂lebesgueC n) = 1 := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let f : ContDiffBump (0 : ComplexVector n) := default
  exact ⟨f.normed (lebesgueC n), f.contDiff_normed, f.hasCompactSupport_normed,
    f.nonneg_normed, f.integral_normed⟩

end Yau.LeafProofs.L03
