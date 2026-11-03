import Yau.LeafProofs.L17NormalizedPartitionJets

/-! The original geometry supplies every partition jet budget before the small scale. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_partition_scaled_jet_budget
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ ε : ℝ, 0 < ε →
      ∃ P : UniformChartPartition g, P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧
        2 * P.radius < A.radius ∧ P.overlapBudget = N ∧
        ∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) 2 →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q (P.radius • w))) z‖ ≤ C k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q (P.radius • w))) z‖ ≤ C k := by
  classical
  obtain ⟨N, hN⟩ := A.exists_uniform_partition_budget hg
  choose B hB hb using fun k => partitionScaledWeight_uniformJetBounds A N k
  choose D hD hd using fun k => A.scaled_chartLocalization_jet_bound k
  refine ⟨N, (fun k => max (B k) (D k)), fun k =>
    (zero_lt_one.trans_le (hB k)).trans_le (le_max_left _ _), ?_⟩
  intro ε hε
  let δ := min ε (A.radius / 4)
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min hε (by have := A.radius_pos; positivity)
  obtain ⟨P, hA, hPδ, hρone, hbudget⟩ := hN δ hδ
  have hρε : P.radius < ε := hPδ.trans_le (min_le_left _ _)
  have hρr : 2 * P.radius < A.radius := by
    have hp := hPδ.trans_le (min_le_right _ _)
    nlinarith [A.radius_pos]
  refine ⟨P, hA, hρε, hρone, hρr, hbudget, ?_⟩
  intro k p q z hz
  let Q : PartitionBudgetFamily A N := ⟨P, hA, hρone, hρr, hbudget.le⟩
  let i : PartitionWeightIndex A N := ⟨Q, p, q⟩
  constructor
  · exact (hb k i z hz k le_rfl).trans (le_max_left _ _)
  · have hlocal := hd k P.radius P.radius_pos hρone hρr p q z hz
    simpa only [UniformChartPartition.localization, hA] using
      hlocal.trans (le_max_right (B k) (D k))

end Yau.LeafProofs.L17Aux
