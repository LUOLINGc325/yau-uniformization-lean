import Yau.LeafProofs.L17PartitionInverseJets

/-! All finite jets of the actual normalized partition are uniform at unit scale. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

abbrev PartitionWeightIndex (A : BoundedChartFamily g) (N : ℕ) :=
  Σ P : PartitionBudgetFamily A N, P.val.centers × M.Carrier

def partitionScaledNumerator (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionWeightIndex A N) (z : ComplexVector n) : ℝ :=
  chartWeight (i.1.val.charts.chart i.2.1) i.1.val.radius i.1.val.radius_pos
    (i.1.val.charts.chart i.2.2 (i.1.val.radius • z))

def partitionScaledWeight (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionWeightIndex A N) (z : ComplexVector n) : ℝ :=
  i.1.val.weight i.2.1 (i.1.val.charts.chart i.2.2 (i.1.val.radius • z))

theorem partitionScaledWeight_eq_mul (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionWeightIndex A N) (z : ComplexVector n) :
    partitionScaledWeight A N i z = partitionScaledNumerator A N i z *
      (partitionScaledSum A N (i.1, i.2.2) z)⁻¹ := by
  exact div_eq_mul_inv _ _

theorem partitionScaledNumerator_smooth (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionWeightIndex A N) :
    ContDiffOn ℝ ∞ (partitionScaledNumerator A N i) (ball (0 : ComplexVector n) 2) :=
  smoothFn_comp_scaledChart_contDiffOn i.1.val.charts
    (i.1.val.charts.chartWeight_properties i.2.1 i.1.val.radius_pos i.1.val.radius_lt).2.1
    i.1.val.radius_pos (by simpa only [i.1.property.1] using i.1.property.2.2.1) i.2.2

theorem partitionScaledWeight_smooth (A : BoundedChartFamily g) (N : ℕ)
    (i : PartitionWeightIndex A N) :
    ContDiffOn ℝ ∞ (partitionScaledWeight A N i) (ball (0 : ComplexVector n) 2) :=
  smoothFn_comp_scaledChart_contDiffOn i.1.val.charts (i.1.val.weight_smooth i.2.1)
    i.1.val.radius_pos (by simpa only [i.1.property.1] using i.1.property.2.2.1) i.2.2

theorem partitionScaledNumerator_uniformJetBounds (A : BoundedChartFamily g) (N k : ℕ) :
    UniformJetBounds k (partitionScaledNumerator A N) (fun _ => ball (0 : ComplexVector n) 2) := by
  apply UniformJetBounds.of_orderBounds
  intro j hj
  obtain ⟨C, _, hc⟩ := A.scaled_chartWeight_jet_bound j
  refine ⟨C, ?_⟩
  intro i z hz
  change ‖iteratedFDeriv ℝ j (fun w => chartWeight (i.1.val.charts.chart i.2.1)
    i.1.val.radius i.1.val.radius_pos
      (i.1.val.charts.chart i.2.2 (i.1.val.radius • w))) z‖ ≤ C
  simpa only [i.1.property.1] using
    hc i.1.val.radius i.1.val.radius_pos i.1.property.2.1 i.1.property.2.2.1 i.2.1 i.2.2 z hz

theorem partitionScaledWeight_uniformJetBounds (A : BoundedChartFamily g) (N k : ℕ) :
    UniformJetBounds k (partitionScaledWeight A N) (fun _ => ball (0 : ComplexVector n) 2) := by
  let r : PartitionWeightIndex A N → PartitionBudgetIndex A N := fun i => (i.1, i.2.2)
  have hi := (partitionScaledSum_inverse_uniformJetBounds A N k).reindex r
  have his (i : PartitionWeightIndex A N) := partitionScaledSum_inverse_smooth A N (r i)
  have hprod := (partitionScaledNumerator_uniformJetBounds A N k).bilinear hi
    (fun _ => isOpen_ball) (partitionScaledNumerator_smooth A N) his (ContinuousLinearMap.mul ℝ ℝ)
  apply hprod.congr (fun _ => isOpen_ball)
  intro i z hz
  exact (partitionScaledWeight_eq_mul A N i z).symm

end Yau.LeafProofs.L17Aux
