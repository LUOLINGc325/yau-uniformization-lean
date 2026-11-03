import Yau.Proofs.P06HodgeSpectralBounds

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- Actual iterates of the original geometric Hodge expression. -/
def compactHodgeIterate (g : SmoothMetric M) (A : RealForm M k) : ℕ → RealForm M k
  | 0 => A
  | j + 1 => hodgeRealForm g.form k (compactHodgeIterate g A j)

theorem compactHodgeIterate_smooth_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    SmoothRealForm (compactHodgeIterate g A j) ∧
      CompactlySupportedRealForm (compactHodgeIterate g A j) := by
  induction j with
  | zero => exact ⟨hA, hcA⟩
  | succ j ih =>
    exact ⟨hodgeRealForm_smooth g μ hμ _ ih.1,
      hodgeRealForm_compactlySupported g μ hμ _ ih.1 ih.2⟩

theorem compactHodgeIterate_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    L2RealForm g.form μ (compactHodgeIterate g A j) :=
  smooth_compactlySupported_l2RealForm g μ hμ _
    (compactHodgeIterate_smooth_compact g μ hμ A hA hcA j).1
    (compactHodgeIterate_smooth_compact g μ hμ A hA hcA j).2

def compactHodgeIterateHilbert (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    L2FormHilbert g μ k :=
  realizeActualForm g μ (compactHodgeIterate g A j) (compactHodgeIterate_l2 g μ hμ A hA hcA j)

theorem compactHodgeIterateHilbert_core_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    (compactHodgeIterateHilbert g μ hμ A hA hcA j,
      compactHodgeIterateHilbert g μ hμ A hA hcA (j + 1)) ∈
        (hodgeCoreOperator g μ hμ k).graph := by
  rw [hodgeCoreOperator_graph]
  change _ ∈ hodgeCoreRealizedGraph g μ k
  have hj := compactHodgeIterate_smooth_compact g μ hμ A hA hcA j
  refine ⟨compactHodgeIterate g A j, hodgeRealForm g.form k (compactHodgeIterate g A j),
    hodgeRealForm_corePair g μ hμ _ hj.1 hj.2, rfl⟩

theorem compactHodgeIterateHilbert_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    (compactHodgeIterateHilbert g μ hμ A hA hcA j,
      compactHodgeIterateHilbert g μ hμ A hA hcA (j + 1)) ∈
        (hodgeCoreOperator g μ hμ k).closure.graph :=
  LinearPMap.le_graph_of_le (hodgeCoreOperator g μ hμ k).le_closure
    (compactHodgeIterateHilbert_core_graph g μ hμ A hA hcA j)

/-- Every true geometric Hodge iterate of a compact smooth initial form
has strong initial convergence under the same constructed heat family. -/
theorem compactHodgeHeat_initial (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (j : ℕ) :
    Tendsto (fun t : ℝ => hodgeHeatHilbert g μ hμ k t
      (compactHodgeIterateHilbert g μ hμ A hA hcA j) -
        compactHodgeIterateHilbert g μ hμ A hA hcA j) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  simpa only [sub_self] using
    (hodgeHeatHilbert_tendsto_zero g μ hμ k (compactHodgeIterateHilbert g μ hμ A hA hcA j)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => compactHodgeIterateHilbert g μ hμ A hA hcA j)
        (𝓝[≥] (0 : ℝ)) (𝓝 (compactHodgeIterateHilbert g μ hμ A hA hcA j)))

theorem compactHodgeHeat_initial_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (t : ℝ) (j : ℕ) :
    (hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA j) -
        compactHodgeIterateHilbert g μ hμ A hA hcA j,
      hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA (j + 1)) -
        compactHodgeIterateHilbert g μ hμ A hA hcA (j + 1)) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph := by
  have hg := compactHodgeIterateHilbert_graph g μ hμ A hA hcA j
  exact (hodgeCoreOperator g μ hμ k).closure.graph.sub_mem
    (hodgeHeatHilbert_graph g μ hμ k t hg) hg

end Yau.NodeProofs.P06Aux
