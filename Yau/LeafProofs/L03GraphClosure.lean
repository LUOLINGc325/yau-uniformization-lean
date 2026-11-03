import Yau.LeafProofs.L03

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- Convergence in the exact frozen L² distance preserves every integrated
metric pairing against a fixed L² form. -/
theorem formL2DistanceSq_tendsto_integral_pairing (g : SmoothMetric M)
    (μ : Measure M.Carrier) (A : ℕ → RealForm M k) (B Z : RealForm M k)
    (hA : ∀ j, L2RealForm g.form μ (A j)) (hB : L2RealForm g.form μ B)
    (hZ : L2RealForm g.form μ Z)
    (ht : Tendsto (fun j => formL2DistanceSq g.form μ (A j) B) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y, formInner g.form (A j) Z y ∂μ) atTop
      (𝓝 (∫ y, formInner g.form B Z y ∂μ)) := by
  let u : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (A j) (hA j)
  let v : L2FormSpace g μ k := L2FormSpace.ofSection B hB
  let z : L2FormSpace g μ k := L2FormSpace.ofSection Z hZ
  have hu : Tendsto (fun j => realizeL2Form g μ (u j)) atTop (𝓝 (realizeL2Form g μ v)) :=
    (tendsto_realizeL2Form_iff g μ u v).mpr (by
      simpa only [u, v, L2FormSpace.toSection_ofSection] using ht)
  have hh : Tendsto (fun j => inner ℝ (realizeL2Form g μ (u j)) (realizeL2Form g μ z))
      atTop (𝓝 (inner ℝ (realizeL2Form g μ v) (realizeL2Form g μ z))) :=
    hu.inner tendsto_const_nhds
  simpa only [realizeL2Form_inner, u, v, z, L2FormSpace.toSection_ofSection] using hh

/-- Finite graded graph convergence preserves pairing against every fixed
actual graded L² test section. -/
theorem gradedDistanceSq_tendsto_integral_pairing (g : SmoothMetric M)
    (μ : Measure M.Carrier) (A : ℕ → OperatorCandidates.GradedRealForm M)
    (B Z : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, OperatorCandidates.GradedL2 g.form μ (A j))
    (hB : OperatorCandidates.GradedL2 g.form μ B)
    (hZ : OperatorCandidates.GradedL2 g.form μ Z)
    (ht : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (A j) B) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y, OperatorCandidates.gradedInner g.form (A j) Z y ∂μ) atTop
      (𝓝 (∫ y, OperatorCandidates.gradedInner g.form B Z y ∂μ)) := by
  have hk (i : Fin (2 * n + 1)) : Tendsto
      (fun j => formL2DistanceSq g.form μ (A j i.val) (B i.val)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le)
    intro j
    change formL2DistanceSq g.form μ (A j i.val) (B i.val) ≤
      ∑ i : Fin (2 * n + 1), formL2DistanceSq g.form μ (A j i.val) (B i.val)
    exact Finset.single_le_sum (fun i _ =>
      (show (0 : ENNReal) ≤ formL2DistanceSq g.form μ (A j i.val) (B i.val) from bot_le))
      (Finset.mem_univ i)
  have hh (i : Fin (2 * n + 1)) := formL2DistanceSq_tendsto_integral_pairing g μ
    (fun j => A j i.val) (B i.val) (Z i.val)
    (fun j => (hA j).2 i.val) (hB.2 i.val) (hZ.2 i.val) (hk i)
  have heq (F : OperatorCandidates.GradedRealForm M)
      (hF : OperatorCandidates.GradedL2 g.form μ F) :
      (∫ y, OperatorCandidates.gradedInner g.form F Z y ∂μ) =
        ∑ i : Fin (2 * n + 1), ∫ y, formInner g.form (F i.val) (Z i.val) y ∂μ := by
    change (∫ y, ∑ i : Fin (2 * n + 1), formInner g.form (F i.val) (Z i.val) y ∂μ) = _
    exact integral_finsetSum Finset.univ (fun i _ =>
      formInner_integrable g μ (F i.val) (Z i.val) (hF.2 i.val) (hZ.2 i.val))
  simpa only [heq _ hB] using (tendsto_finsetSum Finset.univ (fun i _ => hh i)).congr'
    (Filter.Eventually.of_forall fun j => (heq (A j) (hA j)).symm)

/-- The full original minimal Dirac graph is contained in the original
maximal graph, by core symmetry and continuity of actual L² pairings. -/
theorem diracMinimalGraph_implies_maximal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracMinimalGraph g.form μ A W) :
    OperatorCandidates.DiracMaximalGraph g.form μ A W := by
  obtain ⟨hA, hW, As, Ws, hc, ht⟩ := hAW
  refine ⟨hA, hW, ?_⟩
  intro B Z hBZ
  refine ⟨gradedInner_integrable g μ A Z hA hBZ.2.1,
    gradedInner_integrable g μ W B hW hBZ.1, ?_⟩
  have htA : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun _ => le_add_of_nonneg_right (by positivity))
  have htW : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (Ws j) W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun _ => le_add_of_nonneg_left (by positivity))
  have ha := gradedDistanceSq_tendsto_integral_pairing g μ As A Z
    (fun j => (hc j).1) hA hBZ.2.1 htA
  have hw := gradedDistanceSq_tendsto_integral_pairing g μ Ws W B
    (fun j => (hc j).2.1) hW hBZ.1 htW
  exact tendsto_nhds_unique ha (hw.congr' (Filter.Eventually.of_forall fun j =>
    (diracCorePair_symmetric g μ hμ (As j) (Ws j) B Z (hc j) hBZ).symm))

end Yau.LeafProofs.L03
