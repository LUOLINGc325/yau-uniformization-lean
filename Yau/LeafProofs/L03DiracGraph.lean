import Yau.LeafProofs.L03DiracLocalApprox

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Finite product of the actual degreewise metric L² completions. -/
abbrev L2GradedProduct (g : SmoothMetric M) (μ : Measure M.Carrier) :=
  (i : Fin (2 * n + 1)) → L2FormHilbert g μ i.val

def realizeGradedForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A) :
    L2GradedProduct g μ :=
  fun i => realizeL2Form g μ (L2FormSpace.ofSection (A i.val) (hA.2 i.val))

/-- The original graded distance gives precisely the product topology of
all the actual metric L² realizations. -/
theorem tendsto_realizeGradedForm_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As : ℕ → OperatorCandidates.GradedRealForm M) (A : OperatorCandidates.GradedRealForm M)
    (hAs : ∀ j, OperatorCandidates.GradedL2 g.form μ (As j))
    (hA : OperatorCandidates.GradedL2 g.form μ A) :
    Tendsto (fun j => realizeGradedForm g μ (As j) (hAs j)) atTop
      (𝓝 (realizeGradedForm g μ A hA)) ↔
    Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
  constructor
  · intro ht
    have hi (i : Fin (2 * n + 1)) :
        Tendsto (fun j => formL2DistanceSq g.form μ (As j i.val) (A i.val)) atTop (𝓝 0) := by
      have hp := (tendsto_pi_nhds.mp ht) i
      exact (tendsto_realizeL2Form_iff g μ
        (fun j => L2FormSpace.ofSection (As j i.val) ((hAs j).2 i.val))
        (L2FormSpace.ofSection (A i.val) (hA.2 i.val))).mp hp
    simpa only [OperatorCandidates.gradedDistanceSq, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hi i)
  · intro ht
    apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_realizeL2Form_iff g μ
      (fun j => L2FormSpace.ofSection (As j i.val) ((hAs j).2 i.val))
      (L2FormSpace.ofSection (A i.val) (hA.2 i.val))).mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro j
    change formL2DistanceSq g.form μ (As j i.val) (A i.val) ≤
      ∑ i : Fin (2 * n + 1), formL2DistanceSq g.form μ (As j i.val) (A i.val)
    exact Finset.single_le_sum (fun i _ =>
      (show (0 : ENNReal) ≤ formL2DistanceSq g.form μ (As j i.val) (A i.val) from bot_le))
      (Finset.mem_univ i)

/-- The actual compact smooth Dirac core, in the product of the genuine
metric L² completions, with both entries tied to the same computed operator. -/
def diracCoreRealizedGraph (g : SmoothMetric M) (μ : Measure M.Carrier) :
    Set (L2GradedProduct g μ × L2GradedProduct g μ) :=
  {p | ∃ (A W : OperatorCandidates.GradedRealForm M)
    (hc : OperatorCandidates.DiracCorePair g.form μ A W),
    p = (realizeGradedForm g μ A hc.1, realizeGradedForm g μ W hc.2.1)}

/-- The exact original sequence definition of the minimal Dirac graph is
closure of the exact realized compact smooth graph. -/
theorem diracMinimalGraph_iff_core_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W ↔
      (realizeGradedForm g μ A hA, realizeGradedForm g μ W hW) ∈
        closure (diracCoreRealizedGraph g μ) := by
  classical
  constructor
  · rintro ⟨_, _, As, Ws, hc, ht⟩
    have htA : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_right (by positivity))
    have htW : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (Ws j) W) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_left (by positivity))
    have hu := (tendsto_realizeGradedForm_iff g μ As A (fun j => (hc j).1) hA).mpr htA
    have hw := (tendsto_realizeGradedForm_iff g μ Ws W (fun j => (hc j).2.1) hW).mpr htW
    exact mem_closure_of_tendsto (hu.prodMk_nhds hw)
      (Filter.Eventually.of_forall fun j => ⟨As j, Ws j, hc j, rfl⟩)
  · intro hp
    obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hp
    choose As Ws hc heq using hp
    have hu : Tendsto (fun j => realizeGradedForm g μ (As j) (hc j).1) atTop
        (𝓝 (realizeGradedForm g μ A hA)) := by
      have hf := (continuous_fst.tendsto
        (realizeGradedForm g μ A hA, realizeGradedForm g μ W hW)).comp ht
      convert hf using 1
      funext j
      exact (congrArg Prod.fst (heq j)).symm
    have hw : Tendsto (fun j => realizeGradedForm g μ (Ws j) (hc j).2.1) atTop
        (𝓝 (realizeGradedForm g μ W hW)) := by
      have hf := (continuous_snd.tendsto
        (realizeGradedForm g μ A hA, realizeGradedForm g μ W hW)).comp ht
      convert hf using 1
      funext j
      exact (congrArg Prod.snd (heq j)).symm
    have htA := (tendsto_realizeGradedForm_iff g μ As A (fun j => (hc j).1) hA).mp hu
    have htW := (tendsto_realizeGradedForm_iff g μ Ws W (fun j => (hc j).2.1) hW).mp hw
    exact ⟨hA, hW, As, Ws, hc, by simpa only [zero_add] using htA.add htW⟩

/-- Strong convergence of both entries preserves membership in the original
minimal Dirac graph. This is closedness, with no additional analytic premise. -/
theorem diracMinimalGraph_of_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As Ws : ℕ → OperatorCandidates.GradedRealForm M)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmin : ∀ j, OperatorCandidates.DiracMinimalGraph g.form μ (As j) (Ws j))
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (htA : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0))
    (htW : Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (Ws j) W) atTop (𝓝 0)) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  apply (diracMinimalGraph_iff_core_closure g μ A W hA hW).mpr
  have hu := (tendsto_realizeGradedForm_iff g μ As A (fun j => (hmin j).1) hA).mpr htA
  have hw := (tendsto_realizeGradedForm_iff g μ Ws W (fun j => (hmin j).2.1) hW).mpr htW
  exact isClosed_closure.mem_of_tendsto (hu.prodMk_nhds hw)
    (Filter.Eventually.of_forall fun j =>
      (diracMinimalGraph_iff_core_closure g μ (As j) (Ws j) (hmin j).1 (hmin j).2.1).mp (hmin j))

end Yau.LeafProofs.L03
