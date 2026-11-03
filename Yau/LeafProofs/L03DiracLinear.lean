import Yau.LeafProofs.L03DiracGraph

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Addition of actual graded L² sections is degreewise addition. -/
theorem gradedL2_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B) :
    OperatorCandidates.GradedL2 g.form μ (A + B) := by
  apply (gradedL2_iff g.form μ (A + B)).mpr
  intro j
  exact l2RealForm_add g μ (A j) (B j) (hA.2 j) (hB.2 j)

theorem diracRealForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (hB : ∀ j, SmoothRealForm (B j)) :
    diracRealForm g.form (A + B) = diracRealForm g.form A + diracRealForm g.form B := by
  funext j
  cases j with
  | zero => exact codifferentialRealForm_add g μ hμ (A 1) (B 1) (hA 1) (hB 1)
  | succ j =>
      change exteriorRealForm (A j + B j) + codifferentialRealForm g.form (A (j + 2) + B (j + 2)) =
        (exteriorRealForm (A j) + codifferentialRealForm g.form (A (j + 2))) +
        (exteriorRealForm (B j) + codifferentialRealForm g.form (B (j + 2)))
      rw [exteriorRealForm_add (A j) (B j) (hA j) (hB j),
        codifferentialRealForm_add g μ hμ (A (j + 2)) (B (j + 2)) (hA (j + 2)) (hB (j + 2))]
      abel

theorem diracCorePair_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W B Z : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracCorePair g.form μ A W)
    (hBZ : OperatorCandidates.DiracCorePair g.form μ B Z) :
    OperatorCandidates.DiracCorePair g.form μ (A + B) (W + Z) := by
  have hA (j : ℕ) : SmoothRealForm (A j) := (hAW.2.2.1 j).1
  have hB (j : ℕ) : SmoothRealForm (B j) := (hBZ.2.2.1 j).1
  have hc := diracRealForm_corePair g μ hμ (A + B)
    (fun j => smoothRealForm_add (A j) (B j) (hA j) (hB j))
    (fun j => compactlySupportedRealForm_add (A j) (B j) (hAW.2.2.1 j).2.1 (hBZ.2.2.1 j).2.1)
  have heq : W + Z = diracRealForm g.form (A + B) := by
    rw [diracCorePair_output_eq g μ hμ A W hAW, diracCorePair_output_eq g μ hμ B Z hBZ,
      diracRealForm_add g μ hμ A B hA hB]
  rwa [← heq] at hc

/-- Realization respects the actual sum of raw sections. Its membership
proofs do not change the realized value. -/
theorem realizeGradedForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B)
    (hAB : OperatorCandidates.GradedL2 g.form μ (A + B)) :
    realizeGradedForm g μ (A + B) hAB = realizeGradedForm g μ A hA + realizeGradedForm g μ B hB := by
  funext i
  exact UniformSpace.Completion.coe_add
    (L2FormSpace.ofSection (A i.val) (hA.2 i.val)) (L2FormSpace.ofSection (B i.val) (hB.2 i.val))

/-- Addition preserves the exact actual compact Dirac graph after
realization, before taking its closure. -/
theorem diracCoreRealizedGraph_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {p q : L2GradedProduct g μ × L2GradedProduct g μ}
    (hp : p ∈ diracCoreRealizedGraph g μ) (hq : q ∈ diracCoreRealizedGraph g μ) :
    p + q ∈ diracCoreRealizedGraph g μ := by
  obtain ⟨A, W, hAW, rfl⟩ := hp
  obtain ⟨B, Z, hBZ, rfl⟩ := hq
  have hc := diracCorePair_add g μ hμ A W B Z hAW hBZ
  refine ⟨A + B, W + Z, hc, ?_⟩
  rw [realizeGradedForm_add g μ A B hAW.1 hBZ.1 hc.1,
    realizeGradedForm_add g μ W Z hAW.2.1 hBZ.2.1 hc.2.1]
  rfl

/-- The exact original minimal graph is additive, by continuity of addition
on the closure of the actual compact smooth graph. -/
theorem diracMinimalGraph_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W B Z : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracMinimalGraph g.form μ A W)
    (hBZ : OperatorCandidates.DiracMinimalGraph g.form μ B Z) :
    OperatorCandidates.DiracMinimalGraph g.form μ (A + B) (W + Z) := by
  have hAB := gradedL2_add g μ A B hAW.1 hBZ.1
  have hWZ := gradedL2_add g μ W Z hAW.2.1 hBZ.2.1
  apply (diracMinimalGraph_iff_core_closure g μ (A + B) (W + Z) hAB hWZ).mpr
  rw [realizeGradedForm_add g μ A B hAW.1 hBZ.1 hAB,
    realizeGradedForm_add g μ W Z hAW.2.1 hBZ.2.1 hWZ]
  change (realizeGradedForm g μ A hAW.1, realizeGradedForm g μ W hAW.2.1) +
    (realizeGradedForm g μ B hBZ.1, realizeGradedForm g μ Z hBZ.2.1) ∈ _
  exact map_mem_closure₂ continuous_add
    ((diracMinimalGraph_iff_core_closure g μ A W hAW.1 hAW.2.1).mp hAW)
    ((diracMinimalGraph_iff_core_closure g μ B Z hBZ.1 hBZ.2.1).mp hBZ)
    (fun _ hp _ hq => diracCoreRealizedGraph_add g μ hμ hp hq)

/-- The actual Dirac expression of the zero graded section is zero. -/
theorem diracRealForm_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    diracRealForm g.form (0 : OperatorCandidates.GradedRealForm M) = 0 := by
  have he (j : ℕ) : exteriorRealForm (0 : RealForm M j) = 0 := by
    simpa only [zero_smul] using exteriorRealForm_smul (M := M) (k := j) 0 (0 : RealForm M j) smoothRealForm_zero
  funext j
  cases j with
  | zero => exact codifferentialRealForm_zero g μ hμ 0
  | succ j =>
      change exteriorRealForm (0 : RealForm M j) + codifferentialRealForm g.form (0 : RealForm M (j + 2)) = 0
      rw [he j, codifferentialRealForm_zero g μ hμ (j + 1), add_zero]

theorem diracCorePair_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    OperatorCandidates.DiracCorePair g.form μ (0 : OperatorCandidates.GradedRealForm M) 0 := by
  have h := diracRealForm_corePair g μ hμ (0 : OperatorCandidates.GradedRealForm M)
    (fun _ => smoothRealForm_zero) (fun _ => by simp [CompactlySupportedRealForm])
  simpa only [diracRealForm_zero g μ hμ] using h

/-- Finite sums of exact minimal graph pairs stay in the same minimal graph. -/
theorem diracMinimalGraph_finset_sum {ι : Type*} (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (s : Finset ι)
    (A W : ι → OperatorCandidates.GradedRealForm M)
    (h : ∀ i ∈ s, OperatorCandidates.DiracMinimalGraph g.form μ (A i) (W i)) :
    OperatorCandidates.DiracMinimalGraph g.form μ (∑ i ∈ s, A i) (∑ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using diracCorePair_minimal (diracCorePair_zero g μ hμ)
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      exact diracMinimalGraph_add g μ hμ (A i) (W i) _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end Yau.LeafProofs.L03
