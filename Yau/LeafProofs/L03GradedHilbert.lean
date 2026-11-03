import Yau.LeafProofs.L03DiracMultiplier
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual finite graded metric L² Hilbert space, with the sum inner
product rather than the auxiliary product sup norm. -/
abbrev L2GradedHilbert (g : SmoothMetric M) (μ : Measure M.Carrier) :=
  PiLp 2 (fun i : Fin (2 * n + 1) => L2FormHilbert g μ i.val)

def realizeGradedL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A) :
    L2GradedHilbert g μ := WithLp.toLp 2 (realizeGradedForm g μ A hA)

theorem realizeGradedL2_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B) :
    inner ℝ (realizeGradedL2 g μ A hA) (realizeGradedL2 g μ B hB) =
      ∫ y, OperatorCandidates.gradedInner g.form A B y ∂μ := by
  rw [PiLp.inner_apply]
  change (∑ i : Fin (2 * n + 1), inner ℝ
    (realizeL2Form g μ (L2FormSpace.ofSection (A i.val) (hA.2 i.val)))
    (realizeL2Form g μ (L2FormSpace.ofSection (B i.val) (hB.2 i.val)))) = _
  simp only [realizeL2Form_inner, L2FormSpace.toSection_ofSection]
  exact (integral_finsetSum Finset.univ (fun i _ =>
    formInner_integrable g μ (A i.val) (B i.val) (hA.2 i.val) (hB.2 i.val))).symm

theorem realizeGradedL2_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A) :
    ‖realizeGradedL2 g μ A hA‖ ^ 2 = ∫ y, OperatorCandidates.gradedInner g.form A A y ∂μ := by
  rw [← real_inner_self_eq_norm_sq, realizeGradedL2_inner]

/-- The original frozen graded distance is exactly the squared norm in
the genuine finite metric L² Hilbert realization. -/
theorem realizeGradedL2_distanceSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B) :
    ENNReal.ofReal (‖realizeGradedL2 g μ A hA - realizeGradedL2 g μ B hB‖ ^ 2) =
      OperatorCandidates.gradedDistanceSq g.form μ A B := by
  rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  exact realizeL2Form_distanceSq g μ (L2FormSpace.ofSection (A i.val) (hA.2 i.val))
    (L2FormSpace.ofSection (B i.val) (hB.2 i.val))

theorem gradedL2_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B) :
    OperatorCandidates.GradedL2 g.form μ (A - B) :=
  (gradedL2_iff g.form μ (A - B)).mpr (fun j => l2RealForm_sub g μ (A j) (B j) (hA.2 j) (hB.2 j))

theorem realizeGradedL2_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B)
    (hAB : OperatorCandidates.GradedL2 g.form μ (A - B)) :
    realizeGradedL2 g μ (A - B) hAB = realizeGradedL2 g μ A hA - realizeGradedL2 g μ B hB := by
  apply PiLp.ext
  intro i
  exact UniformSpace.Completion.coe_sub
    (L2FormSpace.ofSection (A i.val) (hA.2 i.val)) (L2FormSpace.ofSection (B i.val) (hB.2 i.val))

theorem tendsto_realizeGradedL2_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As : ℕ → OperatorCandidates.GradedRealForm M) (A : OperatorCandidates.GradedRealForm M)
    (hAs : ∀ j, OperatorCandidates.GradedL2 g.form μ (As j))
    (hA : OperatorCandidates.GradedL2 g.form μ A) :
    Tendsto (fun j => realizeGradedL2 g μ (As j) (hAs j)) atTop (𝓝 (realizeGradedL2 g μ A hA)) ↔
      Tendsto (fun j => OperatorCandidates.gradedDistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht := (PiLp.continuous_ofLp 2 (fun i : Fin (2 * n + 1) => L2FormHilbert g μ i.val)).tendsto
      (realizeGradedL2 g μ A hA) |>.comp h
    exact (tendsto_realizeGradedForm_iff g μ As A hAs hA).mp ht
  · intro h
    have ht := (tendsto_realizeGradedForm_iff g μ As A hAs hA).mpr h
    exact (PiLp.continuous_toLp 2 (fun i : Fin (2 * n + 1) => L2FormHilbert g μ i.val)).tendsto
      (realizeGradedForm g μ A hA) |>.comp ht

/-- The actual maximal weak graph is exactly pairing against its fixed
actual compact smooth Dirac core in this Hilbert realization. -/
theorem diracMaximalGraph_iff_gradedHilbert_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W) :
    OperatorCandidates.DiracMaximalGraph g.form μ A W ↔
      ∀ B Z (hc : OperatorCandidates.DiracCorePair g.form μ B Z),
        inner ℝ (realizeGradedL2 g μ A hA) (realizeGradedL2 g μ Z hc.2.1) =
          inner ℝ (realizeGradedL2 g μ W hW) (realizeGradedL2 g μ B hc.1) := by
  constructor
  · intro h B Z hc
    simpa only [realizeGradedL2_inner] using (h.2.2 B Z hc).2.2
  · intro h
    refine ⟨hA, hW, ?_⟩
    intro B Z hc
    refine ⟨gradedInner_integrable g μ A Z hA hc.2.1,
      gradedInner_integrable g μ W B hW hc.1, ?_⟩
    simpa only [realizeGradedL2_inner] using h B Z hc

end Yau.LeafProofs.L03
