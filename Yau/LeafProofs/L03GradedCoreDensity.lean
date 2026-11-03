import Yau.LeafProofs.L03GradedHilbert

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Inputs of the fixed actual compact smooth Dirac core, realized in the
true sum-inner-product graded L² Hilbert space. -/
def diracHilbertCoreInputSet (g : SmoothMetric M) (μ : Measure M.Carrier) : Set (L2GradedHilbert g μ) :=
  {v | ∃ (A W : OperatorCandidates.GradedRealForm M)
    (hc : OperatorCandidates.DiracCorePair g.form μ A W), v = realizeGradedL2 g μ A hc.1}

/-- Density of genuine compact smooth form inputs holds for the actual
full graded Dirac core, not an independently chosen test space. -/
theorem diracHilbertCoreInputSet_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Dense (diracHilbertCoreInputSet g μ) := by
  classical
  let T : Set (L2GradedProduct g μ) := Set.pi Set.univ
    (fun i : Fin (2 * n + 1) => Prod.fst '' hodgeCoreRealizedGraph g μ i.val)
  have hd : Dense T := dense_pi Set.univ (fun i _ => hodgeCoreRealizedGraph_domain_dense g μ hμ i.val)
  have hsurj : Function.Surjective (WithLp.toLp 2 : L2GradedProduct g μ → L2GradedHilbert g μ) :=
    fun v => ⟨WithLp.ofLp v, rfl⟩
  have hdi := hsurj.denseRange.dense_image
    (PiLp.continuous_toLp 2 (fun i : Fin (2 * n + 1) => L2FormHilbert g μ i.val)) hd
  apply hdi.mono
  rintro v ⟨p, hp, rfl⟩
  have hi (i : Fin (2 * n + 1)) : ∃ B : RealForm M i.val,
      ∃ hB : L2RealForm g.form μ B, SmoothRealForm B ∧ CompactlySupportedRealForm B ∧
        p i = realizeL2Form g μ (L2FormSpace.ofSection B hB) := by
    obtain ⟨q, hq, heq⟩ := hp i (Set.mem_univ i)
    obtain ⟨B, C, hBC, rfl⟩ := hq
    exact ⟨B, hBC.2.2.2.1, hBC.1, hBC.2.1, heq.symm⟩
  choose B hB hsB hcB heq using hi
  let A : OperatorCandidates.GradedRealForm M := fun j => if hj : j < 2 * n + 1 then B ⟨j, hj⟩ else 0
  have hAs (j : ℕ) : SmoothRealForm (A j) ∧ CompactlySupportedRealForm (A j) := by
    by_cases hj : j < 2 * n + 1
    · simpa only [A, dif_pos hj] using And.intro (hsB ⟨j, hj⟩) (hcB ⟨j, hj⟩)
    · simp only [A, dif_neg hj]
      exact ⟨smoothRealForm_zero, by simp [CompactlySupportedRealForm]⟩
  have hA := gradedL2_of_smooth_compact g μ hμ A (fun j => (hAs j).1) (fun j => (hAs j).2)
  have hAi (i : Fin (2 * n + 1)) : A i.val = B i := by
    dsimp only [A]
    rw [dif_pos i.isLt]
  have hpi : realizeGradedForm g μ A hA = p := by
    funext i
    change realizeL2Form g μ (L2FormSpace.ofSection (A i.val) (hA.2 i.val)) = p i
    have hs : L2FormSpace.ofSection (A i.val) (hA.2 i.val) = L2FormSpace.ofSection (B i) (hB i) := by
      apply L2FormSpace.toSection_injective g μ i.val
      exact hAi i
    rw [hs]
    exact (heq i).symm
  have hc := diracRealForm_corePair g μ hμ A (fun j => (hAs j).1) (fun j => (hAs j).2)
  refine ⟨A, diracRealForm g.form A, hc, ?_⟩
  change WithLp.toLp 2 p = WithLp.toLp 2 (realizeGradedForm g μ A hc.1)
  congr 1
  exact hpi.symm

/-- Bounds on all genuine compact Dirac inputs control the norm of an
actual graded Hilbert vector. The required core density is proved internally. -/
theorem gradedHilbert_norm_le_of_core_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (e : L2GradedHilbert g μ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (B Z : OperatorCandidates.GradedRealForm M) (hc : OperatorCandidates.DiracCorePair g.form μ B Z),
      |inner ℝ e (realizeGradedL2 g μ B hc.1)| ≤ C * ‖realizeGradedL2 g μ B hc.1‖) : ‖e‖ ≤ C := by
  have hs : closure (diracHilbertCoreInputSet g μ) ⊆
      {v : L2GradedHilbert g μ | |inner ℝ e v| ≤ C * ‖v‖} := by
    apply closure_minimal
    · rintro v ⟨B, Z, hc, rfl⟩
      exact h B Z hc
    · exact isClosed_le (continuous_const.inner continuous_id).abs (continuous_const.mul continuous_norm)
  have he : |inner ℝ e e| ≤ C * ‖e‖ := hs (by
    rw [(diracHilbertCoreInputSet_dense g μ hμ).closure_eq]
    trivial)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at he
  by_cases hzero : ‖e‖ = 0
  · simpa only [hzero] using hC
  · have hpos : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg e) (Ne.symm hzero)
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [pow_two, mul_comm] using he)

end Yau.LeafProofs.L03
