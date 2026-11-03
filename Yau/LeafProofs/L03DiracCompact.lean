import Yau.LeafProofs.L03DiracUniqueness

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem gradedInner_add_left (g : HermitianField M) (A B C : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g (A + B) C =
      OperatorCandidates.gradedInner g A C + OperatorCandidates.gradedInner g B C := by
  funext y
  simp only [OperatorCandidates.gradedInner, Pi.add_apply, formInner_add_left, Finset.sum_add_distrib]

/-- The actual distributional maximal graph is additive. -/
theorem diracMaximalGraph_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W B Z : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hBZ : OperatorCandidates.DiracMaximalGraph g.form μ B Z) :
    OperatorCandidates.DiracMaximalGraph g.form μ (A + B) (W + Z) := by
  refine ⟨gradedL2_add g μ A B hAW.1 hBZ.1,
    gradedL2_add g μ W Z hAW.2.1 hBZ.2.1, ?_⟩
  intro C D hc
  have h1 := hAW.2.2 C D hc
  have h2 := hBZ.2.2 C D hc
  refine ⟨?_, ?_, ?_⟩
  · rw [gradedInner_add_left]
    exact h1.1.add h2.1
  · rw [gradedInner_add_left]
    exact h1.2.1.add h2.2.1
  · rw [gradedInner_add_left, gradedInner_add_left]
    simp only [Pi.add_apply]
    rw [integral_add h1.1 h2.1, integral_add h1.2.1 h2.2.1, h1.2.2, h2.2.2]

theorem diracMaximalGraph_finset_sum {ι : Type*} (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (s : Finset ι)
    (A W : ι → OperatorCandidates.GradedRealForm M)
    (h : ∀ i ∈ s, OperatorCandidates.DiracMaximalGraph g.form μ (A i) (W i)) :
    OperatorCandidates.DiracMaximalGraph g.form μ (∑ i ∈ s, A i) (∑ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using diracCorePair_maximal g μ hμ _ _ (diracCorePair_zero g μ hμ)
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      exact diracMaximalGraph_add g μ (A i) (W i) _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Once an actual maximal input is a finite sum of genuine minimal graph
inputs, the output sum is forced to equal its original output a.e. Thus no
unproved derivative cancellation for a rough partition support is needed. -/
theorem diracMinimalGraph_of_finite_minimal_partition {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (As Ws : ι → OperatorCandidates.GradedRealForm M)
    (hmin : ∀ i, OperatorCandidates.DiracMinimalGraph g.form μ (As i) (Ws i))
    (hsum : (∑ i, As i) = A) : OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  have hs : OperatorCandidates.DiracMinimalGraph g.form μ (∑ i, As i) (∑ i, Ws i) :=
    diracMinimalGraph_finset_sum g μ hμ Finset.univ As Ws (fun i _ => hmin i)
  rw [hsum] at hs
  have hsm := diracMinimalGraph_implies_maximal g μ hμ A (∑ i, Ws i) hs
  have hw := diracMaximalGraph_output_ae_unique g μ hμ A (∑ i, Ws i) W hsm hmax
  exact diracMinimalGraph_of_ae_eq (fun _ => Filter.Eventually.of_forall fun _ => rfl) hw hs

/-- Finite compact chart localization of actual maximal pairs suffices to
assemble the original minimal graph; all output matching is derived. -/
theorem diracMinimalGraph_of_finite_chart_maximal_partition {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (x : ι → M.Carrier) (As Ws : ι → OperatorCandidates.GradedRealForm M)
    (hloc : ∀ i, OperatorCandidates.DiracMaximalGraph g.form μ (As i) (Ws i))
    (hcA : ∀ i j, CompactlySupportedRealForm (As i j))
    (hcW : ∀ i j, CompactlySupportedRealForm (Ws i j))
    (hsA : ∀ i j, closure {y | As i j y ≠ 0} ⊆ (extChartAt (ComplexModel n) (x i)).source)
    (hsW : ∀ i j, closure {y | Ws i j y ≠ 0} ⊆ (extChartAt (ComplexModel n) (x i)).source)
    (hsum : (∑ i, As i) = A) : OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  apply diracMinimalGraph_of_finite_minimal_partition g μ hμ A W hmax As Ws _ hsum
  intro i
  exact diracMaximalGraph_to_minimal_of_compact_chart g μ hμ (As i) (Ws i) (hloc i)
    (hcA i) (hcW i) (x i) (hsA i) (hsW i)

end Yau.LeafProofs.L03
