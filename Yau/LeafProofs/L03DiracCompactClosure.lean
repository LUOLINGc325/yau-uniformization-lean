import Yau.LeafProofs.L03DiracRowToMinimal

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

set_option maxHeartbeats 1000000 in
/-- Multiplying an original maximal Dirac input by a genuine compact chart
scalar gives an actual minimal pair with its internally constructed raw L²
product-rule output. -/
theorem diracMaximalGraph_chart_multiplier_minimal {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    OperatorCandidates.DiracMinimalGraph g.form μ
      (fun j => multiplyRealForm (L18Aux.chartPushforwardZero x φ) (A j))
      (modelGradedChartPushforward x (diracLocalizedChartOutput g.form x b φ A W)) := by
  classical
  let P := fun z => φ z • modelGradedChartPullbackZero A x z
  let Q := diracLocalizedChartOutput g.form x b φ A W
  have hPm : MemLp P 2 (lebesgueC n) :=
    modelGradedChartPullbackZero_cutoff_memLp g μ hμ A hmax.1 x φ hφ hcφ hφO
  have hPs : tsupport P ⊆ tsupport φ := by
    apply closure_mono
    intro z hz hzero
    exact hz (by change φ z • modelGradedChartPullbackZero A x z = 0; rw [hzero, zero_smul])
  have hcP : HasCompactSupport P := hcφ.of_isClosed_subset (isClosed_tsupport _) hPs
  have hQ := diracLocalizedChartOutput_properties g μ hμ A W hmax.1 hmax.2.1 x b φ hφ hcφ hφO
  have hrawP := modelGradedChartPushforward_raw_properties g μ hμ x P hPm hcP (hPs.trans hφO)
  have hrawQ := modelGradedChartPushforward_raw_properties g μ hμ x Q hQ.1 hQ.2.1 (hQ.2.2.trans hφO)
  have hmin : OperatorCandidates.DiracMinimalGraph g.form μ
      (modelGradedChartPushforward x P) (modelGradedChartPushforward x Q) := by
    apply diracMinimalGraph_of_compact_chart_row_tests g μ hμ _ _ hrawP.1 hrawQ.1
      (fun j => (hrawP.2.1 j).1) (fun j => (hrawQ.2.1 j).1) x
      (fun j => (hrawP.2.1 j).2) (fun j => (hrawQ.2.1 j).2) b
    intro r ψ hψ hcψ
    have hh := diracMaximalGraph_localized_chart_row_test g μ hμ A W hmax x b φ hφ hcφ hφO r ψ hψ hcψ
    simpa only [hrawP.2.2, hrawQ.2.2, Q, diracLocalizedChartOutput_coordinates,
      P, map_smul, Finsupp.smul_apply, smul_eq_mul] using hh
  rwa [modelGradedChartPushforward_localized_input x φ hφO A] at hmin

/-- Every compactly supported rough input in the original actual maximal
Dirac graph belongs to its original minimal graph. All chart localization,
raw outputs, finite sums, and output identification are constructed internally. -/
theorem diracMaximalGraph_to_minimal_of_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j)) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  let K := ⋃ i : Fin (2 * n + 1), closure {y | A i.val y ≠ 0}
  have hcK : IsCompact K := isCompact_iUnion (fun i => hcA i.val)
  have hAK (j : ℕ) (y : M.Carrier) (hy : A j y ≠ 0) : y ∈ K := by
    by_cases hj : j ≤ 2 * n
    · exact Set.mem_iUnion.mpr ⟨⟨j, by omega⟩, subset_closure hy⟩
    · have hjgt : 2 * n < j := Nat.lt_of_not_ge hj
      exact False.elim (hy (by rw [hmax.1.1 j hjgt]; rfl))
  obtain ⟨s, φ, hφ, hsumφ⟩ := exists_finite_compact_smooth_chart_partition hcK
  let b := Module.finBasis ℝ (modelGradedFiber n)
  let η := fun i : s => L18Aux.chartPushforwardZero (i : M.Carrier) (φ i)
  let As := fun i : s => fun j => multiplyRealForm (η i) (A j)
  let Ws := fun i : s => modelGradedChartPushforward (i : M.Carrier)
    (diracLocalizedChartOutput g.form (i : M.Carrier) b (φ i) A W)
  have hmin (i : s) : OperatorCandidates.DiracMinimalGraph g.form μ (As i) (Ws i) :=
    diracMaximalGraph_chart_multiplier_minimal g μ hμ A W hmax (i : M.Carrier) b (φ i)
      (hφ i).1 (hφ i).2.1 (hφ i).2.2
  have hsumA : (∑ i : s, As i) = A := by
    funext j y
    simp only [Finset.sum_apply, As, multiplyRealForm]
    rw [← Finset.sum_smul]
    by_cases hy : A j y = 0
    · rw [hy, smul_zero]
    · have hs : (∑ i : s, η i y) = 1 := hsumφ y (hAK j y hy)
      rw [hs, one_smul]
  exact diracMinimalGraph_of_finite_minimal_partition g μ hμ A W hmax As Ws hmin hsumA

end Yau.LeafProofs.L03
