import Yau.LeafProofs.L03DiracCompactClosure

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Scalar chart pushforward respects multiplication by an arbitrary
intrinsic scalar function, using the exact chart inverse on its source. -/
theorem chartPushforwardZero_mul_inChart (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (η : M.Carrier → ℝ) :
    L18Aux.chartPushforwardZero x (fun z => φ z * η (chartInv x z)) =
      fun y => L18Aux.chartPushforwardZero x φ y * η y := by
  funext y
  by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
  · have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
    simp only [L18Aux.chartPushforwardZero, if_pos hy, hi]
  · simp only [L18Aux.chartPushforwardZero, if_neg hy, zero_mul]

/-- Every compact smooth scalar multiplier of an arbitrary original
maximal input has an internally constructed actual minimal Dirac output.
There is no compactness premise on the original input or output. -/
theorem diracMaximalGraph_compact_multiplier_exists_minimal_output
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    ∃ V : OperatorCandidates.GradedRealForm M,
      OperatorCandidates.DiracMinimalGraph g.form μ (fun j => multiplyRealForm η (A j)) V := by
  classical
  obtain ⟨s, φ, hφ, hsumφ⟩ := exists_finite_compact_smooth_chart_partition hcη
  let θ := fun i : s => fun z => φ i z * η (chartInv (i : M.Carrier) z)
  have hθ (i : s) := scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) (i : M.Carrier)) (φ i)
    (hφ i).1 (hφ i).2.1 (hφ i).2.2 (fun z => η (chartInv (i : M.Carrier) z)) (hη (i : M.Carrier))
  let ζ := fun i : s => L18Aux.chartPushforwardZero (i : M.Carrier) (θ i)
  let b := Module.finBasis ℝ (modelGradedFiber n)
  let As := fun i : s => fun j => multiplyRealForm (ζ i) (A j)
  let Vs := fun i : s => modelGradedChartPushforward (i : M.Carrier)
    (diracLocalizedChartOutput g.form (i : M.Carrier) b (θ i) A W)
  have hm (i : s) : OperatorCandidates.DiracMinimalGraph g.form μ (As i) (Vs i) :=
    diracMaximalGraph_chart_multiplier_minimal g μ hμ A W hmax (i : M.Carrier) b (θ i)
      (hθ i).1 (hθ i).2.1 ((hθ i).2.2.trans (hφ i).2.2)
  have heq (i : s) : ζ i = fun y => L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y * η y :=
    chartPushforwardZero_mul_inChart (i : M.Carrier) (φ i) η
  have hsζ (y : M.Carrier) : (∑ i : s, ζ i y) = η y := by
    calc
      _ = ∑ i : s, L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y * η y :=
        Finset.sum_congr rfl (fun i _ => congrFun (heq i) y)
      _ = (∑ i : s, L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y) * η y := (Finset.sum_mul _ _ _).symm
      _ = η y := by
        by_cases hy : η y = 0
        · rw [hy, mul_zero]
        · rw [hsumφ y (subset_tsupport η hy), one_mul]
  have hsA : (∑ i : s, As i) = fun j => multiplyRealForm η (A j) := by
    funext j y
    simp only [Finset.sum_apply, As, multiplyRealForm]
    rw [← Finset.sum_smul, hsζ y]
  have hmin : OperatorCandidates.DiracMinimalGraph g.form μ (∑ i : s, As i) (∑ i : s, Vs i) :=
    diracMinimalGraph_finset_sum g μ hμ Finset.univ As Vs (fun i _ => hm i)
  exact ⟨∑ i : s, Vs i, hsA ▸ hmin⟩

end Yau.LeafProofs.L03
