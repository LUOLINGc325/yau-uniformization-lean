import Yau.LeafProofs.L03FormFiniteLimits

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem l2RealForm_multiply_smooth_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) : L2RealForm g.form μ (multiplyRealForm η A) := by
  have hcont := L18Aux.continuous_of_smoothFn hη
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support hcη
  exact l2RealForm_multiply_bounded g μ η hcont.aestronglyMeasurable (max D 0) (le_max_right _ _)
    (fun y => (show |η y| ≤ D by simpa only [Real.norm_eq_abs] using hD y).trans (le_max_left _ _)) A hA

theorem hodgeLowerRealForm_smooth_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    SmoothRealForm (hodgeLowerRealForm g.form k A) ∧
      CompactlySupportedRealForm (hodgeLowerRealForm g.form k A) := by
  cases k with
  | zero => exact ⟨smoothRealForm_zero, by simp [hodgeLowerRealForm, CompactlySupportedRealForm]⟩
  | succ j => exact ⟨codifferentialRealForm_smooth g μ hμ A hA,
      codifferentialRealForm_compactlySupported g μ hμ A hA hcA⟩

/-- Every compact smooth scalar multiplier of an original raw Hodge
deficiency field admits a genuine compact smooth approximation in the
actual d/δ energy graph. The outputs and a common compact support are
constructed from finitely many genuine chart regularizations. -/
theorem exists_hodge_compact_multiplier_energy_approximation
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    ∃ L : Set M.Carrier, IsCompact L ∧
      ∃ (As : ℕ → RealForm M k) (V : RealForm M (k + 1)) (W : RealForm M (k - 1)),
      (∀ m, SmoothRealForm (As m) ∧ CompactlySupportedRealForm (As m) ∧
        closure {y | As m y ≠ 0} ⊆ L) ∧ L2RealForm g.form μ V ∧ L2RealForm g.form μ W ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (As m) (multiplyRealForm η A)) atTop (𝓝 0) ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (exteriorRealForm (As m)) V) atTop (𝓝 0) ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (hodgeLowerRealForm g.form k (As m)) W) atTop (𝓝 0) := by
  classical
  obtain ⟨s, φ, hφ, hsumφ⟩ := exists_finite_compact_smooth_chart_partition hcη
  let θ := fun i : s => fun z => φ i z * η (chartInv (i : M.Carrier) z)
  have hθ (i : s) := scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) (i : M.Carrier)) (φ i)
    (hφ i).1 (hφ i).2.1 (hφ i).2.2 (fun z => η (chartInv (i : M.Carrier) z)) (hη (i : M.Carrier))
  let ζ := fun i : s => L18Aux.chartPushforwardZero (i : M.Carrier) (θ i)
  let Ai := fun i : s => multiplyRealForm (ζ i) A
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  have hpiece (i : s) := exists_chart_hodge_energy_approximation g μ hμ A hmax (i : M.Carrier) b
    (θ i) (hθ i).1 (hθ i).2.1 ((hθ i).2.2.trans (hφ i).2.2)
  choose Li hLi As V W hAs hV hW htA htV htW using hpiece
  have hAi (i : s) : L2RealForm g.form μ (Ai i) :=
    l2RealForm_multiply_smooth_compact g μ (ζ i)
      (L18Aux.smoothFn_chartPushforwardZero (i : M.Carrier) (hθ i).1 (hθ i).2.1 ((hθ i).2.2.trans (hφ i).2.2))
      (L18Aux.chartPushforwardZero_properties (i : M.Carrier) (hθ i).1 (hθ i).2.1 ((hθ i).2.2.trans (hφ i).2.2)).1 A hmax.1
  have hAs2 (m : ℕ) (i : s) : L2RealForm g.form μ (As i m) :=
    smooth_compactlySupported_l2RealForm g μ hμ (As i m) (hAs i m).1 (hAs i m).2.1
  have hdAs2 (m : ℕ) (i : s) : L2RealForm g.form μ (exteriorRealForm (As i m)) :=
    smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth _ (hAs i m).1)
      (exteriorRealForm_compactlySupported _ (hAs i m).1 (hAs i m).2.1)
  have hlAs2 (m : ℕ) (i : s) : L2RealForm g.form μ (hodgeLowerRealForm g.form k (As i m)) :=
    smooth_compactlySupported_l2RealForm g μ hμ _
      (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs i m).1 (hAs i m).2.1).1
      (hodgeLowerRealForm_smooth_compact g μ hμ _ (hAs i m).1 (hAs i m).2.1).2
  have hsζ (y : M.Carrier) : (∑ i : s, ζ i y) = η y := by
    calc
      _ = ∑ i : s, L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y * η y :=
        Finset.sum_congr rfl (fun i _ => congrFun (chartPushforwardZero_mul_inChart (i : M.Carrier) (φ i) η) y)
      _ = (∑ i : s, L18Aux.chartPushforwardZero (i : M.Carrier) (φ i) y) * η y := (Finset.sum_mul _ _ _).symm
      _ = η y := by
        by_cases hy : η y = 0
        · rw [hy, mul_zero]
        · rw [hsumφ y (subset_tsupport η hy), one_mul]
  have hsAi : (∑ i : s, Ai i) = multiplyRealForm η A := by
    funext y
    simp only [Finset.sum_apply, Ai, multiplyRealForm]
    rw [← Finset.sum_smul, hsζ y]
  let L : Set M.Carrier := ⋃ i : s, Li i
  have hL : IsCompact L := isCompact_iUnion hLi
  let T := fun m => ∑ i : s, As i m
  have hTs (m : ℕ) : SmoothRealForm (T m) := smoothRealForm_finset_sum Finset.univ _ (fun i _ => (hAs i m).1)
  have hTL (m : ℕ) : closure {y | T m y ≠ 0} ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro y hy
    by_contra hn
    have hz (i : s) : As i m y = 0 := by
      by_contra hne
      exact hn (Set.mem_iUnion.mpr ⟨i, (hAs i m).2.2 (subset_closure hne)⟩)
    exact hy (by simp only [T, Finset.sum_apply, hz, Finset.sum_const_zero])
  refine ⟨L, hL, T, ∑ i : s, V i, ∑ i : s, W i, ?_,
    l2RealForm_finset_sum g μ Finset.univ V (fun i _ => hV i),
    l2RealForm_finset_sum g μ Finset.univ W (fun i _ => hW i), ?_, ?_, ?_⟩
  · intro m
    exact ⟨hTs m, hL.of_isClosed_subset isClosed_closure (hTL m), hTL m⟩
  · have h := formL2DistanceSq_fintype_sum_tendsto g μ (fun m i => As i m) Ai hAs2 hAi htA
    simpa only [T, hsAi] using h
  · have h := formL2DistanceSq_fintype_sum_tendsto g μ (fun m i => exteriorRealForm (As i m)) V hdAs2 hV htV
    have heq (m : ℕ) : exteriorRealForm (T m) = ∑ i : s, exteriorRealForm (As i m) :=
      exteriorRealForm_finset_sum Finset.univ _ (fun i _ => (hAs i m).1)
    simpa only [heq] using h
  · have h := formL2DistanceSq_fintype_sum_tendsto g μ (fun m i => hodgeLowerRealForm g.form k (As i m)) W hlAs2 hW htW
    have heq (m : ℕ) : hodgeLowerRealForm g.form k (T m) = ∑ i : s, hodgeLowerRealForm g.form k (As i m) :=
      hodgeLowerRealForm_finset_sum g μ hμ Finset.univ _ (fun i _ => (hAs i m).1)
    simpa only [heq] using h

end Yau.LeafProofs.L03
