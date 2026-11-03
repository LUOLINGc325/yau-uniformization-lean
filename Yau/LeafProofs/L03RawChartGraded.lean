import Yau.LeafProofs.L03RawChartForms

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Raw compact Euclidean graded L² fields push to genuine Riemannian
L² sections with compact chart support, and their exact zero pullback
reconstructs the original field. No smoothness is assumed. -/
theorem modelGradedChartPushforward_raw_properties (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : MemLp G 2 (lebesgueC n))
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    OperatorCandidates.GradedL2 g.form μ (modelGradedChartPushforward x G) ∧
      (∀ j, CompactlySupportedRealForm (modelGradedChartPushforward x G j) ∧
        closure {y | modelGradedChartPushforward x G j y ≠ 0} ⊆
          (extChartAt (ComplexModel n) x).source) ∧
      modelGradedChartPullbackZero (modelGradedChartPushforward x G) x = G := by
  let P := fun j z => modelGradedProjection n j (G z)
  have hs (j : ℕ) : tsupport (P j) ⊆ tsupport G := by
    apply closure_mono
    intro z hz hzero
    exact hz (by change modelGradedProjection n j (G z) = 0; rw [hzero, map_zero])
  have hcP (j : ℕ) : HasCompactSupport (P j) :=
    hcG.of_isClosed_subset (isClosed_tsupport _) (hs j)
  have hPO (j : ℕ) : tsupport (P j) ⊆ chartTarget x := (hs j).trans hGO
  have hPm (j : ℕ) : MemLp (P j) 2 (lebesgueC n) :=
    (modelGradedProjection n j).comp_memLp' hG
  have hL (j : ℕ) : L2RealForm g.form μ (modelGradedChartPushforward x G j) :=
    chartFormPushforward_l2_of_memLp g μ hμ x (P j) (hPm j) (hcP j) (hPO j)
  refine ⟨(gradedL2_iff g.form μ _).mpr hL, ?_, ?_⟩
  · intro j
    have hi := chartFormPushforward_image_support x (P j) (hcP j) (hPO j)
    have hK : IsCompact (chartInv x '' tsupport (P j)) :=
      (hcP j).image_of_continuousOn ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono (hPO j))
    refine ⟨hK.of_isClosed_subset isClosed_closure hi, ?_⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hi hy
    exact (extChartAt (ComplexModel n) x).map_target (hPO j hz)
  · funext z
    by_cases hz : z ∈ chartTarget x
    · rw [modelGradedChartPullbackZero_eq _ x hz, modelGradedChartPushforward_to_chart x G hz]
    · have hGz : G z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hGO h))
      funext i
      simp only [modelGradedChartPullbackZero, chartFormPullbackZero, if_neg hz, hGz, Pi.zero_apply]

end Yau.LeafProofs.L03
