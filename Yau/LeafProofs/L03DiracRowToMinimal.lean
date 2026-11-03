import Yau.LeafProofs.L03DiracLocalWeak

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

set_option maxHeartbeats 1000000 in
/-- Compact actual chart L² fields satisfying the genuine scalar Dirac
rows belong to the original minimal graph. This is Friedrichs approximation,
without requiring or assuming a maximal graph for these fields. -/
theorem diracMinimalGraph_of_compact_chart_row_tests {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j)) (hcW : ∀ j, CompactlySupportedRealForm (W j))
    (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n))
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, ψ z * b.repr (modelGradedChartPullbackZero W x z) r ∂lebesgueC n) =
        ∫ z, ∑ c, b.repr (modelGradedChartPullbackZero A x z) c *
          diracFormalAdjointTestRow g.form x b r c ψ z ∂lebesgueC n) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  let U := modelGradedChartPullbackZero A x
  let V := modelGradedChartPullbackZero W x
  let a := diracScalarDerivativeCoefficient g.form x b
  let q := diracScalarValueCoefficient g.form x b
  have hU := modelGradedChartPullbackZero_properties g μ hμ A hA hcA x hAx b
  have hV := modelGradedChartPullbackZero_properties g μ hμ W hW hcW x hWx b
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨χ, hχ, hcχ, hχO, hχrange, hχK⟩ := exists_model_chart_cutoff hO
    (hU.1.union hV.1) (Set.union_subset hU.2.1 hV.2.1)
  have ha (r c : α) (i : RIdx n) : ContDiffOn ℝ ∞ (a r c i) (chartTarget x) :=
    diracScalarDerivativeCoefficient_contDiffOn g x b r c i
  have hAe (r c : α) (i : RIdx n) : ContDiff ℝ ∞ (fun z => χ z * a r c i z) :=
    (scalar_cutoff_contDiff_properties hO χ hχ hcχ hχO _ (ha r c i)).1
  have hBe (r c : α) : ContDiff ℝ ∞ (fun z => χ z * q r c z) :=
    (scalar_cutoff_contDiff_properties hO χ hχ hcχ hχO _
      (diracScalarValueCoefficient_contDiffOn g x b r c)).1
  have hweak : firstOrderSystemWeakEquation (lebesgueC n) (realModelBasis n)
      (fun r c i z => χ z * a r c i z) (fun r c z => χ z * q r c z)
      (fun z c => b.repr (U z) c) (fun z r => b.repr (V z) r) := by
    apply firstOrderSystemWeakEquation_of_row_integral (lebesgueC n) (realModelBasis n)
      (fun r c i z => χ z * a r c i z) (fun r c z => χ z * q r c z)
      (fun r c i => (hAe r c i).of_le (by simp)) (fun r c => (hBe r c).continuous)
      (fun z c => b.repr (U z) c) (fun z r => b.repr (V z) r) hU.2.2.2
    intro r ψ hψ hcψ
    rw [hrow r ψ hψ hcψ]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    apply Finset.sum_congr rfl
    intro c _
    change b.repr (U z) c * diracFormalAdjointTestRow g.form x b r c ψ z = _
    by_cases hz : U z = 0
    · simp only [hz, map_zero, Finsupp.zero_apply, zero_mul]
    · have hzK : z ∈ tsupport U ∪ tsupport V := Or.inl (subset_tsupport U hz)
      have hzO : z ∈ chartTarget x := hU.2.1 (subset_tsupport U hz)
      have hdA (i : RIdx n) : fderiv ℝ (fun y => χ y * a r c i y) z = fderiv ℝ (a r c i) z := by
        simpa only [(hχK z hzK).1, (hχK z hzK).2, one_smul, zero_smul, smul_zero, add_zero, zero_add] using
          fderiv_fun_mul (hχ.differentiable (by simp) z)
            (((ha r c i).contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp))
      simp only [diracFormalAdjointTestRow, hdA, (hχK z hzK).1, one_mul, a, q]
  exact diracMinimalGraph_of_compact_chart_extended_weak_system g μ hμ A W hA hW
    hcA hcW x hAx hWx b χ hχ hcχ hχO hχrange hχK hAe hBe hweak

end Yau.LeafProofs.L03
