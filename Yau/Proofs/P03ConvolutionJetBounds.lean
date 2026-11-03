import Yau.Proofs.P03ConvolutionJets

open scoped Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem scalarConvolution_norm_le (f : ComplexVector n → ℂ) (k : ComplexVector n → F)
    (hf : Integrable f volume) (x : ComplexVector n) (t A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ y, ‖k y‖ ≤ A) (hs : tsupport k ⊆ Metric.closedBall 0 t) :
    ‖scalarConvolution f k x‖ ≤ A * ∫ y in Metric.closedBall x t, ‖f y‖ := by
  let K := Metric.closedBall x t
  have hi : Integrable (fun y => A * K.indicator (fun y => ‖f y‖) y) volume :=
    (hf.norm.indicator Metric.isClosed_closedBall.measurableSet).const_mul A
  have hdom : ∀ y, ‖f y • k (x - y)‖ ≤ A * K.indicator (fun y => ‖f y‖) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hbound (x - y)) (norm_nonneg (f y))).trans_eq
        (mul_comm _ _)
    · have hn : x - y ∉ tsupport k := by
        intro hk
        apply hy
        have hh := hs hk
        simpa only [K, Metric.mem_closedBall, dist_zero_right, dist_eq_norm,
          sub_zero, norm_sub_rev] using hh
      rw [image_eq_zero_of_notMem_tsupport hn, smul_zero, norm_zero,
        Set.indicator_of_notMem hy, mul_zero]
  change ‖∫ y, f y • k (x - y)‖ ≤ _
  calc
    _ ≤ ∫ y, A * K.indicator (fun y => ‖f y‖) y :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hdom)
    _ = _ := by
      rw [integral_const_mul, integral_indicator Metric.isClosed_closedBall.measurableSet]

theorem scalarConvolution_jet_norm_le (f : ComplexVector n → ℂ) (k : ComplexVector n → F)
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (j : ℕ) (x : ComplexVector n) (t A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ y, ‖iteratedFDeriv ℝ j k y‖ ≤ A)
    (hs : tsupport k ⊆ Metric.closedBall 0 t) :
    ‖iteratedFDeriv ℝ j (scalarConvolution f k) x‖ ≤
      A * ∫ y in Metric.closedBall x t, ‖f y‖ := by
  rw [scalarConvolution_iteratedFDeriv f k hf.locallyIntegrable hk hkc]
  exact scalarConvolution_norm_le f (iteratedFDeriv ℝ j k) hf x t A hA hbound
    ((tsupport_iteratedFDeriv_subset j).trans hs)

end Yau.NodeProofs.P03Aux
