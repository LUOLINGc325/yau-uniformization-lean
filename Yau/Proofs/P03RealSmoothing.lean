import Yau.Proofs.P03InteriorSmoothing

open scoped Topology ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem ofRealKernel_contDiff {k : ComplexVector n → ℝ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (fun y => (k y : ℂ)) := Complex.ofRealCLM.contDiff.comp hk

theorem ofRealKernel_hasCompactSupport {k : ComplexVector n → ℝ}
    (hkc : HasCompactSupport k) : HasCompactSupport (fun y => (k y : ℂ)) :=
  hkc.comp_left (g := Complex.ofReal) (by simp)

theorem ofRealKernel_tsupport_subset {k : ComplexVector n → ℝ} {r : ℝ}
    (hks : tsupport k ⊆ Metric.closedBall 0 r) :
    tsupport (fun y => (k y : ℂ)) ⊆ Metric.closedBall 0 r := by
  exact (tsupport_comp_subset (g := Complex.ofReal) (by simp) k).trans hks

theorem smoothBy_contDiff {f : ComplexVector n → ℂ} {k : ComplexVector n → ℝ}
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (smoothBy k f) :=
  hkc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hf.locallyIntegrable

theorem interior_real_smoothing_holomorphic
    {u : ComplexVector n → ℂ} {k : ComplexVector n → ℝ} {a : ComplexVector n} {r : ℝ}
    {U : Set (ComplexVector n)} (hKU : Metric.closedBall a (4 * r) ⊆ U)
    (huK : MemLp u 2 ((volume : Measure (ComplexVector n)).restrict
      (Metric.closedBall a (4 * r))))
    (hweak : ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y, u y * wirtBar ψ y (stdVec i)) = 0)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hks : tsupport k ⊆ Metric.closedBall 0 r) :
    DifferentiableOn ℂ
      (smoothBy k ((Metric.closedBall a (4 * r)).indicator u))
      (Metric.ball a (3 * r)) := by
  rw [smoothBy_eq_cmulConv]
  exact interior_smoothing_holomorphic hKU huK hweak (ofRealKernel_contDiff hk)
    (ofRealKernel_hasCompactSupport hkc) (ofRealKernel_tsupport_subset hks)

end Yau.NodeProofs.P03Aux
