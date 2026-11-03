import Yau.LeafProofs.L23CovariantTrace

/-! Smoothness and iterated metric-trace differentiation for the original
covariant derivative. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorMetricTrace_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n (r+2))
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c)) (v : Fin r → RIdx n) :
    ContDiffOn ℝ ∞ (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹ (A w) v) (chartTarget c) := by
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact (realMetricFn_inverse_contDiffOn h hh c a b).mul (hA (Fin.cons a (Fin.cons b v)))

theorem covariantD_twoMetricTraces (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n (r+4))
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹
      (tensorMetricTrace (realMetricFn h c w)⁻¹ (A w))) z (Fin.cons i v)=
      tensorMetricTrace (realMetricFn h c z)⁻¹
        (tensorMetricTrace (realMetricFn h c z)⁻¹
          (fun u => covariantD h c A z (Fin.cons i u))) v := by
  have hAd (u : Fin (r+4) → RIdx n) := ((hA u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hT (u : Fin (r+2) → RIdx n) := ((tensorMetricTrace_contDiffOn h hh c A hA u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  rw [covariantD_tensorMetricTrace h hh c _ hz hT]
  simp_rw [covariantD_tensorMetricTrace h hh c A hz hAd]
  rfl

end Yau.LeafProofs.L23Aux
