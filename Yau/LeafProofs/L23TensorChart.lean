import Yau.LeafProofs.L23TensorPullback

/-! Genuine chart overlaps and the naturality of the original derivative. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

def realChartOverlap (c d : M.Carrier) : Set (ComplexVector n) :=
  chartTarget c ∩ (chartInv c) ⁻¹' (extChartAt (ComplexModel n) d).source

theorem isOpen_realChartOverlap (c d : M.Carrier) : IsOpen (realChartOverlap c d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hInv : ContinuousAt (chartInv c) z := continuousAt_extChartAt_symm'' hz.1
  exact inter_mem ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz.1)
    (hInv.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) d).mem_nhds hz.2))

theorem covariantD_contDiffOn_of_subset (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (hOc : O ⊆ chartTarget c)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) O) (v : Fin (r+1) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => covariantD h c A z v) O := by
  apply (L12Aux.rDeriv_contDiffOn hO (hA (fun j => v j.succ)) (v 0)).sub
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.sum
  intro b _
  exact ((christoffel_contDiffOn h hh c b (v 0) (v j.succ)).mono hOc).mul
    (hA (Function.update (fun i => v i.succ) j b))

theorem covariantD_chart_change
    (h : HermitianField M) (hh : MetricSmooth h) (c d : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) (L12Aux.realChartChange c d z))
    (hTransform : ∀ w ∈ realChartOverlap c d,
      tensorEvalCLM (A w)=(tensorEvalCLM (B (L12Aux.realChartChange c d w))).compContinuousLinearMap
        (fun _ : Fin r => fderiv ℝ (L12Aux.realChartChange c d) w)) :
    tensorEvalCLM (covariantD h c A z)=
      (tensorEvalCLM (covariantD h d B (L12Aux.realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin (r+1) => fderiv ℝ (L12Aux.realChartChange c d) z) := by
  have hnear : realChartOverlap c d ∈ 𝓝 z := (isOpen_realChartOverlap c d).mem_nhds ⟨hz,hy⟩
  have heq : (fun w => tensorEvalCLM (A w)) =ᶠ[𝓝 z]
      (fun w => (tensorEvalCLM (B (L12Aux.realChartChange c d w))).compContinuousLinearMap
        (fun _ : Fin r => fderiv ℝ (L12Aux.realChartChange c d) w)) := by
    filter_upwards [hnear] with w hw
    exact hTransform w hw
  apply covariantD_pullback_at h c d A B (L12Aux.realChartChange c d) z
    ((L12Aux.realChartChange_contDiffAt c d hz hy).of_le (by simp)) hA hB heq
  exact chartChristoffelBilin_change h hh c d hz hy

end Yau.LeafProofs.L23Aux
