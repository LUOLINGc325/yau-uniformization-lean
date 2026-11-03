import Yau.LeafProofs.L23TensorChart

/-! Constant target covectors and their actual first two covariant derivatives. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def coordinateCovectorTensor (ell : RIdx n) : CovTensor n 1 :=
  fun v => if v 0=ell then 1 else 0

def coordinateCovectorForm (ell : RIdx n) : RealTensorForm n 1 :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 1) ℝ).compContinuousLinearMap
    (fun _ => L12Aux.realCoordCLM ell)

theorem coordinateCovectorForm_apply (ell : RIdx n) (V : Fin 1 → ComplexVector n) :
    coordinateCovectorForm ell V=realCoord (V 0) ell := by
  simp [coordinateCovectorForm,L12Aux.realCoordCLM_apply]

theorem tensorEvalCLM_coordinateCovector (ell : RIdx n) :
    tensorEvalCLM (coordinateCovectorTensor ell)=coordinateCovectorForm ell := by
  have hc : coordinateCovectorTensor ell=
      (fun v : Fin 1 → RIdx n => coordinateCovectorForm ell (fun j => realVec (v j))) := by
    funext v
    simp only [coordinateCovectorTensor,coordinateCovectorForm_apply,L12Aux.realCoord_realVec]
  rw [hc,tensorEvalCLM_coefficients]

def pulledCoordinateCovector (f : ComplexVector n → ComplexVector n) (ell : RIdx n)
    (z : ComplexVector n) : CovTensor n 1 :=
  fun v => realCoord (fderiv ℝ f z (realVec (v 0))) ell

theorem tensorEvalCLM_pulledCoordinateCovector (f : ComplexVector n → ComplexVector n)
    (ell : RIdx n) (z : ComplexVector n) :
    tensorEvalCLM (pulledCoordinateCovector f ell z)=
      (tensorEvalCLM (coordinateCovectorTensor ell)).compContinuousLinearMap
        (fun _ : Fin 1 => fderiv ℝ f z) := by
  rw [tensorEvalCLM_coordinateCovector]
  have hc : pulledCoordinateCovector f ell z=
      (fun v : Fin 1 → RIdx n =>
        ((coordinateCovectorForm ell).compContinuousLinearMap
          (fun _ : Fin 1 => fderiv ℝ f z)) (fun j => realVec (v j))) := by
    funext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      coordinateCovectorForm_apply,pulledCoordinateCovector]
  rw [hc,tensorEvalCLM_coefficients]

theorem pulledCoordinateCovector_contDiffAt
    (f : ComplexVector n → ComplexVector n) (ell : RIdx n) (z : ComplexVector n)
    (hf : ContDiffAt ℝ ∞ f z) (v : Fin 1 → RIdx n) :
    ContDiffAt ℝ ∞ (fun w => pulledCoordinateCovector f ell w v) z := by
  have hJ := (hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := realVec (v 0)))
  have hh := (L12Aux.realCoordCLM ell).contDiff.contDiffAt.comp z hJ
  simpa only [Function.comp_def,L12Aux.realCoordCLM_apply,pulledCoordinateCovector] using hh

variable {M : ComplexManifold n}

theorem coordinateCovector_secondDerivative_change
    (h : HermitianField M) (hh : MetricSmooth h) (c d : M.Carrier) (ell : RIdx n)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (covariantD h c (covariantD h c
      (pulledCoordinateCovector (L12Aux.realChartChange c d) ell)) z)=
    (tensorEvalCLM (covariantD h d (covariantD h d
      (fun _ => coordinateCovectorTensor ell)) (L12Aux.realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin 3 => fderiv ℝ (L12Aux.realChartChange c d) z) := by
  let f := L12Aux.realChartChange c d
  let A := pulledCoordinateCovector f ell
  let B := fun _ : ComplexVector n => coordinateCovectorTensor ell
  let O := realChartOverlap c d
  have hO := isOpen_realChartOverlap c d
  have hOc : O ⊆ chartTarget c := fun _ hw => hw.1
  have hzO : z ∈ O := ⟨hz,hy⟩
  have hA (v : Fin 1 → RIdx n) : ContDiffOn ℝ ∞ (fun w => A w v) O := by
    intro w hw
    exact (pulledCoordinateCovector_contDiffAt f ell w
      (L12Aux.realChartChange_contDiffAt c d hw.1 hw.2) v).contDiffWithinAt
  have hB (v : Fin 1 → RIdx n) : ContDiffOn ℝ ∞ (fun w => B w v) (chartTarget d) := contDiffOn_const
  have hBase (w : ComplexVector n) (_ : w ∈ O) :
      tensorEvalCLM (A w)=(tensorEvalCLM (B (f w))).compContinuousLinearMap
        (fun _ : Fin 1 => fderiv ℝ f w) := tensorEvalCLM_pulledCoordinateCovector f ell w
  have hFirst (w : ComplexVector n) (hw : w ∈ O) :
      tensorEvalCLM (covariantD h c A w)=
        (tensorEvalCLM (covariantD h d B (f w))).compContinuousLinearMap
          (fun _ : Fin 2 => fderiv ℝ f w) := by
    apply covariantD_chart_change h hh c d A B hw.1 hw.2
    · intro v
      exact ((hA v).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)
    · intro v
      exact differentiableAt_const _
    · exact hBase
  have hzD : f z ∈ chartTarget d := (extChartAt (ComplexModel n) d).map_source hy
  apply covariantD_chart_change h hh c d (covariantD h c A) (covariantD h d B) hz hy
  · intro v
    exact ((covariantD_contDiffOn_of_subset h hh c A O hO hOc hA v).contDiffAt
      (hO.mem_nhds hzO)).differentiableAt (by simp)
  · intro v
    exact ((covariantD_contDiffOn h hh d B hB v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hzD)).differentiableAt (by simp)
  · exact hFirst

end Yau.LeafProofs.L23Aux
