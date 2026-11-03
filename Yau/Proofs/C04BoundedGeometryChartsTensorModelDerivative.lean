import Yau.Proofs.C04BoundedGeometryChartsTensorConnectionBilinear

/-! The actual curvature-derivative identity as a sum of fixed model bilinear operations. -/

noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : NormedAddCommGroup
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedSpace ℝ
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

def tensorInsertionBilinear (n r : ℕ) : RealTensorForm n (r + 1) →L[ℝ]
    (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ComplexVector n →L[ℝ] RealTensorForm n r :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (RealTensorForm n r)).bilinearComp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => ComplexVector n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    (ContinuousLinearMap.id ℝ (ComplexVector n →L[ℝ] ComplexVector n))

theorem tensorInsertionBilinear_apply (N : RealTensorForm n (r + 1))
    (A : ComplexVector n →L[ℝ] ComplexVector n) (u : ComplexVector n)
    (V : Fin r → ComplexVector n) :
    tensorInsertionBilinear n r N A u V = N (Fin.cons (A u) V) := rfl

def tensorModelStepNorm (n j : ℕ) : ℝ :=
  ‖tensorInsertionBilinear n (4 + j)‖ + ‖tensorConnectionBilinear n (4 + j)‖

theorem tensorModelStepNorm_nonneg (n j : ℕ) : 0 ≤ tensorModelStepNorm n j :=
  add_nonneg (norm_nonneg (tensorInsertionBilinear n (4 + j)))
    (norm_nonneg (tensorConnectionBilinear n (4 + j)))

theorem radialCurvatureForm_fderiv_eq {M : ComplexManifold n}
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (j : ℕ) (v : ComplexVector n) :
    fderiv ℝ (radialCurvatureForm g p U j) v =
      tensorInsertionBilinear n (4 + j) (radialCurvatureForm g p U (j + 1) v) (radialCoframe g p U v) +
        tensorConnectionBilinear n (4 + j) (radialCurvatureForm g p U j v) (radialConnection g p U v) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMultilinearMap.ext
  intro V
  rw [add_apply, add_apply, tensorInsertionBilinear_apply, tensorConnectionBilinear_apply]
  exact radialCurvatureForm_fderiv g p U j v u V

end Yau.Proofs.C04ChartsAux
