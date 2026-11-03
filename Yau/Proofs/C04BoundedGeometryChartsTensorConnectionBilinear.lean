import Yau.Proofs.C04BoundedGeometryChartsCurvatureDerivative

/-! The connection action is a fixed bounded bilinear operation on the model spaces. -/

noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

local instance : NormedAddCommGroup
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedSpace ℝ
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedAddCommGroup
    (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : NormedSpace ℝ
    (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : FiniteDimensional ℝ (RealTensorForm n r) :=
  FiniteDimensional.of_surjective tensorEvalCLMMap.toLinearMap
    (fun T => ⟨(fun idx => T (fun j => realVec (idx j))), tensorEvalCLM_coefficients T⟩)

def tensorConnectionCLM
    (conn : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (T : RealTensorForm n r) : ComplexVector n →L[ℝ] RealTensorForm n r :=
  ∑ s : Fin r, ((T.compContinuousLinearMapLRight).toContinuousLinearMap
    (fun _ => ContinuousLinearMap.id ℝ (ComplexVector n)) s).comp conn

theorem tensorConnectionCLM_apply
    (conn : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (T : RealTensorForm n r) (u : ComplexVector n) (V : Fin r → ComplexVector n) :
    tensorConnectionCLM conn T u V = ∑ s : Fin r, T (Function.update V s (conn u (V s))) := by
  simp only [tensorConnectionCLM, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro s _
  change T (fun j => Function.update (fun _ : Fin r => ContinuousLinearMap.id ℝ (ComplexVector n)) s
    (conn u) j (V j)) = _
  congr 1
  funext j
  by_cases hj : j = s
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj, ContinuousLinearMap.id_apply]

def tensorConnectionLinear (n r : ℕ) : RealTensorForm n r →ₗ[ℝ]
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →ₗ[ℝ]
      ComplexVector n →L[ℝ] RealTensorForm n r :=
  LinearMap.mk₂ ℝ (fun T conn => tensorConnectionCLM conn T)
    (by
      intro T S conn
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [tensorConnectionCLM_apply, add_apply, Finset.sum_add_distrib])
    (by
      intro a T conn
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [tensorConnectionCLM_apply, smul_apply, Finset.smul_sum])
    (by
      intro T conn chi
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [tensorConnectionCLM_apply, add_apply, ContinuousMultilinearMap.map_update_add,
        Finset.sum_add_distrib])
    (by
      intro a T conn
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [tensorConnectionCLM_apply, smul_apply, ContinuousMultilinearMap.map_update_smul,
        Finset.smul_sum])

def tensorConnectionBilinear (n r : ℕ) : RealTensorForm n r →L[ℝ]
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ]
      ComplexVector n →L[ℝ] RealTensorForm n r :=
  let K :
      (((ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →ₗ[ℝ]
        ComplexVector n →L[ℝ] RealTensorForm n r)) ≃ₗ[ℝ]
      ((ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ]
        ComplexVector n →L[ℝ] RealTensorForm n r) := LinearMap.toContinuousLinearMap
  (K.toLinearMap.comp (tensorConnectionLinear n r)).toContinuousLinearMap

theorem tensorConnectionBilinear_apply
    (conn : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (T : RealTensorForm n r) (u : ComplexVector n) (V : Fin r → ComplexVector n) :
    tensorConnectionBilinear n r T conn u V =
      ∑ s : Fin r, T (Function.update V s (conn u (V s))) :=
  tensorConnectionCLM_apply conn T u V

end Yau.Proofs.C04ChartsAux
