import Yau.Proofs.C04BoundedGeometryChartsCurvatureOperator

/-! A fixed trilinear model for the actual curvature operator. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
local instance : FiniteDimensional ℝ (RealTensorForm n 4) :=
  FiniteDimensional.of_surjective tensorEvalCLMMap.toLinearMap
    (fun T => ⟨(fun idx => T (fun j => realVec (idx j))), tensorEvalCLM_coefficients T⟩)

private abbrev End (n : ℕ) := ComplexVector n →L[ℝ] ComplexVector n
private abbrev Op (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ComplexVector n) (ComplexVector n)

def curvatureContractionRaw (T : RealTensorForm n 4) (L N : End n) : Op n :=
  (curvatureRaisingMap n T).compContinuousLinearMap ![L, N, ContinuousLinearMap.id ℝ (ComplexVector n)]

theorem curvatureContractionRaw_apply (T : RealTensorForm n 4) (L N : End n)
    (V : Fin 3 → ComplexVector n) :
    curvatureContractionRaw T L N V = curvatureRaisingMap n T ![L (V 0), N (V 1), V 2] := by
  unfold curvatureContractionRaw
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

private def contractionPair (T : RealTensorForm n 4) : End n →ₗ[ℝ] End n →ₗ[ℝ] Op n :=
  LinearMap.mk₂ ℝ (curvatureContractionRaw T)
    (by
      intro L M N
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [curvatureContractionRaw_apply, add_apply]
      change (curvatureRaisingMap n T).curryLeft (L (V 0) + M (V 0)) ![N (V 1), V 2] = _
      rw [map_add, add_apply]
      rfl)
    (by
      intro a L N
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [curvatureContractionRaw_apply, smul_apply]
      change (curvatureRaisingMap n T).curryLeft (a • L (V 0)) ![N (V 1), V 2] = _
      rw [map_smul, smul_apply]
      rfl)
    (by
      intro L N P
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [curvatureContractionRaw_apply, add_apply]
      change ((curvatureRaisingMap n T).curryLeft (L (V 0))).curryLeft
        (N (V 1) + P (V 1)) ![V 2] = _
      rw [map_add, add_apply]
      rfl)
    (by
      intro a L N
      apply ContinuousMultilinearMap.ext
      intro V
      simp only [curvatureContractionRaw_apply, smul_apply]
      change ((curvatureRaisingMap n T).curryLeft (L (V 0))).curryLeft
        (a • N (V 1)) ![V 2] = _
      rw [map_smul, smul_apply]
      rfl)

private def contractionLinear (n : ℕ) :
    RealTensorForm n 4 →ₗ[ℝ] End n →ₗ[ℝ] End n →ₗ[ℝ] Op n where
  toFun := contractionPair
  map_add' := by
    intro T S
    apply LinearMap.ext
    intro L
    apply LinearMap.ext
    intro N
    apply ContinuousMultilinearMap.ext
    intro V
    simp only [contractionPair, LinearMap.mk₂_apply, curvatureContractionRaw_apply,
      map_add, add_apply, LinearMap.add_apply]
  map_smul' := by
    intro a T
    apply LinearMap.ext
    intro L
    apply LinearMap.ext
    intro N
    apply ContinuousMultilinearMap.ext
    intro V
    simp only [contractionPair, LinearMap.mk₂_apply, curvatureContractionRaw_apply,
      map_smul, smul_apply, LinearMap.smul_apply, RingHom.id_apply]

def curvatureContraction (n : ℕ) : RealTensorForm n 4 →L[ℝ] End n →L[ℝ] End n →L[ℝ] Op n :=
  let K₁ : (End n →ₗ[ℝ] Op n) ≃ₗ[ℝ] (End n →L[ℝ] Op n) := LinearMap.toContinuousLinearMap
  let K₂ : (End n →ₗ[ℝ] End n →ₗ[ℝ] Op n) →ₗ[ℝ] (End n →L[ℝ] End n →L[ℝ] Op n) :=
    (LinearMap.toContinuousLinearMap :
      (End n →ₗ[ℝ] End n →L[ℝ] Op n) ≃ₗ[ℝ] (End n →L[ℝ] End n →L[ℝ] Op n)).toLinearMap.comp
      (LinearMap.llcomp ℝ (End n) (End n →ₗ[ℝ] Op n) (End n →L[ℝ] Op n) K₁.toLinearMap)
  (K₂.comp (contractionLinear n)).toContinuousLinearMap

theorem curvatureContraction_apply (T : RealTensorForm n 4) (L N : End n) :
    curvatureContraction n T L N = curvatureContractionRaw T L N := rfl

theorem radialCurvatureOperator_eq_contraction {M : ComplexManifold n}
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    radialCurvatureOperator g p U v =
      curvatureContraction n (radialCurvatureForm g p U 0 v) (radialCoframe g p U v) (radialCoframe g p U v) := rfl

end Yau.Proofs.C04ChartsAux
