import Yau.Proofs.P03CoefficientCharts

open scoped Manifold Topology ContDiff TensorProduct
open Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

/-- Intrinsic evaluation, alternating in the tangent inputs and valued in the
actual continuous dual of the canonical fibre. -/
def canonicalEvaluationTensor (x : M.Carrier) :
    (TangentVector M x) [⋀^Fin n]→ₗ[ℂ] AntiCanonicalFiber M x where
  toMultilinearMap :=
    { toFun := fun v => ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ v
      map_update_add' := by
        intro _ v i u w
        apply ContinuousLinearMap.ext
        intro η
        exact η.map_update_add v i u w
      map_update_smul' := by
        intro _ v i c u
        apply ContinuousLinearMap.ext
        intro η
        exact η.map_update_smul v i c u }
  map_eq_zero_of_eq' := by
    intro v i j h hij
    apply ContinuousLinearMap.ext
    intro η
    exact η.map_eq_zero_of_eq v h hij

def scalarToAntiTop (f : M.Carrier → ℂ) : NQForm (AntiCanonicalFiber M) 0 := fun x =>
  ⟨AlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0)
    (f x • canonicalEvaluationTensor x), by intro v i; exact Fin.elim0 i⟩

def fieldToTangentAntiTop (V : VectorField M) : NQForm (TangentAntiCanonicalFiber M) 0 := fun x =>
  ⟨AlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0)
    ((TensorProduct.mk ℂ (TangentVector M x) (AntiCanonicalFiber M x) (V x)).compAlternatingMap
      (canonicalEvaluationTensor x)), by intro v i; exact Fin.elim0 i⟩

@[simp] theorem scalarToAntiTop_apply (f : M.Carrier → ℂ) (x : M.Carrier)
    (v : Fin n → TangentVector M x) :
    ((scalarToAntiTop f x).1 Fin.elim0) v =
      f x • ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ v := rfl

@[simp] theorem fieldToTangentAntiTop_apply (V : VectorField M) (x : M.Carrier)
    (v : Fin n → TangentVector M x) :
    ((fieldToTangentAntiTop V x).1 Fin.elim0) v =
      V x ⊗ₜ[ℂ] ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ v := rfl

theorem scalarToAntiTop_coefficients (f : M.Carrier → ℂ) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (α : Fin 1) :
    coefficients (r := 1) (AntiCanonicalFiber M) (scalarToAntiTop f) a z Fin.elim0 α =
      inChart a f z := by
  let x := chartInv a z
  have hx : x ∈ (extChartAt (ComplexModel n) a).source := (extChartAt (ComplexModel n) a).map_target hz
  have he : (fun i => chartVec a x (stdVec i)) = determinantFrameBasis a x hx := by
    funext i
    exact (determinantFrameBasis_apply a x hx i).symm
  change ((trivializationAt (ComplexVector 1) (AntiCanonicalFiber M) a).continuousLinearMapAt ℂ x
    (f x • ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ
      (fun i => chartVec a x (stdVec i)))) α = f x
  rw [he]
  change ((trivializationAt (ComplexVector 1) (AntiCanonicalFiber M) a).continuousLinearMapAt ℂ x
    (f x • chartTopEvaluation a x hx)) α = f x
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hx,
    antiCanonical_trivialization_apply a x hx]
  change antiCanonicalCoordinateEquiv a x hx (f x • chartTopEvaluation a x hx) α = f x
  simp only [map_smul, PiLp.smul_apply, antiCanonicalCoordinateEquiv_apply,
    chartTopEvaluation_topForm, smul_eq_mul, mul_one]

theorem fieldToTangentAntiTop_coefficients (V : VectorField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    coefficients (r := n) (TangentAntiCanonicalFiber M) (fieldToTangentAntiTop V) a z Fin.elim0 =
      fieldCoords V a z := by
  let x := chartInv a z
  have hx : x ∈ (extChartAt (ComplexModel n) a).source := (extChartAt (ComplexModel n) a).map_target hz
  have he : (fun i => chartVec a x (stdVec i)) = determinantFrameBasis a x hx := by
    funext i
    exact (determinantFrameBasis_apply a x hx i).symm
  change (trivializationAt (ComplexVector n) (TangentAntiCanonicalFiber M) a).continuousLinearMapAt ℂ x
    (V x ⊗ₜ[ℂ] ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ
      (fun i => chartVec a x (stdVec i))) = tangentCoords a x (V x)
  rw [he]
  change (trivializationAt (ComplexVector n) (TangentAntiCanonicalFiber M) a).continuousLinearMapAt ℂ x
    (V x ⊗ₜ[ℂ] chartTopEvaluation a x hx) = tangentCoords a x (V x)
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hx,
    tangentAntiCanonical_trivialization_apply a x hx]
  change tangentAntiCanonicalCoordinateLinearEquiv a x hx
    (V x ⊗ₜ[ℂ] chartTopEvaluation a x hx) = tangentCoords a x (V x)
  rw [tangentAntiCanonicalCoordinateLinearEquiv_tmul, chartTopEvaluation_topForm, one_smul]

end Yau.NodeProofs.P03Aux
