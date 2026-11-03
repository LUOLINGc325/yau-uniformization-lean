import Yau.Proofs.P03TopFormHolomorphic
import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff TensorProduct

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarToAntiTop_value (f : M.Carrier → ℂ) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    Yau.LeafProofs.L14Aux.topTensorValueEquiv (AntiCanonicalFiber M) a x hx
      (scalarToAntiTop f x) = f x • chartTopEvaluation a x hx := by
  change f x • ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ
    (Yau.LeafProofs.chartFrameBasis a x hx) = _
  congr 2
  funext i
  rw [Yau.LeafProofs.chartFrameBasis_apply, determinantFrameBasis_apply]

theorem fieldToTangentAntiTop_value (V : VectorField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    Yau.LeafProofs.L14Aux.topTensorValueEquiv (TangentAntiCanonicalFiber M) a x hx
      (fieldToTangentAntiTop V x) = V x ⊗ₜ[ℂ] chartTopEvaluation a x hx := by
  change V x ⊗ₜ[ℂ] ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ
    (Yau.LeafProofs.chartFrameBasis a x hx) = _
  congr 2
  funext i
  rw [Yau.LeafProofs.chartFrameBasis_apply, determinantFrameBasis_apply]

/-- Recover the intrinsic scalar from an actual anticanonical-valued top tensor. -/
def antiTopToScalar (u : NQForm (AntiCanonicalFiber M) 0) : M.Carrier → ℂ := fun x =>
  antiCanonicalScalarEquiv x x (mem_extChartAt_source x)
    (Yau.LeafProofs.L14Aux.topTensorValueEquiv (AntiCanonicalFiber M) x x
      (mem_extChartAt_source x) (u x))

/-- Recover an actual tangent vector from an actual determinant-tensor top tensor. -/
def tangentAntiTopToField (u : NQForm (TangentAntiCanonicalFiber M) 0) : VectorField M :=
  fun x => chartVec x x
    (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)
      (Yau.LeafProofs.L14Aux.topTensorValueEquiv (TangentAntiCanonicalFiber M) x x
        (mem_extChartAt_source x) (u x)))

@[simp] theorem antiTopToScalar_scalarToAntiTop (f : M.Carrier → ℂ) :
    antiTopToScalar (scalarToAntiTop f) = f := by
  funext x
  unfold antiTopToScalar
  rw [scalarToAntiTop_value]
  change (f x • chartTopEvaluation x x (mem_extChartAt_source x))
    (chartTopForm x x (mem_extChartAt_source x)) = f x
  simp only [ContinuousLinearMap.smul_apply, chartTopEvaluation_topForm,
    smul_eq_mul, mul_one]

@[simp] theorem scalarToAntiTop_antiTopToScalar (u : NQForm (AntiCanonicalFiber M) 0) :
    scalarToAntiTop (antiTopToScalar u) = u := by
  funext x
  apply (Yau.LeafProofs.L14Aux.topTensorValueEquiv (AntiCanonicalFiber M) x x
    (mem_extChartAt_source x)).injective
  rw [scalarToAntiTop_value]
  exact (anticanonical_eq_smul_chartTopEvaluation x x (mem_extChartAt_source x) _).symm

@[simp] theorem tangentAntiTopToField_fieldToTangentAntiTop (V : VectorField M) :
    tangentAntiTopToField (fieldToTangentAntiTop V) = V := by
  funext x
  unfold tangentAntiTopToField
  rw [fieldToTangentAntiTop_value, tangentAntiCanonicalCoordinateLinearEquiv_tmul,
    chartTopEvaluation_topForm, one_smul, chartVec_tangentCoords x x (mem_extChartAt_source x)]

@[simp] theorem fieldToTangentAntiTop_tangentAntiTopToField
    (u : NQForm (TangentAntiCanonicalFiber M) 0) :
    fieldToTangentAntiTop (tangentAntiTopToField u) = u := by
  funext x
  apply (Yau.LeafProofs.L14Aux.topTensorValueEquiv (TangentAntiCanonicalFiber M) x x
    (mem_extChartAt_source x)).injective
  rw [fieldToTangentAntiTop_value]
  apply (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).injective
  rw [tangentAntiCanonicalCoordinateLinearEquiv_tmul, chartTopEvaluation_topForm, one_smul]
  exact tangentCoords_chartVec x x (mem_extChartAt_source x) _

theorem antiTopToScalar_holomorphic (u : NQForm (AntiCanonicalFiber M) 0)
    (hu : HolomorphicTopForm (r := 1) (AntiCanonicalFiber M) u) :
    IsHolomorphicFn (antiTopToScalar u) := by
  apply (scalar_holomorphic_iff _).mp
  simpa only [scalarToAntiTop_antiTopToScalar] using hu

theorem tangentAntiTopToField_holomorphic (u : NQForm (TangentAntiCanonicalFiber M) 0)
    (hu : HolomorphicTopForm (r := n) (TangentAntiCanonicalFiber M) u) :
    IsHolomorphicField (tangentAntiTopToField u) := by
  apply (field_holomorphic_iff _).mp
  simpa only [fieldToTangentAntiTop_tangentAntiTopToField] using hu

end Yau.NodeProofs.P03Aux
