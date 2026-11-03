import Yau.Proofs.C04BoundedGeometryChartsJacobiIntegral
import Yau.LeafProofs.L12JacobiCurvature

/-! The actual Jacobi equation in a fixed Euclidean operator space. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Manifold ContDiff Matrix Matrix.Norms.Elementwise

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def physicalMatrixMap (n : ℕ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ →L[ℝ]
      (EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) :=
  (Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearMap

def physicalJacobiOperator (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ) (realGeodesicJacobiMatrix g q t)

def physicalJacobiDerivative (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ) (realGeodesicJacobiMatrixDeriv g q t)

def physicalCurvatureOperator (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ) (realGeodesicCurvatureMatrix g q t)

theorem physicalJacobiOperator_hasDerivAt (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    HasDerivAt (physicalJacobiOperator g q) (physicalJacobiDerivative g q t) t := by
  have H : HasDerivAt (realGeodesicJacobiMatrix g q)
      (realGeodesicJacobiMatrixDeriv g q t) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j =>
      realGeodesicJacobiMatrix_hasDerivAt g q t i j
  exact (physicalMatrixMap n).hasFDerivAt.comp_hasDerivAt t H

theorem physicalJacobiDerivative_hasDerivAt (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    HasDerivAt (physicalJacobiDerivative g q)
      (-(physicalCurvatureOperator g q t * physicalJacobiOperator g q t)) t := by
  have H : HasDerivAt (realGeodesicJacobiMatrixDeriv g q)
      (-(realGeodesicCurvatureMatrix g q t * realGeodesicJacobiMatrix g q t)) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j =>
      realGeodesicJacobiMatrixDeriv_hasDerivAt_matrix g q t i j
  have H' := (physicalMatrixMap n).hasFDerivAt.comp_hasDerivAt t H
  change HasDerivAt (physicalJacobiDerivative g q)
    (Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℝ)
      (-(realGeodesicCurvatureMatrix g q t * realGeodesicJacobiMatrix g q t))) t at H'
  simpa only [map_neg, map_mul, physicalCurvatureOperator, physicalJacobiOperator] using H'

@[simp] theorem physicalJacobiOperator_zero (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    physicalJacobiOperator g q 0 = 0 := by
  simp only [physicalJacobiOperator, realGeodesicJacobiMatrix_zero, map_zero]

@[simp] theorem physicalJacobiDerivative_zero (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    physicalJacobiDerivative g q 0 = 1 := by
  simp only [physicalJacobiDerivative, realGeodesicJacobiMatrixDeriv_zero, map_one]

theorem physicalJacobiOperator_volterra (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {α : ℝ} (hR : ∀ u ∈ Icc (0 : ℝ) 1, ‖physicalCurvatureOperator g q u‖ ≤ α) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      physicalJacobiOperator g q t = t • 1 -
        ∫ u in 0..t, (t - u) • (physicalCurvatureOperator g q u * physicalJacobiOperator g q u) :=
  volterra_identity_of_jacobi_equations _ _ _
    (physicalJacobiOperator_hasDerivAt g q) (physicalJacobiDerivative_hasDerivAt g q)
    (physicalJacobiOperator_zero g q) (physicalJacobiDerivative_zero g q) hR

end Yau.Proofs.C04ChartsAux
