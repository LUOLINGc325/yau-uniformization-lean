import Yau.Proofs.P03CoefficientNorms

noncomputable section

namespace Yau.NodeProofs.P03Aux.CoefficientNorms

open Yau.BundleDbar
open scoped Yau.NodeProofs.P03Aux.CoefficientNorms

scoped instance canonical_normedSpace_real {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :
    NormedSpace ℝ (CanonicalFiber M x) := NormedSpace.restrictScalars ℝ ℂ _

scoped instance canonical_scalarTower {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :
    IsScalarTower ℝ ℂ (CanonicalFiber M x) := IsScalarTower.restrictScalars ℝ ℂ _

scoped instance antiCanonical_normedSpace_real {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :
    NormedSpace ℝ (AntiCanonicalFiber M x) := inferInstance

scoped instance antiCanonical_scalarTower {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :
    IsScalarTower ℝ ℂ (AntiCanonicalFiber M x) := inferInstance

scoped instance tangentAntiCanonical_normedSpace_real {n : ℕ} (M : ComplexManifold n)
    (x : M.Carrier) : NormedSpace ℝ (TangentAntiCanonicalFiber M x) :=
  NormedSpace.restrictScalars ℝ ℂ _

scoped instance tangentAntiCanonical_scalarTower {n : ℕ} (M : ComplexManifold n)
    (x : M.Carrier) : IsScalarTower ℝ ℂ (TangentAntiCanonicalFiber M x) :=
  IsScalarTower.restrictScalars ℝ ℂ _

end Yau.NodeProofs.P03Aux.CoefficientNorms
