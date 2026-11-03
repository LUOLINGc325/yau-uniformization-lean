import Yau.Proofs.P03TensorFibres

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

/-- Select a compatible norm without replacing the pre-existing TVS topology. -/
@[instance_reducible] def compatibleNormedAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsNormableSpace ℂ V] [T2Space V] : NormedAddCommGroup V := by
  letI := IsNormableSpace.toSeminormedAddCommGroup ℂ V
  exact { (inferInstance : SeminormedAddCommGroup V) with
    toMetricSpace := MetricSpace.ofT0PseudoMetricSpace V }

@[instance_reducible] def compatibleNormedSpace (V : Type*) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsNormableSpace ℂ V] [T2Space V] :
    @NormedSpace ℂ V _ (compatibleNormedAddCommGroup V).toSeminormedAddCommGroup :=
  IsNormableSpace.toNormedSpace ℂ V

namespace CoefficientNorms

scoped instance canonical_finiteDimensional (M : ComplexManifold n) (x : M.Carrier) :
    FiniteDimensional ℂ (CanonicalFiber M x) :=
  (canonicalScalarEquiv x x (mem_extChartAt_source x)).symm.toLinearEquiv.finiteDimensional

scoped instance antiCanonical_finiteDimensional (M : ComplexManifold n) (x : M.Carrier) :
    FiniteDimensional ℂ (AntiCanonicalFiber M x) :=
  (antiCanonicalScalarEquiv x x (mem_extChartAt_source x)).symm.toLinearEquiv.finiteDimensional

open scoped CoefficientNorms

scoped instance canonical_normable (M : ComplexManifold n) (x : M.Carrier) :
    IsNormableSpace ℂ (CanonicalFiber M x) :=
  (canonicalScalarEquiv x x (mem_extChartAt_source x)).isNormableSpace

scoped instance canonical_normedAddCommGroup (M : ComplexManifold n) (x : M.Carrier) :
    NormedAddCommGroup (CanonicalFiber M x) := compatibleNormedAddCommGroup _

scoped instance canonical_normedSpace (M : ComplexManifold n) (x : M.Carrier) :
    NormedSpace ℂ (CanonicalFiber M x) := compatibleNormedSpace _

scoped instance tangentAntiCanonical_normedAddCommGroup (M : ComplexManifold n) (x : M.Carrier) :
    NormedAddCommGroup (TangentAntiCanonicalFiber M x) :=
  NormedAddCommGroup.induced _ _
    (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).toAddEquiv
    (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).injective

scoped instance tangentAntiCanonical_normedSpace (M : ComplexManifold n) (x : M.Carrier) :
    NormedSpace ℂ (TangentAntiCanonicalFiber M x) :=
  NormedSpace.induced ℂ _ _
    (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).toLinearMap

scoped instance tangentAntiCanonical_finiteDimensional (M : ComplexManifold n) (x : M.Carrier) :
    FiniteDimensional ℂ (TangentAntiCanonicalFiber M x) :=
  (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).symm.finiteDimensional

end CoefficientNorms

open scoped CoefficientNorms

/-- All chart tensor coordinates are continuous for the selected fibre norm. -/
def tangentAntiCanonicalCoordinateEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    TangentAntiCanonicalFiber M x ≃L[ℂ] ComplexVector n :=
  (tangentAntiCanonicalCoordinateLinearEquiv a x hx).toContinuousLinearEquiv

end Yau.NodeProofs.P03Aux
