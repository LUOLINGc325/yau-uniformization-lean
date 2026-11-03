import Yau.Proofs.P03CoefficientRealScalars
import Yau.Proofs.P03FramePrebundle
import Yau.Proofs.P03DeterminantRegularity

open scoped Manifold Topology Bundle ContDiff
open Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms

variable {n : ℕ} {M : ComplexManifold n}

theorem antiCanonicalTransition_coordinate (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector 1) :
    antiCanonicalTransition a b x v =
      antiCanonicalCoordinateEquiv b x hb ((antiCanonicalCoordinateEquiv a x ha).symm v) := by
  ext i : 1
  change (determinantTransitionMatrix a b x).det * v i =
    ((antiCanonicalCoordinateEquiv a x ha).symm v) (chartTopForm b x hb)
  rw [antiCanonicalScalar_change a b x ha hb]
  have hv := congrArg (fun w : ComplexVector 1 => w i)
    ((antiCanonicalCoordinateEquiv a x ha).apply_symm_apply v)
  change ((antiCanonicalCoordinateEquiv a x ha).symm v) (chartTopForm a x ha) = v i at hv
  rw [hv]

theorem tangentAntiCanonicalTransition_coordinate (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector n) :
    tangentAntiCanonicalTransition a b x v =
      tangentAntiCanonicalCoordinateEquiv b x hb
        ((tangentAntiCanonicalCoordinateEquiv a x ha).symm v) := by
  change (determinantTransitionMatrix a b x).det • determinantTransition a b x v =
    tangentAntiCanonicalCoordinateLinearEquiv b x hb
      ((tangentAntiCanonicalCoordinateLinearEquiv a x ha).symm v)
  rw [tangentAntiCanonicalCoordinate_change a b x ha hb, LinearEquiv.apply_symm_apply]

def antiCanonicalPrebundle (M : ComplexManifold n) :
    VectorPrebundle ℂ (ComplexVector 1) (AntiCanonicalFiber M) :=
  chartCoordinateVectorPrebundle (AntiCanonicalFiber M) antiCanonicalCoordinateEquiv
    antiCanonicalTransition (fun a b => (antiCanonicalTransition_contMDiffOn a b).continuousOn)
    antiCanonicalTransition_coordinate

def tangentAntiCanonicalPrebundle (M : ComplexManifold n) :
    VectorPrebundle ℂ (ComplexVector n) (TangentAntiCanonicalFiber M) :=
  chartCoordinateVectorPrebundle (TangentAntiCanonicalFiber M) tangentAntiCanonicalCoordinateEquiv
    tangentAntiCanonicalTransition
    (fun a b => (tangentAntiCanonicalTransition_contMDiffOn a b).continuousOn)
    tangentAntiCanonicalTransition_coordinate

theorem antiCanonicalPrebundle_isContMDiff (M : ComplexManifold n) :
    (antiCanonicalPrebundle M).IsContMDiff (ComplexModel n) ⊤ :=
  chartCoordinateVectorPrebundle_isContMDiff _ _ _ _ _ antiCanonicalTransition_contMDiffOn

theorem tangentAntiCanonicalPrebundle_isContMDiff (M : ComplexManifold n) :
    (tangentAntiCanonicalPrebundle M).IsContMDiff (ComplexModel n) ⊤ :=
  chartCoordinateVectorPrebundle_isContMDiff _ _ _ _ _ tangentAntiCanonicalTransition_contMDiffOn

namespace CoefficientBundles

scoped instance antiCanonical_totalSpaceTopology (M : ComplexManifold n) :
    TopologicalSpace (TotalSpace (ComplexVector 1) (AntiCanonicalFiber M)) :=
  (antiCanonicalPrebundle M).totalSpaceTopology

scoped instance tangentAntiCanonical_totalSpaceTopology (M : ComplexManifold n) :
    TopologicalSpace (TotalSpace (ComplexVector n) (TangentAntiCanonicalFiber M)) :=
  (tangentAntiCanonicalPrebundle M).totalSpaceTopology

open scoped CoefficientBundles

scoped instance antiCanonical_fiberBundle (M : ComplexManifold n) :
    FiberBundle (ComplexVector 1) (AntiCanonicalFiber M) :=
  (antiCanonicalPrebundle M).toFiberBundle

scoped instance tangentAntiCanonical_fiberBundle (M : ComplexManifold n) :
    FiberBundle (ComplexVector n) (TangentAntiCanonicalFiber M) :=
  (tangentAntiCanonicalPrebundle M).toFiberBundle

scoped instance antiCanonical_vectorBundle (M : ComplexManifold n) :
    VectorBundle ℂ (ComplexVector 1) (AntiCanonicalFiber M) :=
  (antiCanonicalPrebundle M).toVectorBundle

scoped instance tangentAntiCanonical_vectorBundle (M : ComplexManifold n) :
    VectorBundle ℂ (ComplexVector n) (TangentAntiCanonicalFiber M) :=
  (tangentAntiCanonicalPrebundle M).toVectorBundle

scoped instance antiCanonical_contMDiffVectorBundle (M : ComplexManifold n) :
    ContMDiffVectorBundle ⊤ (ComplexVector 1) (AntiCanonicalFiber M) (ComplexModel n) := by
  letI := antiCanonicalPrebundle_isContMDiff M
  exact VectorPrebundle.contMDiffVectorBundle (a := antiCanonicalPrebundle M)
    (IB := ComplexModel n) (n := ⊤)

scoped instance tangentAntiCanonical_contMDiffVectorBundle (M : ComplexManifold n) :
    ContMDiffVectorBundle ⊤ (ComplexVector n) (TangentAntiCanonicalFiber M) (ComplexModel n) := by
  letI := tangentAntiCanonicalPrebundle_isContMDiff M
  exact VectorPrebundle.contMDiffVectorBundle (a := tangentAntiCanonicalPrebundle M)
    (IB := ComplexModel n) (n := ⊤)

end CoefficientBundles

end Yau.NodeProofs.P03Aux
