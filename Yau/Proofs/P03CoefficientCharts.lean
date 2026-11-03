import Yau.Proofs.P03CoefficientBundles

open scoped Manifold Topology Bundle ContDiff
open Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem antiCanonical_holomorphic : Holomorphic (r := 1) (AntiCanonicalFiber M) :=
  CoefficientBundles.antiCanonical_contMDiffVectorBundle M

theorem tangentAntiCanonical_holomorphic :
    Holomorphic (r := n) (TangentAntiCanonicalFiber M) :=
  CoefficientBundles.tangentAntiCanonical_contMDiffVectorBundle M

@[simp] theorem antiCanonical_trivialization_baseSet (a : M.Carrier) :
    (trivializationAt (ComplexVector 1) (AntiCanonicalFiber M) a).baseSet =
      (extChartAt (ComplexModel n) a).source := rfl

@[simp] theorem tangentAntiCanonical_trivialization_baseSet (a : M.Carrier) :
    (trivializationAt (ComplexVector n) (TangentAntiCanonicalFiber M) a).baseSet =
      (extChartAt (ComplexModel n) a).source := rfl

theorem antiCanonical_trivialization_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (ℓ : AntiCanonicalFiber M x) :
    trivializationAt (ComplexVector 1) (AntiCanonicalFiber M) a ⟨x, ℓ⟩ =
      (x, antiCanonicalCoordinateEquiv a x hx ℓ) := by
  change chartCoordinatePretrivialization (AntiCanonicalFiber M)
    antiCanonicalCoordinateEquiv a ⟨x, ℓ⟩ = _
  exact chartCoordinatePretrivialization_apply _ _ a x hx ℓ

theorem tangentAntiCanonical_trivialization_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (u : TangentAntiCanonicalFiber M x) :
    trivializationAt (ComplexVector n) (TangentAntiCanonicalFiber M) a ⟨x, u⟩ =
      (x, tangentAntiCanonicalCoordinateEquiv a x hx u) := by
  change chartCoordinatePretrivialization (TangentAntiCanonicalFiber M)
    tangentAntiCanonicalCoordinateEquiv a ⟨x, u⟩ = _
  exact chartCoordinatePretrivialization_apply _ _ a x hx u

theorem antiCanonical_trivialization_symmL (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector 1) :
    (trivializationAt (ComplexVector 1) (AntiCanonicalFiber M) a).symmL ℂ x v =
      (antiCanonicalCoordinateEquiv a x hx).symm v := by
  rw [Trivialization.symmL_apply (R := ℂ) _ hx]
  change (chartCoordinatePretrivialization (AntiCanonicalFiber M)
    antiCanonicalCoordinateEquiv a).symm x v = _
  exact chartCoordinatePretrivialization_symm _ _ a x hx v

theorem tangentAntiCanonical_trivialization_symmL (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector n) :
    (trivializationAt (ComplexVector n) (TangentAntiCanonicalFiber M) a).symmL ℂ x v =
      (tangentAntiCanonicalCoordinateEquiv a x hx).symm v := by
  rw [Trivialization.symmL_apply (R := ℂ) _ hx]
  change (chartCoordinatePretrivialization (TangentAntiCanonicalFiber M)
    tangentAntiCanonicalCoordinateEquiv a).symm x v = _
  exact chartCoordinatePretrivialization_symm _ _ a x hx v

@[simp] theorem antiCanonical_localDomain (a : M.Carrier) :
    localDomain (r := 1) (AntiCanonicalFiber M) a = chartTarget a := by
  simp only [localDomain, localTriv, antiCanonical_trivialization_baseSet]
  exact Set.inter_eq_left.mpr fun z hz => (extChartAt (ComplexModel n) a).map_target hz

@[simp] theorem tangentAntiCanonical_localDomain (a : M.Carrier) :
    localDomain (r := n) (TangentAntiCanonicalFiber M) a = chartTarget a := by
  simp only [localDomain, localTriv, tangentAntiCanonical_trivialization_baseSet]
  exact Set.inter_eq_left.mpr fun z hz => (extChartAt (ComplexModel n) a).map_target hz

end Yau.NodeProofs.P03Aux
