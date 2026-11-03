import Yau.Proofs.P03DeterminantFibres

open scoped Manifold Topology TensorProduct

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

def scalarLineEquiv : ℂ ≃L[ℂ] ComplexVector 1 :=
  (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)).symm

@[simp] theorem scalarLineEquiv_apply (c : ℂ) (i : Fin 1) :
    scalarLineEquiv c i = c := rfl

def canonicalCoordinateEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    CanonicalFiber M x ≃L[ℂ] ComplexVector 1 :=
  (canonicalScalarEquiv a x hx).trans scalarLineEquiv

def antiCanonicalCoordinateEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    AntiCanonicalFiber M x ≃L[ℂ] ComplexVector 1 :=
  (antiCanonicalScalarEquiv a x hx).trans scalarLineEquiv

@[simp] theorem antiCanonicalCoordinateEquiv_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (ℓ : AntiCanonicalFiber M x) (i : Fin 1) :
    antiCanonicalCoordinateEquiv a x hx ℓ i = ℓ (chartTopForm a x hx) := rfl

/-- Coordinates of the actual tensor fibre, using only the tensor universal property. -/
def tangentAntiCanonicalCoordinateLinearEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    TangentAntiCanonicalFiber M x ≃ₗ[ℂ] ComplexVector n :=
  (TensorProduct.congr (chartFrameEquiv a x hx).symm.toLinearEquiv
    (antiCanonicalScalarEquiv a x hx).toLinearEquiv).trans
      (TensorProduct.rid ℂ (ComplexVector n))

@[simp] theorem tangentAntiCanonicalCoordinateLinearEquiv_tmul (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (v : TangentVector M x) (ℓ : AntiCanonicalFiber M x) :
    tangentAntiCanonicalCoordinateLinearEquiv a x hx (v ⊗ₜ[ℂ] ℓ) =
      ℓ (chartTopForm a x hx) • tangentCoords a x v := rfl

@[simp] theorem tangentAntiCanonicalCoordinateLinearEquiv_symm (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector n) :
    (tangentAntiCanonicalCoordinateLinearEquiv a x hx).symm v =
      chartVec a x v ⊗ₜ[ℂ] chartTopEvaluation a x hx := by
  apply (tangentAntiCanonicalCoordinateLinearEquiv a x hx).injective
  simp only [LinearEquiv.apply_symm_apply,
    tangentAntiCanonicalCoordinateLinearEquiv_tmul, chartTopEvaluation_topForm,
    tangentCoords_chartVec a x hx, one_smul]

theorem canonicalFiber_finrank (x : M.Carrier) :
    Module.finrank ℂ (CanonicalFiber M x) = 1 := by
  simpa using (canonicalScalarEquiv x x (mem_extChartAt_source x)).toLinearEquiv.finrank_eq

theorem antiCanonicalFiber_finrank (x : M.Carrier) :
    Module.finrank ℂ (AntiCanonicalFiber M x) = 1 := by
  simpa using (antiCanonicalScalarEquiv x x (mem_extChartAt_source x)).toLinearEquiv.finrank_eq

theorem tangentAntiCanonicalFiber_finrank (x : M.Carrier) :
    Module.finrank ℂ (TangentAntiCanonicalFiber M x) = n := by
  simpa using
    (tangentAntiCanonicalCoordinateLinearEquiv x x (mem_extChartAt_source x)).finrank_eq

end Yau.NodeProofs.P03Aux
