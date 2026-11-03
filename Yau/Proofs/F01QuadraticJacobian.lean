import Yau.Proofs.F01QuadraticJets
import Yau.LeafProofs.L17ChartNaturality

/-! Actual complex Jacobian entries and their first jets for the explicit
quadratic change of coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

def quadraticJacobian
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n)
    (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  linearMatrix (fderiv ℂ (quadraticCoordinate B) z)

theorem quadraticJacobian_zero
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n) :
    quadraticJacobian B 0 = 1 := by
  rw [quadraticJacobian, (quadraticCoordinate_hasFDerivAt_zero B).fderiv]
  ext i j
  simp [linearMatrix, stdVec, EuclideanSpace.single, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem quadraticJacobian_entry_differentiableAt
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n)
    (z : ComplexVector n) (i j : Fin n) :
    DifferentiableAt ℂ (fun w => quadraticJacobian B w i j) z := by
  have hD : ContDiffAt ℂ 1 (fderiv ℂ (quadraticCoordinate B)) z :=
    (quadraticCoordinate_contDiff B).contDiffAt.fderiv_right (by simp)
  have hh := hD.differentiableAt one_ne_zero
  exact (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiableAt.comp z
    (hh.clm_apply (differentiableAt_const (stdVec j)))

theorem quadraticJacobian_entry_fderiv
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n)
    (hB : ∀ v w, B v w = B w v) (z v : ComplexVector n) (i j : Fin n) :
    fderiv ℂ (fun w => quadraticJacobian B w i j) z v = B v (stdVec j) i := by
  have hD : ContDiffAt ℂ 1 (fderiv ℂ (quadraticCoordinate B)) z :=
    (quadraticCoordinate_contDiff B).contDiffAt.fderiv_right (by simp)
  have hh := hD.differentiableAt one_ne_zero
  change fderiv ℂ ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ) ∘
    (fun w => fderiv ℂ (quadraticCoordinate B) w (stdVec j))) z v = _
  rw [fderiv_comp z (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiableAt
    (hh.clm_apply (differentiableAt_const (stdVec j))), ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.proj, PiLp.proj_apply]
  rw [fderiv_clm_apply hh (differentiableAt_const (stdVec j))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.map_zero, zero_add]
  rw [quadraticCoordinate_secondFDeriv_of_symmetric B hB]
  have hc : fderiv ℂ (fun _ : ComplexVector n => stdVec j) z = 0 :=
    (hasFDerivAt_const (stdVec j) z).fderiv
  rw [hc]
  simp

end Yau.NodeProofs.F01Aux
