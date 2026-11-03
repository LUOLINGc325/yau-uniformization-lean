import Yau.Proofs.F01CoordinateBilinear
import Yau.Proofs.F01QuadraticWirtingerJet
import Yau.Proofs.F01QuadraticLocalChart
import Yau.Proofs.F01WirtingerIdentityFrame

/-! An explicit quadratic coordinate correction cancels the actual
holomorphic first metric jet. Its coefficients are computed from that jet. -/
noncomputable section
open scoped Matrix ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

def normalCoordinateCorrection (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) :
    ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n :=
  coordinateBilinear (fun i j k => -wirt (fun y => G y i j) 0 (stdVec k))

theorem normalCoordinateCorrection_symmetric
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hsym : ∀ i j k, wirt (fun y => G y i j) 0 (stdVec k) =
      wirt (fun y => G y i k) 0 (stdVec j)) (v w : ComplexVector n) :
    normalCoordinateCorrection G v w = normalCoordinateCorrection G w v := by
  apply coordinateBilinear_symmetric
  intro i j k
  exact congrArg Neg.neg (hsym i j k)

theorem normalCoordinateCorrection_basis
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (i j k : Fin n) :
    normalCoordinateCorrection G (stdVec k) (stdVec j) i =
      -wirt (fun y => G y i k) 0 (stdVec j) := by
  rw [normalCoordinateCorrection, coordinateBilinear_coordinate]
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem quadratic_normal_jet_zero
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) 0)
    (hG0 : G 0 = 1)
    (hsym : ∀ i j k, wirt (fun y => G y i j) 0 (stdVec k) =
      wirt (fun y => G y i k) 0 (stdVec j)) (i j k : Fin n) :
    let B := normalCoordinateCorrection G
    wirt (fun w => ((quadraticJacobian B w)ᴴ * G (quadraticCoordinate B w) *
      quadraticJacobian B w) i j) 0 (stdVec k) = 0 := by
  let B := normalCoordinateCorrection G
  have hB : ∀ v w, B v w = B w v := normalCoordinateCorrection_symmetric G hsym
  have hQ : DifferentiableAt ℂ (quadraticCoordinate B) 0 :=
    (quadraticCoordinate_contDiff B).differentiable (by simp) 0
  have hGQ (p q : Fin n) :
      DifferentiableAt ℝ (fun w => G (quadraticCoordinate B w) p q) 0 := by
    have h := hG p q
    rw [← quadraticCoordinate_zero B] at h
    exact h.comp 0 (hQ.restrictScalars ℝ)
  have hGQ0 : G (quadraticCoordinate B 0) = 1 := by rw [quadraticCoordinate_zero, hG0]
  have h := wirt_congruence_at_identity (quadraticJacobian B)
    (fun w => G (quadraticCoordinate B w)) 0 (stdVec k)
    (quadraticJacobian_entry_differentiableAt B 0) hGQ (quadraticJacobian_zero B) hGQ0 i j
  rw [wirt_comp_complex_differentiable (quadraticCoordinate B) (fun y => G y i j)
    0 (stdVec k) hQ (by simpa only [quadraticCoordinate_zero] using hG i j),
    (quadraticCoordinate_hasFDerivAt_zero B).fderiv, ContinuousLinearMap.id_apply,
    quadraticCoordinate_zero, quadraticJacobian_entry_wirt B hB,
    normalCoordinateCorrection_basis, ← hsym i j k] at h
  simpa only [add_neg_cancel] using h

end Yau.NodeProofs.F01Aux
