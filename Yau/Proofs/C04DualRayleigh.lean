import Yau.Proofs.C04DualLogRate
import Yau.Proofs.C04RayleighScaling

/-! The logarithmic dual rate is the actual primal Ricci Rayleigh quotient. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint Matrix

variable {n : ℕ}

theorem matrixForm_inverse_primal (H : Herm n) (hH : H.PosDef) (w : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm H⁻¹ (H *ᵥ w) =
      Blueprint.Alignment.Y03Proof.matrixForm H w := by
  change realMatrixPairing H⁻¹ (H *ᵥ w) (H *ᵥ w) = realMatrixPairing H w w
  rw [realMatrixPairing_conjugate, hH.isHermitian.eq,
    Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom), Matrix.one_mul]

theorem matrixForm_inverse_ricci_primal (H R : Herm n) (hH : H.PosDef) (w : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm (H⁻¹ * R * H⁻¹) (H *ᵥ w) =
      Blueprint.Alignment.Y03Proof.matrixForm R w := by
  change realMatrixPairing (H⁻¹ * R * H⁻¹) (H *ᵥ w) (H *ᵥ w) = realMatrixPairing R w w
  rw [realMatrixPairing_conjugate, hH.isHermitian.eq]
  have hd := hH.isUnit.map Matrix.detMonoidHom
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv H hd, Matrix.one_mul,
    Matrix.nonsing_inv_mul H hd, Matrix.mul_one]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul H hd, Matrix.mul_one]

theorem ricciMin_lower_of_dual_rates (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (t b : ℝ)
    (hdual : ∀ v : Fin n → ℂ, v ≠ 0 → b ≤ dualClockRate h o v t) :
    b ≤ ricciMin o h t := by
  letI := nonzero_complexVector_nonempty (dimension_pos X.manifold)
  have hH : (gMat (h t) o).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h t) o (chartPt o o) (mem_extChartAt_target o)
  apply le_ciInf
  intro w
  have hw : WithLp.ofLp w.1 ≠ 0 := by
    intro hz
    apply w.2
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_zero] using hz
  have hv : gMat (h t) o *ᵥ WithLp.ofLp w.1 ≠ 0 := by
    intro hz
    apply hw
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hH.isUnit)
    simpa only [Matrix.mulVec_zero] using hz
  have hh := hdual _ hv
  dsimp only [dualClockRate, dualNumerator, dualValue] at hh
  rw [matrixForm_inverse_primal _ hH, matrixForm_inverse_ricci_primal _ _ hH] at hh
  change b ≤ matrixQuadratic ((t : ℂ) • ricci (h t) o) w.1 /
    matrixQuadratic (gMat (h t) o) w.1
  rw [matrixQuadratic_real_smul]
  exact hh

end Yau.Proofs.C04Aux
