import Yau.Proofs.C01MatrixHarnack

/-! The coefficient of the actual moving frame preserves metric norm
and turns the matrix Harnack inequality into monotonicity along that frame. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem moving_frame_adjoint (H A : Herm n)
    (hH : H.IsHermitian) (hA : A.IsHermitian) :
    (((1 / 2 : ℂ) • (H⁻¹ * A))ᴴ) = (1 / 2 : ℂ) • (A * H⁻¹) := by
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hA.eq, hH.inv.eq]

theorem moving_frame_metric_cancellation (H A : Herm n)
    (hH : H.PosDef) (hA : A.IsHermitian) :
    let M : Herm n := (1 / 2 : ℂ) • (H⁻¹ * A)
    Mᴴ * H + -A + H * M = 0 := by
  dsimp only
  have hunit : IsUnit H.det := hH.isUnit.map Matrix.detMonoidHom
  have hl : (((1 / 2 : ℂ) • (H⁻¹ * A))ᴴ) * H = (1 / 2 : ℂ) • A := by
    rw [moving_frame_adjoint H A hH.isHermitian hA, smul_mul_assoc,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul H hunit, Matrix.mul_one]
  have hr : H * ((1 / 2 : ℂ) • (H⁻¹ * A)) = (1 / 2 : ℂ) • A := by
    rw [mul_smul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv H hunit, Matrix.one_mul]
  rw [hl, hr]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply,
    smul_eq_mul]
  ring

theorem moving_frame_ricci_cancellation (H A : Herm n)
    (hH : H.IsHermitian) (hA : A.IsHermitian) :
    let M : Herm n := (1 / 2 : ℂ) • (H⁻¹ * A)
    Mᴴ * A + A * M = A * H⁻¹ * A := by
  dsimp only
  rw [moving_frame_adjoint H A hH hA, smul_mul_assoc, mul_smul_comm, ← Matrix.mul_assoc]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem moving_frame_harnack_factor (H A D : Herm n)
    (hH : H.IsHermitian) (hA : A.IsHermitian) {t : ℝ} (ht : 0 < t) :
    let M : Herm n := (1 / 2 : ℂ) • (H⁻¹ * A)
    (t : ℂ) • (D + (Mᴴ * A + A * M)) + A =
      (t : ℂ) • (D + A * H⁻¹ * A + ((t⁻¹ : ℝ) : ℂ) • A) := by
  dsimp only
  rw [moving_frame_ricci_cancellation H A hH hA]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp [htC]
  <;> ring

end Yau.NodeProofs.C01Aux
