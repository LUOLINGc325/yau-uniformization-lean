import Yau.Proofs.P06SpectralClipIntervalProjection

noncomputable section
open scoped ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
variable {n : ℕ}

def metricRoot (H : Matrix (Fin n) (Fin n) ℂ) := CFC.sqrt H
def metricWhiten (H A : Matrix (Fin n) (Fin n) ℂ) := (metricRoot H)⁻¹ * A * (metricRoot H)⁻¹
def metricUnwhiten (H A : Matrix (Fin n) (Fin n) ℂ) := metricRoot H * A * metricRoot H

theorem metricRoot_hermitian (H : Matrix (Fin n) (Fin n) ℂ) : (metricRoot H).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).1

theorem metricRoot_sq (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : metricRoot H * metricRoot H = H :=
  CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg

theorem metricRoot_isUnit (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : IsUnit (metricRoot H) := by
  have hd : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have he : metricRoot H * (metricRoot H * H⁻¹) = 1 := by
    rw [← mul_assoc, metricRoot_sq H hH, Matrix.mul_nonsing_inv H hd]
  exact IsUnit.of_mul_eq_one _ he

theorem metricRoot_mul_inv (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricRoot H * (metricRoot H)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (metricRoot_isUnit H hH))

theorem metricRoot_inv_mul (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (metricRoot H)⁻¹ * metricRoot H = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (metricRoot_isUnit H hH))

theorem metricRoot_inv_sq (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (metricRoot H)⁻¹ * (metricRoot H)⁻¹ = H⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  calc
    _ = ((metricRoot H)⁻¹ * (metricRoot H)⁻¹) * (metricRoot H * metricRoot H) :=
      congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => ((metricRoot H)⁻¹ * (metricRoot H)⁻¹) * X)
        (metricRoot_sq H hH).symm
    _ = (metricRoot H)⁻¹ * ((metricRoot H)⁻¹ * metricRoot H) * metricRoot H := by simp only [mul_assoc]
    _ = 1 := by rw [metricRoot_inv_mul H hH, mul_one, metricRoot_inv_mul H hH]

theorem metricUnwhiten_whiten (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricUnwhiten H (metricWhiten H A) = A := by
  calc
    _ = (metricRoot H * (metricRoot H)⁻¹) * A * ((metricRoot H)⁻¹ * metricRoot H) := by
      simp only [metricUnwhiten, metricWhiten, mul_assoc]
    _ = A := by rw [metricRoot_mul_inv H hH, metricRoot_inv_mul H hH, one_mul, mul_one]

theorem metricWhiten_unwhiten (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricWhiten H (metricUnwhiten H A) = A := by
  calc
    _ = ((metricRoot H)⁻¹ * metricRoot H) * A * (metricRoot H * (metricRoot H)⁻¹) := by
      simp only [metricUnwhiten, metricWhiten, mul_assoc]
    _ = A := by rw [metricRoot_mul_inv H hH, metricRoot_inv_mul H hH, one_mul, mul_one]

theorem metricWhiten_hermitian (H A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (metricWhiten H A).IsHermitian := by
  have hi := (metricRoot_hermitian H).inv
  simpa only [metricWhiten, hi.eq] using Matrix.isHermitian_conjTranspose_mul_mul (metricRoot H)⁻¹ hA

theorem metricUnwhiten_hermitian (H A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (metricUnwhiten H A).IsHermitian := by
  simpa only [metricUnwhiten, (metricRoot_hermitian H).eq] using Matrix.isHermitian_conjTranspose_mul_mul (metricRoot H) hA

theorem metricWhiten_posSemidef (H A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    (metricWhiten H A).PosSemidef := by
  simpa only [metricWhiten, ((metricRoot_hermitian H).inv).eq] using hA.mul_mul_conjTranspose_same (metricRoot H)⁻¹

theorem metricUnwhiten_posSemidef (H A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    (metricUnwhiten H A).PosSemidef := by
  simpa only [metricUnwhiten, (metricRoot_hermitian H).eq] using hA.mul_mul_conjTranspose_same (metricRoot H)

end Yau.NodeProofs.P06Aux.Clip
