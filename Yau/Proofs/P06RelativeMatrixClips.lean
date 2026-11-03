import Yau.Proofs.P06RelativeMatrixRoot

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
variable {n : ℕ}

theorem metricWhiten_sub (H A B : Matrix (Fin n) (Fin n) ℂ) :
    metricWhiten H (A - B) = metricWhiten H A - metricWhiten H B := by
  simp only [metricWhiten, mul_sub, sub_mul]

theorem metricUnwhiten_sub (H A B : Matrix (Fin n) (Fin n) ℂ) :
    metricUnwhiten H (A - B) = metricUnwhiten H A - metricUnwhiten H B := by
  simp only [metricUnwhiten, mul_sub, sub_mul]

theorem metricWhiten_add (H A B : Matrix (Fin n) (Fin n) ℂ) :
    metricWhiten H (A + B) = metricWhiten H A + metricWhiten H B := by
  simp only [metricWhiten, mul_add, add_mul]

theorem metricUnwhiten_add (H A B : Matrix (Fin n) (Fin n) ℂ) :
    metricUnwhiten H (A + B) = metricUnwhiten H A + metricUnwhiten H B := by
  simp only [metricUnwhiten, mul_add, add_mul]

theorem metricWhiten_smul (H A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    metricWhiten H (c • A) = c • metricWhiten H A := by
  simp only [metricWhiten, Matrix.mul_smul, Matrix.smul_mul]

theorem metricUnwhiten_smul (H A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    metricUnwhiten H (c • A) = c • metricUnwhiten H A := by
  simp only [metricUnwhiten, Matrix.mul_smul, Matrix.smul_mul]

theorem metricUnwhiten_one (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : metricUnwhiten H 1 = H := by
  simpa only [metricUnwhiten, mul_one] using metricRoot_sq H hH

theorem metricWhiten_metric (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) : metricWhiten H H = 1 := by
  calc
    _ = metricWhiten H (metricUnwhiten H 1) := congrArg (metricWhiten H) (metricUnwhiten_one H hH).symm
    _ = 1 := metricWhiten_unwhiten H 1 hH

def relativePositivePart (H A : Matrix (Fin n) (Fin n) ℂ) :=
  metricUnwhiten H (matrixPositivePart (metricWhiten H A))
def relativeIntervalClip (C : ℝ) (H A : Matrix (Fin n) (Fin n) ℂ) :=
  metricUnwhiten H (matrixIntervalClip C (metricWhiten H A))
def relativeMatrixHS (H A : Matrix (Fin n) (Fin n) ℂ) := matrixToHS (metricWhiten H A)

theorem metricWhiten_relativePositivePart (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricWhiten H (relativePositivePart H A) = matrixPositivePart (metricWhiten H A) :=
  metricWhiten_unwhiten H _ hH

theorem metricWhiten_relativeIntervalClip (C : ℝ) (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    metricWhiten H (relativeIntervalClip C H A) = matrixIntervalClip C (metricWhiten H A) :=
  metricWhiten_unwhiten H _ hH

theorem relativePositivePart_posSemidef (H A : Matrix (Fin n) (Fin n) ℂ) :
    (relativePositivePart H A).PosSemidef :=
  metricUnwhiten_posSemidef H _ (matrixPositivePart_posSemidef _)

theorem relativeIntervalClip_hermitian (C : ℝ) (H A : Matrix (Fin n) (Fin n) ℂ) :
    (relativeIntervalClip C H A).IsHermitian :=
  metricUnwhiten_hermitian H _ (matrixIntervalClip_hermitian _ _)

/-- The canonical relative clip preserves the exact original signed C
against the same Hermitian metric matrix H. -/
theorem relativeIntervalClip_bounds {C : ℝ} (hC : 0 ≤ C)
    (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian) :
    (C • H - relativeIntervalClip C H A).PosSemidef ∧
      (relativeIntervalClip C H A + C • H).PosSemidef := by
  have hb := matrixIntervalClip_bounds hC (metricWhiten H A) (metricWhiten_hermitian H A hA)
  have hu := metricUnwhiten_posSemidef H _ hb.1
  have hl := metricUnwhiten_posSemidef H _ hb.2
  rw [metricUnwhiten_sub, metricUnwhiten_smul, metricUnwhiten_one H hH] at hu
  rw [metricUnwhiten_add, metricUnwhiten_smul, metricUnwhiten_one H hH] at hl
  exact ⟨hu, hl⟩

theorem relativeIntervalClip_nonexpansive {C : ℝ} (hC : 0 ≤ C)
    (H A B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖relativeMatrixHS H (relativeIntervalClip C H A - relativeIntervalClip C H B)‖ ≤
      ‖relativeMatrixHS H (A - B)‖ := by
  simp only [relativeMatrixHS, metricWhiten_sub, metricWhiten_relativeIntervalClip C H _ hH]
  exact matrixIntervalClip_nonexpansive hC _ _ (metricWhiten_hermitian H A hA) (metricWhiten_hermitian H B hB)

theorem relativePositivePart_nonexpansive (H A B : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖relativeMatrixHS H (relativePositivePart H A - relativePositivePart H B)‖ ≤
      ‖relativeMatrixHS H (A - B)‖ := by
  simp only [relativeMatrixHS, metricWhiten_sub, metricWhiten_relativePositivePart H _ hH]
  exact matrixPositivePart_nonexpansive _ _ (metricWhiten_hermitian H A hA) (metricWhiten_hermitian H B hB)

theorem relativeIntervalClip_distance_sq {C : ℝ} (hC : 0 ≤ C)
    (H A B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian)
    (hbU : (C • H - B).PosSemidef) (hbL : (B + C • H).PosSemidef) :
    ‖relativeMatrixHS H (relativeIntervalClip C H A - B)‖ ^ 2 ≤ ‖relativeMatrixHS H (A - B)‖ ^ 2 -
      ‖relativeMatrixHS H (A - relativeIntervalClip C H A)‖ ^ 2 := by
  have hU := metricWhiten_posSemidef H _ hbU
  have hL := metricWhiten_posSemidef H _ hbL
  rw [metricWhiten_sub, metricWhiten_smul, metricWhiten_metric H hH] at hU
  rw [metricWhiten_add, metricWhiten_smul, metricWhiten_metric H hH] at hL
  simp only [relativeMatrixHS, metricWhiten_sub, metricWhiten_relativeIntervalClip C H _ hH]
  exact matrixIntervalClip_distance_sq hC _ _ (metricWhiten_hermitian H A hA) hU hL

theorem metricWhiten_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    metricWhiten H 0 = 0 := by simp only [metricWhiten, mul_zero, zero_mul]

theorem metricUnwhiten_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    metricUnwhiten H 0 = 0 := by simp only [metricUnwhiten, mul_zero, zero_mul]

theorem relativeIntervalClip_zero {C : ℝ} (hC : 0 ≤ C)
    (H : Matrix (Fin n) (Fin n) ℂ) : relativeIntervalClip C H 0 = 0 := by
  rw [relativeIntervalClip, metricWhiten_zero, matrixIntervalClip_zero hC,
    metricUnwhiten_zero]

theorem relativePositivePart_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    relativePositivePart H 0 = 0 := by
  rw [relativePositivePart, metricWhiten_zero, matrixPositivePart_zero,
    metricUnwhiten_zero]

theorem relativePositivePart_eq_self (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.PosSemidef) : relativePositivePart H A = A := by
  rw [relativePositivePart,
    matrixPositivePart_eq_self _ (metricWhiten_posSemidef H A hA),
    metricUnwhiten_whiten H A hH]

theorem relativeIntervalClip_eq_self {C : ℝ} (hC : 0 ≤ C)
    (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian)
    (hU : (C • H - A).PosSemidef) (hL : (A + C • H).PosSemidef) :
    relativeIntervalClip C H A = A := by
  have hUw := metricWhiten_posSemidef H _ hU
  have hLw := metricWhiten_posSemidef H _ hL
  rw [metricWhiten_sub, metricWhiten_smul, metricWhiten_metric H hH] at hUw
  rw [metricWhiten_add, metricWhiten_smul, metricWhiten_metric H hH] at hLw
  rw [relativeIntervalClip,
    matrixIntervalClip_eq_self hC _ (metricWhiten_hermitian H A hA) hUw hLw,
    metricUnwhiten_whiten H A hH]

theorem relativePositivePart_distance_sq
    (H A B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    ‖relativeMatrixHS H (relativePositivePart H A - B)‖ ^ 2 ≤
      ‖relativeMatrixHS H (A - B)‖ ^ 2 -
        ‖relativeMatrixHS H (A - relativePositivePart H A)‖ ^ 2 := by
  simp only [relativeMatrixHS, metricWhiten_sub,
    metricWhiten_relativePositivePart H _ hH]
  exact matrixPositivePart_distance_sq _ _ (metricWhiten_hermitian H A hA)
    (metricWhiten_posSemidef H B hB)

end Yau.NodeProofs.P06Aux.Clip
