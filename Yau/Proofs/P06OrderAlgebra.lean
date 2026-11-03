import Yau.Proofs.P06Geometry

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

theorem matrix_trace_mul_nonneg {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  let C := CFC.sqrt B
  have hC : C.IsHermitian :=
    ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg B)).1
  have hsq : C * C = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hpos := hA.mul_mul_conjTranspose_same C
  rw [hC.eq] at hpos
  have htr := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  have heq : Matrix.trace (C * A * C) = Matrix.trace (A * B) := by
    rw [Matrix.trace_mul_cycle, hsq, Matrix.trace_mul_comm]
  rwa [heq] at htr

/-- The Hermitian positive cone is self-dual for the actual real trace
pairing, with rank-one tests proving the reverse implication. -/
theorem matrix_posSemidef_iff_trace_tests {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ B : Matrix (Fin n) (Fin n) ℂ, B.PosSemidef →
      0 ≤ (Matrix.trace (A * B)).re := by
  constructor
  · exact fun hp B hB => matrix_trace_mul_nonneg A B hp hB
  · intro htest
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hA.im_star_dotProduct_mulVec_self v).symm⟩
    have h := htest (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
    simpa only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using h

theorem matrix_posSemidef_iff_metric_trace_tests {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ B : Matrix (Fin n) (Fin n) ℂ, B.PosSemidef →
      0 ≤ (Matrix.trace (H⁻¹ * A * H⁻¹ * B)).re := by
  have hi : H⁻¹.IsHermitian := hH.inv.isHermitian
  have hQ : (H⁻¹ * A * H⁻¹).IsHermitian := by
    simpa only [hi.eq] using Matrix.isHermitian_conjTranspose_mul_mul H⁻¹ hA
  have hconj : (H⁻¹ * A * H⁻¹).PosSemidef ↔ A.PosSemidef := by
    have hu : IsUnit H⁻¹ := hH.inv.isUnit
    simpa only [hi.star_eq] using Matrix.IsUnit.posSemidef_star_left_conjugate_iff hu (x := A)
  exact hconj.symm.trans (matrix_posSemidef_iff_trace_tests _ hQ)

variable {n : ℕ} {M : ComplexManifold n}

theorem formHermitianMatrix_zero (x : M.Carrier) :
    formHermitianMatrix (0 : RealForm M 2) x = 0 := by
  ext a b
  simp [formHermitianMatrix]

/-- The actual form metric pairs the positive (1,1) cone nonnegatively.
The inverse metric factors and the paper normalization are retained. -/
theorem formInner_nonnegative_oneOne (g : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (hAp : FormLE 0 A) (hBp : FormLE 0 B)
    (x : M.Carrier) : 0 ≤ formInner g A B x := by
  have hAx : (formHermitianMatrix A x).PosSemidef := by
    simpa only [formHermitianMatrix_zero, sub_zero] using hAp x
  have hBx : (formHermitianMatrix B x).PosSemidef := by
    simpa only [formHermitianMatrix_zero, sub_zero] using hBp x
  have hH := Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have hQ := hAx.mul_mul_conjTranspose_same ((gMat g x)⁻¹)
  have hh : ((gMat g x)⁻¹).IsHermitian := hH.inv.isHermitian
  rw [hh.eq] at hQ
  rw [G04Aux.formInner_oneOne g A B hA hB x]
  exact matrix_trace_mul_nonneg _ _ hQ hBx

end Yau.NodeProofs.P06Aux
