import Yau.LeafProofs.L05LogDetCalculus
import Yau.LeafProofs.L05ABPAlgebra

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def symInverse {n : ℕ} (A : Sym n) : Sym n :=
  ⟨(A : Mat n)⁻¹,Matrix.isHermitian_iff_isSelfAdjoint.mp
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property).inv⟩

theorem posDef_inv_sqrt_conjugate {n : ℕ} {A : Mat n} (hA : A.PosDef) :
    CFC.sqrt A⁻¹*A*CFC.sqrt A⁻¹=1 := by
  let R := CFC.sqrt A⁻¹
  have hRR : R*R=A⁻¹ := by
    exact CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hRdet : R.det ≠ 0 := by
    intro hzero
    have hd := congrArg Matrix.det hRR
    rw [Matrix.det_mul,hzero,zero_mul] at hd
    exact hA.inv.det_pos.ne' hd.symm
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  change R*A*R=1
  calc
    R*A*R=(R⁻¹*R)*(R*A*R) := by rw [Matrix.nonsing_inv_mul R hRu,one_mul]
    _=R⁻¹*((R*R)*A)*R := by simp only [Matrix.mul_assoc]
    _=R⁻¹*(A⁻¹*A)*R := by rw [hRR]
    _=R⁻¹*R := by rw [Matrix.nonsing_inv_mul A hAu,Matrix.mul_one]
    _=1 := Matrix.nonsing_inv_mul R hRu

theorem symInverse_mem_slopeSet {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A : Sym n} (hA : A ∈ slopeSet n ell L) :
    symInverse A ∈ slopeSet n L⁻¹ ell⁻¹ := by
  have hAp := slopeSet_posDef hell hA
  have hLp : 0 < L := hell.trans_le hL
  let R := CFC.sqrt (A : Mat n)⁻¹
  have hRP : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hRstar : R.conjTranspose=R := hRP.isHermitian.eq
  have hRR : R*R=(A : Mat n)⁻¹ := CFC.sqrt_mul_sqrt_self _ hAp.inv.posSemidef.nonneg
  have hRAR : R*(A : Mat n)*R=1 := posDef_inv_sqrt_conjugate hAp
  have hlow : ((1 : Mat n)-ell • (A : Mat n)⁻¹).PosSemidef := by
    convert! hA.1.conjTranspose_mul_mul_same R using 1
    rw [hRstar,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hRAR,hRR]
  have hupp : (L • (A : Mat n)⁻¹-(1 : Mat n)).PosSemidef := by
    convert! hA.2.conjTranspose_mul_mul_same R using 1
    rw [hRstar,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hRAR,hRR]
  constructor
  · convert! hupp.smul (inv_nonneg.mpr hLp.le) using 1
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hLp.ne',one_smul]
    rfl
  · convert! hlow.smul (inv_nonneg.mpr hell.le) using 1
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hell.ne',one_smul]
    rfl

theorem symInverse_norm_le {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A : Sym n} (hA : A ∈ slopeSet n ell L) :
    ‖(A : Mat n)⁻¹‖ ≤ (2*n)*ell⁻¹ := by
  change ‖symInverse A‖ ≤ (2*n)*ell⁻¹
  exact slopeSet_norm_le (ell := L⁻¹) (L := ell⁻¹)
    (inv_nonneg.mpr (hell.trans_le hL).le) (symInverse_mem_slopeSet hell hL hA)

theorem inverse_sub_identity {n : ℕ} {A B : Mat n}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) : A⁻¹-B⁻¹=A⁻¹*(B-A)*B⁻¹ := by
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_nonsing_inv_cancel_right B A⁻¹
    (isUnit_iff_ne_zero.mpr hB),Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mul]

end Yau.LeafProofs.L05Aux
