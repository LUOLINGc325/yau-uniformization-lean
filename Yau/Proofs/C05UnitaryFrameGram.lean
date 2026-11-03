import Mathlib

/-! The actual complex inverse-metric square root gives an orthonormal factor. -/
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace Yau.Proofs.C05UnitaryFrameAux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_metric_orthonormal_factor (g : Matrix ι ι ℂ) (hg : g.PosDef) :
    ∃ D : Matrix ι ι ℂ, D.det ≠ 0 ∧ g⁻¹=D*Dᴴ ∧ Dᴴ*g*D=1 := by
  let D := CFC.sqrt g⁻¹
  have hself : Dᴴ=D := by
    simpa only [sub_zero] using (CFC.sqrt_nonneg g⁻¹).isHermitian.eq
  have hD : g⁻¹=D*Dᴴ := by
    rw [hself]
    exact (CFC.sqrt_mul_sqrt_self g⁻¹ hg.posSemidef.inv.nonneg).symm
  have hdet : D.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hD
    rw [Matrix.det_mul,Matrix.det_conjTranspose,hz,zero_mul] at hh
    exact hg.inv.det_pos.ne' hh
  have hInvD : D⁻¹*D=1 := Matrix.nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hdet)
  have hInvG : g⁻¹*g=1 := Matrix.nonsing_inv_mul g
    (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  refine ⟨D,hdet,hD,?_⟩
  calc
    Dᴴ*g*D = (D⁻¹*D)*Dᴴ*g*D := by rw [hInvD,Matrix.one_mul]
    _ = D⁻¹*(D*Dᴴ)*g*D := by simp only [Matrix.mul_assoc]
    _ = D⁻¹*(g⁻¹*g)*D := by rw [←hD]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hInvG,Matrix.mul_one,hInvD]

end Yau.Proofs.C05UnitaryFrameAux
