import Yau.Proofs.F01MatrixComparison

/-! Enlarging a positive comparison constant preserves both genuine
positive-semidefinite inequalities. -/
open Matrix
open scoped ComplexOrder
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_scalar_identity_posSemidef {s : ℝ} (hs : 0 ≤ s) :
    ((s : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have h : (s • (1 : Matrix ι ι ℂ)).PosSemidef := Matrix.PosSemidef.one.smul hs
  convert! h using 1

theorem matrix_sandwich_mono {H : Matrix ι ι ℂ} {D C : ℝ}
    (hD : 0 < D) (hC : 0 < C) (hDC : D ≤ C)
    (h : (H - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ ((D : ℂ) • 1 - H).PosSemidef) :
    (H - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧ ((C : ℂ) • 1 - H).PosSemidef := by
  have hInv : C⁻¹ ≤ D⁻¹ := (inv_le_inv₀ hC hD).mpr hDC
  constructor
  · have hs : (((D⁻¹ - C⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
      real_scalar_identity_posSemidef (sub_nonneg.mpr hInv)
    have hadd := h.1.add hs
    convert! hadd using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.ofReal_sub,
      smul_eq_mul]
    ring
  · have hs : (((C - D : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
      real_scalar_identity_posSemidef (sub_nonneg.mpr hDC)
    have hadd := h.2.add hs
    convert! hadd using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.ofReal_sub,
      smul_eq_mul]
    ring

end Yau.NodeProofs.F01Aux
