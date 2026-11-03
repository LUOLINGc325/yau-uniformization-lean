import Yau.Proofs.C01CotangentJetAlgebra

/-! Extracting the original matrix differential Harnack expression from
the computed logarithmic-time curvature block. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem time_curvature_factor (H A D : Herm n) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) • A + ((t ^ 2 : ℝ) : ℂ) • (D + A * H⁻¹ * A) =
      ((t ^ 2 : ℝ) : ℂ) •
        (D + A * H⁻¹ * A + ((t⁻¹ : ℝ) : ℂ) • A) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp [htC]
  <;> ring

theorem matrix_harnack_of_time_curvature
    (H A D : Herm n) (hH : H.PosDef) (hA : A.IsHermitian) (hD : D.IsHermitian)
    {t : ℝ} (ht : 0 < t)
    (hcurv : ∀ v : Fin n → ℂ,
      0 ≤ (star v ⬝ᵥ (((t : ℂ) • A +
        ((t ^ 2 : ℝ) : ℂ) • (D + A * H⁻¹ * A)) *ᵥ v)).re) :
    (D + A * H⁻¹ * A + ((t⁻¹ : ℝ) : ℂ) • A).PosSemidef := by
  have hquad : (A * H⁻¹ * A).IsHermitian := by
    simpa only [hA.eq] using Matrix.isHermitian_conjTranspose_mul_mul A hH.inv.isHermitian
  have hreal : IsSelfAdjoint ((t⁻¹ : ℝ) : ℂ) := by simp [IsSelfAdjoint]
  have hB : (D + A * H⁻¹ * A + ((t⁻¹ : ℝ) : ℂ) • A).IsHermitian :=
    (hD.add hquad).add (hA.smul hreal)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hB
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hB.im_star_dotProduct_mulVec_self v).symm⟩
  have hp := hcurv v
  rw [time_curvature_factor H A D ht, Matrix.smul_mulVec, dotProduct_smul] at hp
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hp
  by_contra hfail
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos ht) (lt_of_not_ge hfail)
  exact (not_lt_of_ge hp) hneg

end Yau.NodeProofs.C01Aux
