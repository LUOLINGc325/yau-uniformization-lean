import Yau.Proofs.F01RelativeSandwichComposition

/-! Widening an actual relative Hermitian metric sandwich preserves
both orders with the same explicitly enlarged scalar constant. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem relative_matrix_sandwich_widen
    {G H : Matrix ι ι ℂ} {C D : ℝ} (hG : G.PosSemidef)
    (hC : 0 < C) (hCD : C ≤ D)
    (hH : (H - ((C⁻¹ : ℝ) : ℂ) • G).PosSemidef ∧ ((C : ℂ) • G - H).PosSemidef) :
    (H - ((D⁻¹ : ℝ) : ℂ) • G).PosSemidef ∧ ((D : ℂ) • G - H).PosSemidef := by
  have hD : 0 < D := hC.trans_le hCD
  have hInv : D⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hD hC).mpr hCD
  constructor
  · have hh := hH.1.add (hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hInv)))
    have he : H - ((D⁻¹ : ℝ) : ℂ) • G =
        (H - ((C⁻¹ : ℝ) : ℂ) • G) + (((C⁻¹ - D⁻¹ : ℝ) : ℂ) • G) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [he]
    exact hh
  · have hh := (hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hCD))).add hH.2
    have he : (D : ℂ) • G - H = (((D - C : ℝ) : ℂ) • G) + ((C : ℂ) • G - H) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [he]
    exact hh

end Yau.NodeProofs.F01Aux
