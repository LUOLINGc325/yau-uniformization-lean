import Yau.Proofs.F01RelativeSandwichWiden

/-! Fixed positive lower and finite upper scalar orders give one
comparison constant before every actual pair of Hermitian matrices. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_relative_sandwich_constant {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G H : Matrix ι ι ℂ), G.PosSemidef →
      (H - (a : ℂ) • G).PosSemidef → ((b : ℂ) • G - H).PosSemidef →
      (H - ((C⁻¹ : ℝ) : ℂ) • G).PosSemidef ∧ ((C : ℂ) • G - H).PosSemidef := by
  let C : ℝ := max 1 (max b a⁻¹)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hbC : b ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have haC : a⁻¹ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hInv : C⁻¹ ≤ a := by
    have hh := (inv_le_inv₀ hC0 (inv_pos.mpr ha)).mpr haC
    simpa only [inv_inv] using hh
  refine ⟨C, hC, ?_⟩
  intro G H hG hlo hhi
  constructor
  · have hh := hlo.add (hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hInv)))
    have he : H - ((C⁻¹ : ℝ) : ℂ) • G =
        (H - (a : ℂ) • G) + (((a - C⁻¹ : ℝ) : ℂ) • G) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [he]
    exact hh
  · have hh := (hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hbC))).add hhi
    have he : (C : ℂ) • G - H = (((C - b : ℝ) : ℂ) • G) + ((b : ℂ) • G - H) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [he]
    exact hh

end Yau.NodeProofs.F01Aux
