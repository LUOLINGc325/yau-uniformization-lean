import Yau.Proofs.F01RayleighPenalty

/-! The actual logarithmic Rayleigh supremum can absorb the small
coefficient multiplying that same supremum in the explicit Q bound. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux

theorem rayleighPenalty_le_two_mul {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    rayleighPenalty a v ≤ 2 * a * v := by
  have hp : 0 < 1 + a * v := by positivity
  have hh := Real.log_le_sub_one_of_pos hp
  unfold rayleighPenalty
  linarith

theorem bounded_range_linear_absorption {A : Type*} [Nonempty A]
    (F : A → ℝ) (hbounded : BddAbove (range F)) {q r : ℝ}
    (hq : 0 ≤ q) (hqone : q < 1) (hr : 0 ≤ r)
    (hbound : ∀ x, F x ≤ q * max 0 (sSup (range F)) + r) :
    ∀ x, F x ≤ r / (1 - q) := by
  let B := max 0 (sSup (range F))
  have hB : 0 ≤ B := le_max_left _ _
  have hrhs : 0 ≤ q * B + r := add_nonneg (mul_nonneg hq hB) hr
  have hsup : sSup (range F) ≤ q * B + r :=
    csSup_le (range_nonempty F) (by rintro y ⟨x, rfl⟩; exact hbound x)
  have hineq : B ≤ q * B + r := max_le hrhs hsup
  have hfinal : B ≤ r / (1 - q) :=
    (le_div_iff₀ (sub_pos.mpr hqone)).mpr (by nlinarith)
  intro x
  exact ((le_csSup hbounded (mem_range_self x)).trans (le_max_right 0 _)).trans hfinal

end Yau.NodeProofs.F01Aux
