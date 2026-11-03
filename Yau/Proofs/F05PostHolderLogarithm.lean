import Yau.LeafProofs.L16Normalization

/-! On nonnegative scalar values the exponential expands distances.
Consequently the value Holder budget for exp(w) already bounds w itself. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_nonnegative_exp_ordered_gap {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y-x ≤ Real.exp y-Real.exp x := by
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hStep : y-x ≤ Real.exp (y-x)-1 := by linarith [Real.add_one_le_exp (y-x)]
  have hExp : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hProduct : Real.exp (y-x)-1 ≤ Real.exp x*(Real.exp (y-x)-1) :=
    le_mul_of_one_le_left (by linarith) hExp
  have hIdentity : Real.exp x*Real.exp (y-x) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

theorem F05_nonnegative_exp_gap {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x-y| ≤ |Real.exp x-Real.exp y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy))]
    linarith [F05_nonnegative_exp_ordered_gap hx hxy]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hyx))]
    exact F05_nonnegative_exp_ordered_gap hy hyx

theorem F05_nonnegative_log_value_holder {α C : ℝ} {Q : Set (Point n)}
    {w : Point n → ℝ} (hw : HolderBound α Q (fun p => Real.exp (w p)) C)
    (hNonneg : ∀ p ∈ Q, 0 ≤ w p) : HolderBound α Q w C := by
  refine ⟨hw.1,?_,?_⟩
  · intro p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (hNonneg p hp)]
    have hSup : Real.exp (w p) ≤ C := by
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hw.2.1 p hp
    linarith [Real.add_one_le_exp (w p)]
  · intro p hp q hq
    have hGap := F05_nonnegative_exp_gap (hNonneg p hp) (hNonneg q hq)
    simpa only [Real.norm_eq_abs] using hGap.trans (hw.2.2 p hp q hq)

end Yau.Proofs.F05Aux
