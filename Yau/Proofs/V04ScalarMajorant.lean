import Yau.Proofs.V04OrderedLimits

/-! Scalar bounds for the exact smoothing function used in the frozen
spectral expression. The smoothing parameter is fixed and strictly positive. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof

def scalarMajorant (δ x : ℝ) : ℝ := δ + (x + Real.sqrt (x ^ 2 + δ ^ 2)) / 2

theorem scalarMajorant_bounds {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    δ ≤ scalarMajorant δ x ∧ x + δ ≤ scalarMajorant δ x ∧
      0 ≤ scalarMajorant δ x - max x 0 ∧
      scalarMajorant δ x - max x 0 ≤ 3 * δ / 2 := by
  have hs : 0 ≤ Real.sqrt (x ^ 2 + δ ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (x ^ 2 + δ ^ 2) ^ 2 = x ^ 2 + δ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have habs : 0 ≤ |x| := abs_nonneg x
  have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hlow : |x| ≤ Real.sqrt (x ^ 2 + δ ^ 2) := by nlinarith
  have hhigh : Real.sqrt (x ^ 2 + δ ^ 2) ≤ |x| + δ := by nlinarith
  have hxlo := neg_abs_le x
  have hxhi := le_abs_self x
  dsimp [scalarMajorant]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx]
      linarith
    · rw [max_eq_right hx]
      linarith
  · rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx] at *
      linarith
    · rw [max_eq_right hx, abs_of_nonpos hx] at *
      linarith

theorem scalarMajorant_contDiff {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (scalarMajorant δ) := by
  have hpos : ∀ x : ℝ, x ^ 2 + δ ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
  exact contDiff_const.add
    ((contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt hpos)).div_const 2)

end Yau.Blueprint.V04Proof
