import Yau.LeafProofs.L16ResidualEstimates

/-! Lowering a positive parabolic Hölder exponent costs at most a factor
two, using the actual value bound for distant pairs. No diameter bound is
needed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V]

theorem F05_holder_lower_exponent {α β C : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    {Q : Set (Point n)} {u : Point n → V} (hu : HolderBound β Q u C) :
    HolderBound α Q u (2*C) := by
  have hC := hu.1
  refine ⟨by positivity,fun p hp => (hu.2.1 p hp).trans (by linarith),?_⟩
  intro p hp q hq
  have hRaw : ‖u p-u q‖ ≤ 2*C := (norm_sub_le _ _).trans
    (by linarith [hu.2.1 p hp,hu.2.1 q hq])
  have hX := Real.rpow_nonneg (norm_nonneg (p.1-q.1)) α
  have hTime := Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)
  by_cases hx : 1 ≤ ‖p.1-q.1‖
  · have hOne := Real.one_le_rpow hx hα
    have hW : 1 ≤ holderWeight α p q := by dsimp only [holderWeight]; linarith
    exact hRaw.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hW (show 0 ≤ 2*C by positivity))
  by_cases ht : 1 ≤ |p.2-q.2|
  · have hOne := Real.one_le_rpow ht (show 0 ≤ α/2 by positivity)
    have hW : 1 ≤ holderWeight α p q := by dsimp only [holderWeight]; linarith
    exact hRaw.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hW (show 0 ≤ 2*C by positivity))
  have hWeight : holderWeight β p q ≤ holderWeight α p q :=
    add_le_add (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) (not_le.mp hx).le hα hαβ)
      (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) (not_le.mp ht).le (by positivity) (by linarith))
  exact (hu.2.2 p hp q hq).trans
    ((mul_le_mul_of_nonneg_left hWeight hC).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by dsimp only [holderWeight]; positivity)))

theorem F05_schauder_lower_exponent {α β C : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    {Q : Set (Point n)} {u : Point n → ℝ} (hu : SchauderBound β Q u C) :
    SchauderBound α Q u (2*C) := by
  refine ⟨hu.1,by linarith [hu.2.1],?_,F05_holder_lower_exponent hα hαβ hu.2.2.2.1,
    F05_holder_lower_exponent hα hαβ hu.2.2.2.2⟩
  intro p hp
  exact ⟨(hu.2.2.1 p hp).1.trans (by linarith [hu.2.1]),
    (hu.2.2.1 p hp).2.trans (by linarith [hu.2.1])⟩

end Yau.Proofs.F05Aux
