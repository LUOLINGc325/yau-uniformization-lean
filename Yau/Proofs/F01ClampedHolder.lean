import Yau.Geometry.ParabolicCalculus
import Yau.Proofs.F01ClampedTimeContinuity

/-! Clamping the actual time variable preserves the original parabolic
Hölder constant on the larger slab. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V]

theorem abs_time_clamp_sub_le (s t : ℝ) : |max s 0 - max t 0| ≤ |s - t| := by
  by_cases hs : s ≤ 0
  · by_cases ht : t ≤ 0
    · simp only [max_eq_right hs, max_eq_right ht, sub_self, abs_zero, abs_nonneg]
    · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
      rw [max_eq_right hs, max_eq_left ht0, zero_sub, abs_neg, abs_of_nonneg ht0,
        abs_of_nonpos (by linarith : s - t ≤ 0)]
      linarith
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    by_cases ht : t ≤ 0
    · rw [max_eq_left hs0, max_eq_right ht, sub_zero, abs_of_nonneg hs0,
        abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith
    · simp only [max_eq_left hs0, max_eq_left (lt_of_not_ge ht).le, le_refl]

theorem holderBound_time_clamp {F : Point n → V} {S : Set (Space n)}
    {a T γ C : ℝ} (hT : 0 ≤ T) (hγ : 0 ≤ γ)
    (hF : HolderBound γ (S ×ˢ Icc 0 T) F C) :
    HolderBound γ (S ×ˢ Icc a T) (fun p : Point n => F (p.1, max p.2 0)) C := by
  have hmap : MapsTo (fun p : Point n => (p.1, max p.2 0))
      (S ×ˢ Icc a T) (S ×ˢ Icc 0 T) := fun p hp =>
    ⟨hp.1, le_max_right _ _, max_le hp.2.2 hT⟩
  refine ⟨hF.1, (fun p hp => hF.2.1 _ (hmap hp)), ?_⟩
  intro p hp q hq
  refine (hF.2.2 _ (hmap hp) _ (hmap hq)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hF.1
  unfold holderWeight
  exact add_le_add le_rfl (Real.rpow_le_rpow (abs_nonneg _)
    (abs_time_clamp_sub_le p.2 q.2) (div_nonneg hγ (by norm_num)))

end Yau.NodeProofs.F01Aux
