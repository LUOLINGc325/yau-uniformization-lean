import Mathlib

/-! A quantitative clock barrier. Its time radius is independent of every
spatial radius introduced later. -/

noncomputable section
open Set
namespace Yau.Proofs.C04RescaledTubeAux

theorem primitive_increment_le {s d : ℝ → ℝ} {u v B : ℝ}
    (huv : u ≤ v) (hd : ∀ t ∈ Icc u v, HasDerivAt s (d t) t)
    (hb : ∀ t ∈ Icc u v, d t ≤ B) : s v - s u ≤ B * (v - u) := by
  apply (convex_Icc u v).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact hb t (interior_subset ht))
    u ⟨le_rfl, huv⟩ v ⟨huv, le_rfl⟩ huv

/-- Endpoints of a clock window lie beyond a fixed rescaled time interval.
The derivative bound is needed only where the physical time is at least half
the central time. -/
theorem clock_window_time_barrier {s d : ℝ → ℝ} {L t H R δ B m : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hhalf : δ / R < t / 2) (hLt : L ≤ t) (htH : t ≤ H)
    (hleft : m ≤ s t - s L) (hright : m ≤ s H - s t)
    (hmargin : B * δ < m)
    (hd : ∀ u ∈ Icc L H, HasDerivAt s (d u) u)
    (hb : ∀ u ∈ Icc L H, t / 2 ≤ u → d u ≤ B * R) :
    L < t - δ / R ∧ t + δ / R < H := by
  have hδR : 0 < δ / R := div_pos hδ hR
  have hcancel : R * (δ / R) = δ := mul_div_cancel₀ δ hR.ne'
  constructor
  · by_contra hn
    have hL : t - δ / R ≤ L := le_of_not_gt hn
    have hinc := primitive_increment_le hLt
      (fun u hu => hd u ⟨hu.1, hu.2.trans htH⟩)
      (fun u hu => hb u ⟨hu.1, hu.2.trans htH⟩ (by have huL := hu.1; linarith))
    have hdist : t - L ≤ δ / R := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdist (mul_nonneg hB hR.le)
    have heq : B * R * (δ / R) = B * δ := by rw [mul_assoc, hcancel]
    rw [heq] at hmul
    linarith
  · by_contra hn
    have hH : H ≤ t + δ / R := le_of_not_gt hn
    have hinc := primitive_increment_le htH
      (fun u hu => hd u ⟨hLt.trans hu.1, hu.2⟩)
      (fun u hu => hb u ⟨hLt.trans hu.1, hu.2⟩ (by have htu := hu.1; linarith))
    have hdist : H - t ≤ δ / R := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdist (mul_nonneg hB hR.le)
    have heq : B * R * (δ / R) = B * δ := by rw [mul_assoc, hcancel]
    rw [heq] at hmul
    linarith

end Yau.Proofs.C04RescaledTubeAux
