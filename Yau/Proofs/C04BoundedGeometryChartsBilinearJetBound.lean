import Mathlib

/-! A pointwise finite-jet estimate for a fixed bounded bilinear operation. -/

noncomputable section
open scoped ContDiff
namespace Yau.Proofs.C04ChartsAux
variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinear_jet_bound_flat (B : E →L[ℝ] F →L[ℝ] G)
    (f : X → E) (g : X → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (x : X) {P L : ℝ} (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hfj : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ P)
    (hgj : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ L) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * (2 : ℝ) ^ m * P * L := by
  have H := B.norm_iteratedFDeriv_le_of_bilinear hf hg x (n := m) (by simp)
  have hs : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖) ≤ (2 : ℝ) ^ m * P * L := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * P * L := by
        apply Finset.sum_le_sum
        intro i hi
        have him : i ≤ m := by simpa only [Finset.mem_range] using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        have hh := mul_le_mul (hfj i him) (hgj (m - i) (Nat.sub_le m i)) (norm_nonneg _) hP
        have hc : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg hc (sub_nonneg.mpr hh)]
      _ = (2 : ℝ) ^ m * P * L := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose m
  exact H.trans (by nlinarith [mul_nonneg (norm_nonneg B) (sub_nonneg.mpr hs)])

end Yau.Proofs.C04ChartsAux
