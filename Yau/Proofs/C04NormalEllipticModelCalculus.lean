import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Linear, bilinear, additive, and finite-sum jet bounds on one open set. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem normal_elliptic_linear_jet (T : E →L[ℝ] F) {f : D → E} {U : Set D}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => T (f y)) x‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ m f x‖ := by
  have hh := T.norm_iteratedFDerivWithin_comp_left (hf x hx) hU.uniqueDiffOn hx
    (by simp : (m : ℕ∞ω) ≤ ∞)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hh
  exact hh

theorem normal_elliptic_bilinear_jet (T : E →L[ℝ] F →L[ℝ] G)
    {f : D → E} {g : D → F} {U : Set D}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    {x : D} (hx : x ∈ U) (P Q : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (hpf : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ P j)
    (hqg : ∀ j, ‖iteratedFDeriv ℝ j g x‖ ≤ Q j) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => T (f y) (g y)) x‖ ≤
      ‖T‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * P i * Q (m - i) := by
  have hh := T.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx
    (by simp : (m : ℕ∞ω) ≤ ∞)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hpf i) (Nat.cast_nonneg _)) (hqg _)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hP i))

theorem normal_elliptic_add_jet {f g : D → E} {U : Set D}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  have hh := fun_iteratedFDerivWithin_add_apply
    ((hf x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    ((hg x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hU.uniqueDiffOn hx
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hh
  rw [hh]
  exact norm_add_le _ _

theorem normal_elliptic_sum_jet {ι : Type*} (s : Finset ι) (f : ι → D → E)
    {U : Set D} (hf : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) U) (hU : IsOpen U)
    {x : D} (hx : x ∈ U) (m : ℕ) (C : ι → ℝ)
    (hbound : ∀ i ∈ s, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C i) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ i ∈ s, f i y) x‖ ≤ ∑ i ∈ s, C i := by
  have hh := iteratedFDerivWithin_fun_sum_apply hU.uniqueDiffOn hx
    (fun i hi => ((hf i hi) x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hh
  rw [hh]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hbound)

end Yau.Proofs.C04Aux
