import Yau.LeafProofs.L17LocalizedSchauderDerivativeNorms
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def bilinearJetConstant (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)

theorem bilinearJetConstant_nonneg (k : ℕ) : 0 ≤ bilinearJetConstant k := by
  exact Finset.sum_nonneg (fun j hj => Nat.cast_nonneg _)

theorem norm_iteratedFDeriv_bilinear_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) (f : E → F) (g : E → G)
    (hf : ContDiffOn ℝ (k : ℕ∞ω) f U) (hg : ContDiffOn ℝ (k : ℕ∞ω) g U)
    {x : E} (hx : x ∈ U) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hF : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hG : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x‖ ≤ ‖B‖*bilinearJetConstant k*A*D := by
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx
    (by simp : (k : ℕ) ≤ (k : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  apply h.trans
  calc
    _ ≤ ‖B‖*∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*A*D := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF j hjk) (Nat.cast_nonneg _))
        (hG (k-j) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      simp only [bilinearJetConstant,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end Yau.LeafProofs.L17LocalizedSchauderAux
