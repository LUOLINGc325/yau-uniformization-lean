import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Uniform Taylor estimates used for the local Holder graph. -/

noncomputable section
open Set Metric Filter Asymptotics
open scoped Topology

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform second derivative bound controls the actual first Taylor remainder.
The deliberately loose constant avoids any integration convention. -/
theorem norm_taylor_remainder_le
    {s : Set E} (hs : Convex ℝ s) {f : E → F}
    {f' : E → E →L[ℝ] F} {f'' : E → E →L[ℝ] E →L[ℝ] F}
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hf' : ∀ x ∈ s, HasFDerivAt f' (f'' x) x)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ s, ‖f'' x‖ ≤ C)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - f' x (y-x)‖ ≤ C * ‖y-x‖^2 := by
  have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hfirst : ∀ z ∈ segment ℝ x y, ‖f' z-f' x‖ ≤ C*‖y-x‖ := by
    intro z hz
    exact (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw => (hf' w hw).hasFDerivWithinAt) hbound hs hx (hseg hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hC)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z-f' x z) (f' := fun z => f' z-f' x)
    (fun z hz => ((hf z (hseg hz)).sub (f' x).hasFDerivAt).hasFDerivWithinAt)
    hfirst (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : (f y-f' x y)-(f x-f' x x) = f y-f x-f' x (y-x) := by
    rw [map_sub]
    abel
  rw [heq] at h
  simpa only [pow_two, mul_assoc] using h

/-- An actual quadratic norm remainder gives a Frechet derivative. -/
theorem hasFDerivAt_of_quadratic_remainder {f : E → F} {A : E →L[ℝ] F}
    {x : E} {C : ℝ}
    (h : ∀ᶠ y in 𝓝 x, ‖f y-f x-A (y-x)‖ ≤ C*‖y-x‖^2) :
    HasFDerivAt f A x := by
  rw [hasFDerivAt_iff_isLittleO]
  exact (IsBigO.of_bound C (by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using h)).trans_isLittleO
    (isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ)))

end Yau.LeafProofs.L17BootstrapHolderTaylorAux
