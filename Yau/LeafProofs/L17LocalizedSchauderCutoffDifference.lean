import Yau.LeafProofs.L17LocalizedSchauderTransitionBudget
import Yau.LeafProofs.L17LocalizedSchauderCompositionDifference

open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The next actual derivative controls finite jet differences on a convex set. -/
theorem iteratedFDeriv_sub_le_on_convex {U : Set E} (hU : IsOpen U) (hConv : Convex ℝ U)
    {f : E → F} {k : ℕ} (hf : ContDiffOn ℝ ((k+1 : ℕ) : ℕ∞ω) f U)
    {C : ℝ} (hBound : ∀ z ∈ U, ‖iteratedFDeriv ℝ (k+1) f z‖ ≤ C)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ k f x-iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖ := by
  have hDiff : ∀ z ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    intro z hz
    exact (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  have hDeriv : ∀ z ∈ U, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖ ≤ C := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hBound z hz
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hDeriv hConv hy hx

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The cutoff jet bound is a genuine scaled derivative bound, not a supplied
Hölder bound. Only the next derivative is used. -/
theorem unitCutoff_iteratedFDeriv_sub_le (P : UniformChartPartition g)
    (hρr : 2*P.radius < P.charts.radius) (p : P.centers) (q : M.Carrier)
    {k : ℕ} {C : ℝ}
    (hBound : ∀ z ∈ ball (0 : ComplexVector n) 2,
      ‖iteratedFDeriv ℝ (k+1) (unitCutoff P p q) z‖ ≤ C)
    {x y : ComplexVector n} (hx : x ∈ ball 0 2) (hy : y ∈ ball 0 2) :
    ‖iteratedFDeriv ℝ k (unitCutoff P p q) x-
      iteratedFDeriv ℝ k (unitCutoff P p q) y‖ ≤ C*‖x-y‖ :=
  iteratedFDeriv_sub_le_on_convex isOpen_ball (convex_ball _ _)
    ((unitCutoff_contDiffOn P hρr p q).of_le (by simp)) hBound hx hy

end Yau.LeafProofs.L17LocalizedSchauderAux
