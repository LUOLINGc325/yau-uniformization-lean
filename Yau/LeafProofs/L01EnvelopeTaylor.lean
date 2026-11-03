import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

open Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable gradient supplies a symmetric second Peano expansion at that point. -/
theorem second_peano_of_gradient_hasFDerivAt
    (H : E → ℝ) (P : E → E)
    (hH : ∀ y, HasFDerivAt H (innerSL ℝ (P y)) y)
    (y₀ : E) (T : E →L[ℝ] E) (hT : HasFDerivAt P T y₀) :
    (∀ v w, ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ) ∧
    (fun y => H y - H y₀ - ⟪P y₀, y - y₀⟫_ℝ -
      (1 / 2) * ⟪T (y - y₀), y - y₀⟫_ℝ)
      =o[𝓝 y₀] (fun y => ‖y - y₀‖ ^ 2) := by
  have hfield : HasFDerivAt (fun y => innerSL ℝ (P y)) ((innerSL ℝ).comp T) y₀ :=
    (innerSL ℝ).hasFDerivAt.comp y₀ hT
  have hsym (v w : E) : ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ :=
    second_derivative_symmetric hH hfield v w
  refine ⟨hsym, ?_⟩
  let R : E → ℝ := fun y => H y - H y₀ - ⟪P y₀, y - y₀⟫_ℝ -
    (1 / 2) * ⟪T (y - y₀), y - y₀⟫_ℝ
  let R' : E → E →L[ℝ] ℝ := fun y => innerSL ℝ (P y - P y₀ - T (y - y₀))
  have hshift (y : E) : HasFDerivAt (fun y : E => y - y₀) (ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).sub_const y₀
  have hquad (y : E) :
      HasFDerivAt (fun y => (1 / 2 : ℝ) * ⟪T (y - y₀), y - y₀⟫_ℝ)
        (innerSL ℝ (T (y - y₀))) y := by
    have hb := (innerSL ℝ).hasFDerivAt_of_bilinear
      (T.hasFDerivAt.comp y (hshift y)) (hshift y)
    convert hb.const_mul (1 / 2 : ℝ) using 1
    · rfl
    · ext v
      change ⟪T (y - y₀), v⟫_ℝ =
        (1 / 2 : ℝ) * (⟪T (y - y₀), v⟫_ℝ + ⟪T v, y - y₀⟫_ℝ)
      rw [hsym v (y - y₀)]
      ring
  have hR (y : E) : HasFDerivAt R (R' y) y := by
    have hlin := (innerSL ℝ (P y₀)).hasFDerivAt.comp y (hshift y)
    convert (((hH y).sub_const (H y₀)).sub hlin).sub (hquad y) using 1
    · rfl
    · ext v
      simp [R']
  have hremainder : (fun y => P y - P y₀ - T (y - y₀)) =o[𝓝 y₀] (fun y => y - y₀) :=
    hasFDerivAt_iff_isLittleO.mp hT
  have hsmall : R' =o[𝓝 y₀] (fun y => ‖y - y₀‖ ^ 1) := by
    simpa only [R', isLittleO_norm_right, pow_one] using
      ((innerSL ℝ).isBigO_comp (fun y => P y - P y₀ - T (y - y₀)) (𝓝 y₀)).trans_isLittleO
        hremainder
  have hfinal := convex_univ.isLittleO_pow_succ (n := 1) (mem_univ y₀)
    (fun y _ => (hR y).hasFDerivWithinAt) (by simpa only [nhdsWithin_univ] using hsmall)
  simpa only [R, sub_self, map_zero, inner_zero_right, inner_zero_left, mul_zero, sub_zero,
    nhdsWithin_univ] using hfinal

end Yau.LeafProofs.L01Aux
