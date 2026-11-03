import Yau.LeafProofs.L16CompatibleHolderGraph

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance compatibleInverseOperator_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance compatibleInverseOperator_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The actual weighted contraction makes the correction equation unique
    within the closed corner-compatible source space. -/
theorem compatibleHolderGraph_correction_injective {n : ℕ} {α T B : ℝ} {O : Set (Space n)}
    (R : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T) (hB : 0 ≤ B)
    (hContract : ∀ x, ‖R x‖+B*‖(R x).val.val.1‖ ≤
      (1/2 : ℝ)*(‖x‖+B*‖x.val.val.1‖)) :
    Function.Injective (fun x => x+R x) := by
  intro x y hxy
  let z := x-y
  have hRz : R z = -z := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      R z+z = (x+R x)-(y+R y) := by dsimp only [z]; rw [R.map_sub]; abel
      _ = 0 := sub_eq_zero.mpr hxy
  have h := hContract z
  rw [hRz] at h
  have hNegProj : ‖(-z).val.val.1‖ = ‖z.val.val.1‖ := by
    change ‖-(z.val.val.1)‖ = ‖z.val.val.1‖
    exact norm_neg _
  rw [norm_neg,hNegProj] at h
  have hz : ‖z‖ ≤ 0 := by nlinarith [mul_nonneg hB (norm_nonneg z.val.val.1)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg z)))

/-- The proved weighted Neumann correction has a genuine bounded linear
    choice. Linearity follows from uniqueness of the actual correction
    equation, rather than from an unproved claim about arbitrary choices. -/
theorem compatibleHolderGraph_linear_residual_correction {n : ℕ} {α T B : ℝ} {O : Set (Space n)}
    (R : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T) (hB : 0 ≤ B)
    (hContract : ∀ x, ‖R x‖+B*‖(R x).val.val.1‖ ≤
      (1/2 : ℝ)*(‖x‖+B*‖x.val.val.1‖)) :
    ∃ G : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α O T,
      ‖G‖ ≤ 2*(1+B) ∧ ∀ f, G f+R (G f) = f := by
  classical
  choose g hEq hNorm using fun f : compatibleHolderGraph α O T =>
    compatibleHolderGraph_residual_correction_weighted R hB hContract f
  have hInj := compatibleHolderGraph_correction_injective R hB hContract
  have hAdd (x y : compatibleHolderGraph α O T) : g (x+y) = g x+g y := by
    apply hInj
    change g (x+y)+R (g (x+y)) = (g x+g y)+R (g x+g y)
    rw [hEq (x+y),R.map_add]
    calc
      x+y = (g x+R (g x))+(g y+R (g y)) := by rw [hEq x,hEq y]
      _ = _ := by abel
  have hSmul (c : ℝ) (x : compatibleHolderGraph α O T) : g (c • x) = c • g x := by
    apply hInj
    change g (c • x)+R (g (c • x)) = c • g x+R (c • g x)
    rw [hEq (c • x),R.map_smul]
    calc
      c • x = c • (g x+R (g x)) := by rw [hEq x]
      _ = _ := smul_add _ _ _
  let L : compatibleHolderGraph α O T →ₗ[ℝ] compatibleHolderGraph α O T :=
    { toFun := g, map_add' := hAdd, map_smul' := hSmul }
  let G := L.mkContinuous (2*(1+B)) hNorm
  refine ⟨G,?_,hEq⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact hNorm

end Yau.LeafProofs.L16Aux
