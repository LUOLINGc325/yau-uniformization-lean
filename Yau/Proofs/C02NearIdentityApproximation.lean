import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! Derivative control on an actual convex domain gives the quantitative
linear approximation used for a fixed-radius inverse chart. -/

noncomputable section
open Set
open scoped NNReal
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem approximates_identity_of_fderiv_close {f : E → E} {O : Set E}
    (hO : Convex ℝ O) (hf : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hClose : ∀ x ∈ O, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ApproximatesLinearOn f (ContinuousLinearMap.id ℝ E) O (1 / 4 : ℝ≥0) := by
  let F := fun x => f x - x
  have hF (x : E) (hx : x ∈ O) : DifferentiableAt ℝ F x :=
    (hf x hx).sub differentiableAt_id
  have hDF (x : E) (hx : x ∈ O) : ‖fderiv ℝ F x‖ ≤ (1 / 4 : ℝ) := by
    change ‖fderiv ℝ (fun y => f y - id y) x‖ ≤ _
    rw [fderiv_fun_sub (hf x hx) (differentiableAt_id : DifferentiableAt ℝ (id : E → E) x), fderiv_id]
    exact hClose x hx
  intro x hx y hy
  have hh := hO.norm_image_sub_le_of_norm_fderiv_le hF hDF hy hx
  have heq : F x - F y = f x - f y - ContinuousLinearMap.id ℝ E (x - y) := by
    simp only [F, ContinuousLinearMap.id_apply]
    abel
  rw [heq] at hh
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

end Yau.Blueprint.C02Proof
