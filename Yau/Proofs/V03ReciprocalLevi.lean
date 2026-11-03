import Yau.Proofs.V03LeviCalculus

/-! Exact reciprocal-cutoff Hessian calculus for the original nested
Wirtinger operators. Clearing powers will give smooth boundary tensors. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirtBar_inv {f : E → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) (v : E) :
    wirtBar (fun y => (f y)⁻¹) z v = -(f z)⁻¹ ^ 2 * wirtBar f z v := by
  simp only [wirtBar, fderiv_inv_complex_apply hf hne]
  ring

theorem wirt_neg (f : E → ℂ) (z v : E) :
    wirt (fun y => -f y) z v = -wirt f z v := by
  simp only [wirt, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  ring

theorem reciprocal_levi {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v : E) :
    wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z v =
      2 * (f z)⁻¹ ^ 3 * wirt f z v * wirtBar f z v -
      (f z)⁻¹ ^ 2 * wirt (fun y => wirtBar f y v) z v := by
  have hd := hf.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hi := hd.fun_inv hne
  have hB := wirtBar_differentiableAt hf v
  have heq : (fun y => wirtBar (fun x => (f x)⁻¹) y v) =ᶠ[𝓝 z]
      (fun y => -((f y)⁻¹ * (f y)⁻¹) * wirtBar f y v) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne hne] with y hy hny
    rw [wirtBar_inv (hy.differentiableAt (by norm_num)) hny]
    ring
  have hw : wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z v =
      wirt (fun y => -((f y)⁻¹ * (f y)⁻¹) * wirtBar f y v) z v := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_mul (f := fun y => -((f y)⁻¹ * (f y)⁻¹)) (hi.mul hi).neg hB,
    wirt_neg, wirt_mul hi hi, wirt_inv hd hne]
  ring

theorem reciprocal_levi_cleared {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v : E) {m : ℕ} (hm : 3 ≤ m) :
    f z ^ m * wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z v =
      2 * f z ^ (m - 3) * wirt f z v * wirtBar f z v -
      f z ^ (m - 2) * wirt (fun y => wirtBar f y v) z v := by
  rw [reciprocal_levi hf hne]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h32 : 3 + k - 2 = 1 + k := by omega
  rw [Nat.add_sub_cancel_left, h32]
  simp only [pow_add, pow_succ, pow_zero]
  field_simp [hne]
  <;> ring

end Yau.Blueprint.V03Proof
