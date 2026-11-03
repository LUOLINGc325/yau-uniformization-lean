import Yau.LeafProofs.L19Exact

/-! Affine and scalar energy calculus in the original metric. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.P07Aux
open Yau Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem gradNormSq_nonnegative (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (x : M.Carrier) : 0 ≤ gradNormSq h f x := by
  have hh := scalarGradientPair_self_nonneg h f x
  rw [scalarGradientPair_eq_twice_gradNormSq h hf x] at hh
  linarith

theorem gradNormSq_scalar_comp (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : M.Carrier) :
    gradNormSq h (fun y => F (f y)) x = deriv F (f x) ^ 2 * gradNormSq h f x := by
  have he := scalarGradientPair_scalar_comp_self h hf F x
    (hF.differentiable (by simp) (f x))
  rw [scalarGradientPair_eq_twice_gradNormSq h (smoothFn_scalar_comp hf F hF) x,
    scalarGradientPair_eq_twice_gradNormSq h hf x] at he
  linarith

theorem gradNormSq_affine (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (a b : ℝ) (x : M.Carrier) :
    gradNormSq h (fun y => a * f y + b) x = a ^ 2 * gradNormSq h f x := by
  have hd : deriv (fun s : ℝ => a * s + b) (f x) = a := by
    simpa using (((hasDerivAt_id (f x)).const_mul a).add_const b).deriv
  rw [gradNormSq_scalar_comp h hf (fun s => a * s + b)
    (contDiff_const.mul contDiff_id |>.add contDiff_const) x, hd]

theorem laplacian_affine (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (a b : ℝ) (x : M.Carrier) :
    laplacian h (fun y => a * f y + b) x = a * laplacian h f x := by
  have hd : deriv (fun s : ℝ => a * s + b) = fun _ => a := by
    funext s
    simpa using (((hasDerivAt_id s).const_mul a).add_const b).deriv
  rw [laplacian_scalar_comp h hf (fun s => a * s + b) x
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const), hd]
  simp

end Yau.NodeProofs.P07Aux
