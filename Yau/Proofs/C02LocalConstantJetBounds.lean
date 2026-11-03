import spec.CHAIN.CONTRACTS

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_const_add_on_le {O : Set E} (hO : IsOpen O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) {x : E} (hx : x ∈ O)
    (C : F) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => C + f y) x‖ ≤
      if m = 0 then ‖C‖ + ‖f x‖ else ‖iteratedFDeriv ℝ m f x‖ := by
  cases m with
  | zero => simpa only [norm_iteratedFDeriv_zero, ite_true] using norm_add_le C (f x)
  | succ m =>
    have hAt := (hf x hx).contDiffAt (hO.mem_nhds hx)
    rw [fun_iteratedFDeriv_add_apply
      (contDiffAt_const : ContDiffAt ℝ (m + 1) (fun _ : E => C) x)
      (hAt.of_le (by simp)), iteratedFDeriv_succ_const]
    simp

theorem norm_iteratedFDeriv_const_sub_on_le {O : Set E} (hO : IsOpen O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) {x : E} (hx : x ∈ O)
    (C : F) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => C - f y) x‖ ≤
      if m = 0 then ‖C‖ + ‖f x‖ else ‖iteratedFDeriv ℝ m f x‖ := by
  cases m with
  | zero => simpa only [norm_iteratedFDeriv_zero, ite_true] using norm_sub_le C (f x)
  | succ m =>
    have hAt := (hf x hx).contDiffAt (hO.mem_nhds hx)
    rw [fun_iteratedFDeriv_sub_apply
      (contDiffAt_const : ContDiffAt ℝ (m + 1) (fun _ : E => C) x)
      (hAt.of_le (by simp)), iteratedFDeriv_succ_const]
    simp

end Yau.Blueprint.C02Proof
