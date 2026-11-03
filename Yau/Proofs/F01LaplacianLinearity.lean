import Yau.Proofs.F01PotentialLaplacian

/-! Linearity of the actual native scalar Laplacian follows from the
actual complex Hessian, rather than from a caller-supplied differential operator. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothFn_chart_contDiffAt {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
  ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_target x))).of_le (by simp)

theorem levi_add_native {f g : M.Carrier → ℝ} (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    levi (fun y => f y + g y) x = levi f x + levi g x :=
  leviC_add (smoothFn_chart_contDiffAt hf x) (smoothFn_chart_contDiffAt hg x)

theorem levi_sub_native {f g : M.Carrier → ℝ} (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    levi (fun y => f y - g y) x = levi f x - levi g x :=
  leviC_sub (smoothFn_chart_contDiffAt hf x) (smoothFn_chart_contDiffAt hg x)

theorem levi_const_mul_native {f : M.Carrier → ℝ} (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    levi (fun y => c * f y) x = (c : ℂ) • levi f x :=
  leviC_const_mul (smoothFn_chart_contDiffAt hf x) c

theorem levi_const_native (c : ℝ) (x : M.Carrier) : levi (fun _ => c) x = 0 :=
  leviC_const c (chartPt x x)

theorem laplacian_add_native (h : HermitianField M) {f g : M.Carrier → ℝ}
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    laplacian h (fun y => f y + g y) x = laplacian h f x + laplacian h g x := by
  unfold laplacian
  rw [levi_add_native hf hg, traceWith_add]

theorem laplacian_sub_native (h : HermitianField M) {f g : M.Carrier → ℝ}
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    laplacian h (fun y => f y - g y) x = laplacian h f x - laplacian h g x := by
  unfold laplacian
  rw [levi_sub_native hf hg, traceWith_sub]

theorem laplacian_const_mul_native (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun y => c * f y) x = c * laplacian h f x := by
  unfold laplacian
  rw [levi_const_mul_native hf c, traceWith_real_smul]

theorem laplacian_const_native (h : HermitianField M) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun _ => c) x = 0 := by
  simp only [laplacian, levi_const_native, traceWith, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

end Yau.NodeProofs.F01Aux
