import Yau.Proofs.F04LeviComp

open Filter
open scoped Topology ContDiff Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem laplacian_sub_smooth (H : HermitianField M) {f k : M.Carrier → ℝ}
    (hf : SmoothFn f) (hk : SmoothFn k) (x : M.Carrier) :
    laplacian H (fun y => f y - k y) x = laplacian H f x - laplacian H k x := by
  have hfx := (contDiffAt_inChart hf x (mem_extChartAt_target x)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hkx := (contDiffAt_inChart hk x (mem_extChartAt_target x)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  unfold laplacian levi
  change traceWith (gMat H x) (leviC (fun z => inChart x f z - inChart x k z) (chartPt x x)) = _
  rw [leviC_sub (z := chartPt x x) hfx hkx, Yau.Proofs.F02Aux.traceWith_sub]

theorem laplacian_smul_smooth (H : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    laplacian H (fun y => c * f y) x = c * laplacian H f x := by
  have hfx := (contDiffAt_inChart hf x (mem_extChartAt_target x)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hc : ContDiffAt ℝ 2 (fun s : ℝ => c * s) ((inChart x f) (chartPt x x)) :=
    (contDiff_const.mul contDiff_id).contDiffAt
  have hl := leviC_real_comp (z := chartPt x x) hfx hc
  simp only [deriv_const_mul_id', deriv_const, Complex.ofReal_zero, zero_smul, add_zero] at hl
  unfold laplacian levi
  change traceWith (gMat H x) (leviC (fun z => c * inChart x f z) (chartPt x x)) = _
  rw [hl, Yau.Proofs.F02Aux.traceWith_real_smul]

theorem laplacian_add_smooth (H : HermitianField M) {f k : M.Carrier → ℝ}
    (hf : SmoothFn f) (hk : SmoothFn k) (x : M.Carrier) :
    laplacian H (fun y => f y + k y) x = laplacian H f x + laplacian H k x := by
  have hm : SmoothFn (fun y => (-1 : ℝ) * k y) := fun a => contDiffOn_const.mul (hk a)
  have he : (fun y => f y + k y) = (fun y => f y - (-1 : ℝ) * k y) := by
    funext y
    ring
  rw [he, laplacian_sub_smooth H hf hm x, laplacian_smul_smooth H hk (-1) x]
  ring

end Yau.F04Proof
