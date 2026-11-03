import Yau.Proofs.C02RescaledCorrection
import Mathlib.Analysis.Calculus.MeanValue

/-! The normalized correction has uniformly bounded amplitude from its
actual derivative bound. No boundary value on an artificial rim is assumed. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem rescaledCorrection_norm_le
    (s : ℝ) (hs : s ≠ 0) (a : E) (w : E → F) (hw : ContDiff ℝ ∞ w)
    {O : Set E} (hMaps : MapsTo (fun z => a + s • z) (Metric.ball (0 : E) 1) O)
    (B : ℝ) (hBound : ∀ y ∈ O, ‖fderiv ℝ w y‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball (0 : E) 1) :
    ‖rescaledCorrection s a w z‖ ≤ B * ‖z‖ := by
  have hDiff (x : E) (hx : x ∈ Metric.ball (0 : E) 1) :=
    rescaledCorrection_hasFDerivAt s hs a w x (hw.differentiable (by simp) _)
  have hDeriv (x : E) (hx : x ∈ Metric.ball (0 : E) 1) :
      ‖fderiv ℝ (rescaledCorrection s a w) x‖ ≤ B := by
    rw [(hDiff x hx).fderiv]
    exact hBound _ (hMaps hx)
  have h := (convex_ball (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hDiff x hx).differentiableAt) hDeriv (Metric.mem_ball_self zero_lt_one) hz
  simpa only [rescaledCorrection_zero, sub_zero] using h

end Yau.Blueprint.C02Proof
