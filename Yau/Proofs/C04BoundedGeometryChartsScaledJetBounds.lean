import Yau.Proofs.C04BoundedGeometryChartsScaledConnection
import Yau.LeafProofs.L21FiniteJetScaling

/-! The one chosen dilation preserves the uniform full jet bounds. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_dilate_le_one (f : E → F) (m : ℕ) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => f (d • y)) x‖ ≤ ‖iteratedFDeriv ℝ m f (d • x)‖ := by
  have H := Yau.LeafProofs.L21Aux.norm_iteratedFDeriv_dilate_le f m d hd.ne' x
  rw [abs_of_pos hd] at H
  exact H.trans (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hd.le hd1))

theorem norm_iteratedFDeriv_scaled_dilate_le_one (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => d • f (d • y)) x‖ ≤ ‖iteratedFDeriv ℝ m f (d • x)‖ := by
  have hfd : ContDiff ℝ ∞ (fun y => f (d • y)) := hf.comp (contDiff_id.const_smul d)
  change ‖iteratedFDeriv ℝ m (d • (fun y => f (d • y))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hfd.contDiffAt.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_pos hd]
  exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dilate_le_one f m hd hd1 x) hd.le).trans
    (mul_le_of_le_one_left (norm_nonneg _) hd1)

theorem dilate_half_ball_mem_closed {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (hdR : d ≤ R / 4)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    d • x ∈ Metric.closedBall (0 : E) R := by
  have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  nlinarith
end Generic

theorem scaled_normal_jets_le {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (R : ℝ) (hR : 0 < R) (B : ℕ → ℝ) (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hdR : d ≤ R / 4)
    (hjet : ∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R →
      ‖iteratedFDeriv ℝ m (radialCoframe g p U) x‖ ≤ B m ∧
      ‖iteratedFDeriv ℝ m (radialConnection g p U) x‖ ≤ B m) :
    ∀ m x, x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ) →
      ‖iteratedFDeriv ℝ m (scaledRadialCoframe g p U d) x‖ ≤ B m ∧
      ‖iteratedFDeriv ℝ m (scaledRadialConnection g p U d) x‖ ≤ B m := by
  intro m x hx
  have hdx := dilate_half_ball_mem_closed hR hd hdR hx
  exact ⟨(norm_iteratedFDeriv_dilate_le_one (radialCoframe g p U) m hd hd1 x).trans (hjet m _ hdx).1,
    (norm_iteratedFDeriv_scaled_dilate_le_one (radialConnection g p U) (radialConnection_smooth g p U)
      m hd hd1 x).trans (hjet m _ hdx).2⟩

end Yau.Proofs.C04ChartsAux
