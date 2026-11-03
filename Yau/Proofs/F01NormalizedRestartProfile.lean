import Yau.Proofs.F01NativeClosedProfileIdentity

/-! Exact normalized profile of the actual restarted potential after
restoring the original absolute clock. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def absoluteRestartPotential (W : M.Carrier → ℝ → ℝ) (T : ℝ) : M.Carrier → ℝ → ℝ :=
  fun x t => W x (t - T)

theorem normalized_restart_profile_eq
    (A : BoundedChartFamily g) (W : M.Carrier → ℝ → ℝ) (a : M.Carrier)
    (σ T : ℝ) (p : Point n) :
    shiftedNativePotential A (absoluteRestartPotential W T) a σ T p =
      (σ ^ 2)⁻¹ * W (A.chart a (σ • p.1)) (σ ^ 2 * p.2) := by
  simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
    affineParabolicPoint, absoluteRestartPotential, add_zero, add_sub_cancel_left]

theorem normalized_restart_profile_smooth
    (A : BoundedChartFamily g) (W : M.Carrier → ℝ → ℝ) {σ ε r : ℝ}
    (hσ : 0 < σ) (hσr : σ ≤ A.radius) (hrε : σ ^ 2 * r ≤ ε)
    (hW : SmoothSpaceTime W (Icc 0 ε)) (a : M.Carrier) (T : ℝ) :
    ContDiffOn ℝ ∞ (shiftedNativePotential A (absoluteRestartPotential W T) a σ T)
      (ball 0 1 ×ˢ Ico 0 r) := by
  have hAffine : ContDiff ℝ ∞ (fun p : Point n => (σ • p.1, σ ^ 2 * p.2)) := by fun_prop
  have hMap : MapsTo (fun p : Point n => (σ • p.1, σ ^ 2 * p.2))
      (ball 0 1 ×ˢ Ico 0 r) (ball 0 A.radius ×ˢ Icc 0 ε) := by
    intro p hp
    refine ⟨spatialDilation_mem_ball hσ hσr hp.1,
      mul_nonneg (sq_nonneg σ) hp.2.1, ?_⟩
    exact (mul_le_mul_of_nonneg_left hp.2.2.le (sq_nonneg σ)).trans hrε
  have hh : ContDiffOn ℝ ∞
      (fun p : Point n => (σ ^ 2)⁻¹ * W (A.chart a (σ • p.1)) (σ ^ 2 * p.2))
      (ball 0 1 ×ˢ Ico 0 r) :=
    contDiffOn_const.mul ((bounded_chart_spaceTime_smooth A hW a).comp hAffine.contDiffOn hMap)
  exact hh.congr (fun p hp => normalized_restart_profile_eq A W a σ T p)

end Yau.NodeProofs.F01Aux
