import Yau.Proofs.F01NativeTerminalClosure
import Yau.Proofs.F01ScalarChartSmooth

/-! Each slice of the explicitly closed native potential is genuinely
smooth, including the constructed terminal slice. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem nativeClosedTerminalPotential_smooth_slice
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (hu : SmoothFn u) (T : ℝ)
    (hU : ∀ s, 0 ≤ s → s < T → SmoothSpaceTime U (Icc 0 s))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    SmoothFn (fun x => nativeClosedTerminalPotential U u T x t) := by
  by_cases he : t = T
  · simpa only [nativeClosedTerminalPotential, if_pos he] using hu
  · have hh : SmoothFn (fun x => U x t) :=
      smoothSpaceTime_slice (hU t ht0 (lt_of_le_of_ne htT he)) ⟨ht0, le_rfl⟩
    simpa only [nativeClosedTerminalPotential, if_neg he] using hh

theorem native_closed_terminal_profile_slices
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (hu : SmoothFn u) {σ T : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hEarly : 0 ≤ T - σ ^ 2 / 4)
    (hU : ∀ s, 0 ≤ s → s < T → SmoothSpaceTime U (Icc 0 s)) (a : M.Carrier)
    {t : ℝ} (ht : t ∈ Ioc (-(1 / 4 : ℝ)) 0) :
    ContDiffOn ℝ ∞
      (fun z => shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T (z, t))
      (ball 0 1) := by
  have hClock0 : 0 ≤ T + σ ^ 2 * t := by
    have hh := mul_lt_mul_of_pos_left ht.1 (sq_pos_of_pos hσ)
    linarith
  have hClockT : T + σ ^ 2 * t ≤ T := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg σ) ht.2
    linarith
  have hNative := nativeClosedTerminalPotential_smooth_slice U u hu T hU hClock0 hClockT
  have hChart := smoothFn_comp_holomorphic_chart _ hNative (A.chart a) (A.differentiable a)
  have hDilation : ContDiffOn ℝ ∞ (fun z : Space n => σ • z) (ball 0 1) := by fun_prop
  have hCompose := hChart.comp hDilation (fun z hz =>
    A.closedBall_source a (ball_subset_closedBall (spatialDilation_mem_ball hσ hσr hz)))
  have hh : ContDiffOn ℝ ∞ (fun z => (σ ^ 2)⁻¹ *
      nativeClosedTerminalPotential U u T (A.chart a (σ • z)) (T + σ ^ 2 * t))
      (ball 0 1) := contDiffOn_const.mul hCompose
  apply hh.congr
  intro z hz
  simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
    affineParabolicPoint, add_zero]

end Yau.NodeProofs.F01Aux
