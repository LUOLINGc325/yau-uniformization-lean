import Yau.LeafProofs.L16HalfSpaceLowInterpolation
import Yau.LeafProofs.L16Continuation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance zeroInitialSchauder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance zeroInitialSchauder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance zeroInitialSchauder_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance zeroInitialSchauder_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual global secant interpolation retains an arbitrary positive
    spatial interpolation length. -/
theorem c2_global_lowPair_scaled {n : ℕ} {α T B K ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hB : 0 ≤ B) (hK : 0 ≤ K) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {u : Point n → ℝ} (hu : C2 (cylinder univ 0 T) u)
    (hBound : ∀ p ∈ cylinder univ 0 T, |u p| ≤ B ∧ ‖spatialDD u p‖ ≤ K ∧
      |timeD (cylinder univ 0 T) u p| ≤ K) :
    HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) (8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
  have hLocal (s : ℝ) (hs : 0 ≤ s) :
      HolderBound α (cylinder (Metric.closedBall 0 s) 0 T) (fun p => (u p,spatialD u p)) (8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
    have hh := c2_lowPair_interpolation (s := s) (R := s+ρ) (ρ := ρ) (B := B) (K := K)
      hα hα1 hT hs hρ hρ1 (by linarith) hB hK
      (c2_cylinder_restrict_space hu)
      (fun p hp => (hBound p ⟨mem_univ _,hp.2⟩).1)
      (fun p hp => ⟨(hBound p ⟨mem_univ _,hp.2⟩).2.1,by
        rw [timeD_cylinder_restrict_space u hp]
        exact (hBound p ⟨mem_univ _,hp.2⟩).2.2⟩)
    exact hh
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    apply (hLocal ‖p.1‖ (norm_nonneg _)).2.1 p
    refine ⟨?_,hp.2⟩
    simp only [Metric.mem_closedBall,dist_zero_right,le_refl]
  · intro p hp q hq
    let s := max ‖p.1‖ ‖q.1‖
    have hs : 0 ≤ s := (norm_nonneg p.1).trans (le_max_left _ _)
    have hpS : p ∈ cylinder (Metric.closedBall 0 s) 0 T := by
      refine ⟨?_,hp.2⟩
      simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_left ‖p.1‖ ‖q.1‖
    have hqS : q ∈ cylinder (Metric.closedBall 0 s) 0 T := by
      refine ⟨?_,hq.2⟩
      simpa only [Metric.mem_closedBall,dist_zero_right] using le_max_right ‖p.1‖ ‖q.1‖
    exact (hLocal s hs).2.2 p hpS q hqS

/-- Small actual value and Hessian bounds follow from the proved full
    Schauder estimate and the real zero initial slice. -/
theorem zero_initial_schauder_small_sup {n : ℕ} {α T K : ℝ}
    (hα : 0 < α) (hT : 0 < T) {u : Point n → ℝ}
    (hu : SchauderBound α (cylinder univ 0 T) u K) (h0 : ∀ x, u (x,0) = 0) :
    ∀ p ∈ cylinder univ 0 T, |u p| ≤ K*T ∧ ‖spatialDD u p‖ ≤ K*T^(α/2) := by
  intro p hp
  have hBall : p.1 ∈ Metric.closedBall (0 : Space n) ‖p.1‖ := by
    simp only [Metric.mem_closedBall,dist_zero_right,le_refl]
  have hTime := c2_time_lipschitz_on_closedBall (c2_cylinder_restrict_space hu.1)
    (fun q hq => by
      rw [timeD_cylinder_restrict_space u hq]
      simpa only [Real.norm_eq_abs] using hu.2.2.2.2.2.1 q ⟨mem_univ _,hq.2⟩)
    hBall (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩) hp.2
  have hValue : |u p| ≤ K*p.2 := by
    simpa only [h0,sub_zero,abs_of_nonneg hp.2.1,Prod.eta] using hTime
  have hHessian := hu.2.2.2.1.2.2 p hp (p.1,0) ⟨mem_univ _,le_rfl,hT.le⟩
  rw [spatialDD_initial_zero h0 p.1,sub_zero] at hHessian
  have hHessPoint : ‖spatialDD u p‖ ≤ K*p.2^(α/2) := by
    simpa only [holderWeight,sub_self,norm_zero,Real.zero_rpow hα.ne',zero_add,
      sub_zero,abs_of_nonneg hp.2.1] using hHessian
  exact ⟨hValue.trans (mul_le_mul_of_nonneg_left hp.2.2 hu.2.1),
    hHessPoint.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp.2.1 hp.2.2 (by positivity : 0 ≤ α/2)) hu.2.1)⟩

/-- Lower Holder jets become small after the time interval is shortened
    below the square of a freely selected secant scale. No new kernel
    derivative estimate or mixed derivative is needed. -/
theorem zero_initial_schauder_lowPair_small {n : ℕ} {α T K ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hTρ : T ≤ ρ^2) {u : Point n → ℝ}
    (hu : SchauderBound α (cylinder univ 0 T) u K) (h0 : ∀ x, u (x,0) = 0) :
    HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p))
      (16*K*ρ^(1-α)) := by
  have hK : 0 ≤ K := hu.2.1
  have h := c2_global_lowPair_scaled hα hα1 hT (by positivity : 0 ≤ K*T) hK hρ hρ1 hu.1
    (fun p hp => ⟨(zero_initial_schauder_small_sup hα hT hu h0 p hp).1,
      hu.2.2.2.1.2.1 p hp,by simpa only [Real.norm_eq_abs] using hu.2.2.2.2.2.1 p hp⟩)
  apply holderBound_mono_const h
  have hPower : ρ^(-1-α)*ρ^2 = ρ^(1-α) := by
    calc
      _ = ρ^(-1-α)*ρ^(2 : ℝ) := by rw [Real.rpow_two]
      _ = _ := by rw [← Real.rpow_add hρ]; congr 1; ring
  have hSmall : ρ^(-1-α)*(K*T) ≤ K*ρ^(1-α) := by
    calc
      _ = K*(ρ^(-1-α)*T) := by ring
      _ ≤ K*(ρ^(-1-α)*ρ^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hTρ (by positivity)) hK
      _ = _ := by rw [hPower]
  nlinarith

end Yau.LeafProofs.L16Aux
