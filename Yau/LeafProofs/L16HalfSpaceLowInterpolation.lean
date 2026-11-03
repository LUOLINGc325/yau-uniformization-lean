import Yau.LeafProofs.L16HalfSpaceSchauderTransport
import Yau.LeafProofs.L16LowJetInterpolation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance halfSpaceLowInterpolation_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceLowInterpolation_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Actual global raw parabolic bounds give a global lower-jet Holder bound.
The existing finite-radius secant estimate is applied at arbitrary radii,
with one fixed unit interpolation margin. -/
theorem c2_global_lowPair_holder {n : ℕ} {α T K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hK : 0 ≤ K) {u : Point n → ℝ} (hu : C2 (cylinder univ 0 T) u)
    (hBound : ∀ p ∈ cylinder univ 0 T, |u p| ≤ K ∧ ‖spatialDD u p‖ ≤ K ∧
      |timeD (cylinder univ 0 T) u p| ≤ K) :
    HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) (16*K) := by
  have hLocal (s : ℝ) (hs : 0 ≤ s) :
      HolderBound α (cylinder (Metric.closedBall 0 s) 0 T) (fun p => (u p,spatialD u p)) (16*K) := by
    have hh := c2_lowPair_interpolation (s := s) (R := s+1) (ρ := 1) (B := K) (K := K)
      hα hα1 hT hs (by norm_num) (by norm_num) (by linarith) hK hK
      (c2_cylinder_restrict_space hu)
      (fun p hp => (hBound p ⟨mem_univ _,hp.2⟩).1)
      (fun p hp => ⟨(hBound p ⟨mem_univ _,hp.2⟩).2.1,by
        rw [timeD_cylinder_restrict_space u hp]
        exact (hBound p ⟨mem_univ _,hp.2⟩).2.2⟩)
    convert hh using 1
    simp only [Real.one_rpow,one_mul]
    ring
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

/-- Raw one-sided parabolic bounds imply the complete lower-jet Holder bound
    on the genuine closed half space. The reflection and secant arguments
    require no pre-existing Holder seminorm or mixed derivative. -/
theorem c2_halfSpace_lowPair_holder {n : ℕ} {α T K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hK : 0 ≤ K) {e : Space n} (he : ‖e‖ = 1) {u : Point n → ℝ}
    (hu : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) u)
    (hBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      |u p| ≤ K ∧ ‖spatialD u p‖ ≤ K ∧ ‖spatialDD u p‖ ≤ K ∧
      |timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) u p| ≤ K) :
    HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => (u p,spatialD u p)) (8000*K) := by
  let U := halfSpaceSecondOrderExtension e u
  obtain ⟨hU,hVal,hGrad,hRaw⟩ := halfSpaceSecondOrderExtension_raw_bounds he hT hK hu hBound
  have hGlobal : HolderBound α (cylinder univ 0 T) (fun p => (U p,spatialD U p)) (8000*K) := by
    have hh := c2_global_lowPair_holder hα hα1 hT (by positivity : 0 ≤ 500*K) hU
      (fun p hp => ⟨(hRaw p hp).1,(hRaw p hp).2.2.1,(hRaw p hp).2.2.2⟩)
    convert hh using 1
    ring
  have hSmall := holderBound_mono hGlobal
    (show cylinder {x | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder univ 0 T from fun p hp => ⟨mem_univ _,hp.2⟩)
  exact holderBound_congr_on hSmall (fun p hp => Prod.ext (hVal hp) (hGrad hp))

end Yau.LeafProofs.L16Aux
