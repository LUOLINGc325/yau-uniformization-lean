import Yau.LeafProofs.L17InteriorCoordinates

/-! Actual induced-distance completeness from the already proved uniform chart
escape and inverse-coordinate estimates; no metric completion is supplied. -/
open Set Metric Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem completeDistance_of_hermitianBoundedGeometry (g : HermitianField M)
    (hg : MetricSmooth g) (hbg : LeafCandidates.HermitianBoundedGeometry g) :
    IsCompleteDistance (inducedDistance g) := by
  classical
  obtain ⟨A⟩ := L17Aux.exists_boundedChartFamily g hbg
  intro s hs
  let r := A.radius
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  have hr : 0 < r := A.radius_pos
  have hA0 : 0 < A.bound 0 := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N₀, hN₀⟩ := hs (c * r / 8) (by positivity)
  let p := s N₀
  let e := A.chart p
  let z : ℕ → ComplexVector n := fun k => e.symm (s (N₀ + k))
  have hcoords (k : ℕ) : ‖z k‖ < r / 4 ∧ z k ∈ e.source ∧ e (z k) = s (N₀ + k) := by
    have hnear : inducedDistance g p (s (N₀ + k)) < c * (r / 4) := by
      have h := hN₀ N₀ (N₀ + k) le_rfl (Nat.le_add_right _ _)
      dsimp [p]
      exact h.trans (by nlinarith [mul_pos hc hr])
    obtain ⟨w, hw, hew⟩ := A.chartBall_contains_distance_ball hg p (s (N₀ + k))
      (by positivity : 0 < r / 4) (by dsimp [r]; linarith [A.radius_pos]) hnear
    have hwR : w ∈ ball (0 : ComplexVector n) A.radius :=
      mem_ball.mpr ((mem_ball.mp hw).trans (by dsimp [r]; linarith [A.radius_pos]))
    have hwS : w ∈ e.source := A.closedBall_source p (ball_subset_closedBall hwR)
    have hzw : z k = w := by
      change e.symm (s (N₀ + k)) = w
      rw [← hew]
      exact e.left_inv hwS
    rw [hzw]
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hw, hwS, hew⟩
  have hzC : CauchySeq z := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hs (min (ε * c / 2) (c * r / 4)) (by positivity)
    refine ⟨N, ?_⟩
    intro m hm k hk
    have hm' : N ≤ N₀ + m := hm.trans (Nat.le_add_left _ _)
    have hk' : N ≤ N₀ + k := hk.trans (Nat.le_add_left _ _)
    have hdist := hN (N₀ + m) (N₀ + k) hm' hk'
    have hρ : 0 < r / 2 := by positivity
    have hbuffer : closedBall (z m) (r / 2) ⊆ ball (0 : ComplexVector n) A.radius := by
      intro w hw
      have hwm : ‖w - z m‖ ≤ r / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
      apply mem_ball.mpr
      rw [dist_zero_right]
      calc
        ‖w‖ = ‖(w - z m) + z m‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z m‖ + ‖z m‖ := norm_add_le _ _
        _ ≤ r / 2 + ‖z m‖ := by linarith
        _ < r / 2 + r / 4 := by linarith [(hcoords m).1]
        _ < A.radius := by dsimp [r]; linarith [A.radius_pos]
    have hshort : inducedDistance g (A.chart p (z m)) (s (N₀ + k)) <
        Real.sqrt (2 * (A.bound 0)⁻¹) * (r / 2) := by
      rw [(hcoords m).2.2]
      exact (hdist.trans_le (min_le_right _ _)).trans (by
        change c * r / 4 < c * (r / 2)
        nlinarith [mul_pos hc hr])
    have hco := A.coordinate_diff_le_distance hg p (s (N₀ + k)) (z m) hρ hbuffer hshort
    have hb : dist (z m) (z k) ≤ c⁻¹ * inducedDistance g (s (N₀ + m)) (s (N₀ + k)) := by
      simpa only [z, e, (hcoords m).2.2, dist_eq_norm, norm_sub_rev, c] using hco
    have hsmall : inducedDistance g (s (N₀ + m)) (s (N₀ + k)) < ε * c :=
      (hdist.trans_le (min_le_left _ _)).trans (by nlinarith [mul_pos hε hc])
    calc
      _ ≤ c⁻¹ * inducedDistance g (s (N₀ + m)) (s (N₀ + k)) := hb
      _ < c⁻¹ * (ε * c) := mul_lt_mul_of_pos_left hsmall (inv_pos.mpr hc)
      _ = ε := by field_simp [hc.ne']
  obtain ⟨zlimit, hzconv⟩ := cauchySeq_tendsto_of_complete hzC
  have hzlimit : zlimit ∈ closedBall (0 : ComplexVector n) (r / 4) :=
    isClosed_closedBall.mem_of_tendsto hzconv (Eventually.of_forall fun k => by
      exact mem_closedBall.mpr (by simpa only [dist_zero_right] using (hcoords k).1.le))
  have hzlimitR : zlimit ∈ ball (0 : ComplexVector n) A.radius :=
    mem_ball.mpr ((mem_closedBall.mp hzlimit).trans_lt (by dsimp [r]; linarith [A.radius_pos]))
  refine ⟨e zlimit, ?_⟩
  intro ε hε
  let C := Real.sqrt (2 * A.bound 0)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hzconv) (ε / C) (div_pos hε hC)
  refine ⟨N₀ + N, ?_⟩
  intro k hk
  have hk₀ : N₀ ≤ k := by omega
  have hkN : N ≤ k - N₀ := by omega
  have hrep : N₀ + (k - N₀) = k := Nat.add_sub_of_le hk₀
  have hzk : z (k - N₀) ∈ ball (0 : ComplexVector n) A.radius :=
    mem_ball.mpr ((show dist (z (k - N₀)) 0 < r / 4 by
      simpa only [dist_zero_right] using (hcoords (k - N₀)).1).trans (by dsimp [r]; linarith [A.radius_pos]))
  have hd := A.distance_le hg p hzk hzlimitR
  have hpoint : A.chart p (z (k - N₀)) = s k := by
    simpa only [hrep] using (hcoords (k - N₀)).2.2
  rw [hpoint] at hd
  exact hd.trans_lt (by
    change C * dist (z (k - N₀)) zlimit < ε
    exact (mul_lt_mul_of_pos_left (hN (k - N₀) hkN) hC).trans_eq (by field_simp [hC.ne']))

end Yau.NodeProofs.F01Aux
