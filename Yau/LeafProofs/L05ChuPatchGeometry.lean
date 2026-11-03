import Yau.LeafProofs.L05ChuParabolicGeometry
import Yau.LeafProofs.L05ChuSpatialCutoffBudget
import Yau.LeafProofs.L05ChuCausalCutoff

noncomputable section

open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def chuCausalPatch {n : ℕ} (p : Point n) (h : ℝ) : Set (Point n) :=
  cylinder (Metric.ball p.1 (2*h)) (p.2-4*h^2) p.2

theorem chuCausalPatch_distance_to_center {n : ℕ} {p0 p : Point n} {h : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ chuCausalPatch p0 h) : parabolicDistance p p0 ≤ 4*h := by
  have hx : ‖p.1-p0.1‖ < 2*h := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hp.1
  have ht : |p.2-p0.2| ≤ 4*h^2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hp.2.2)]
    linarith only [hp.2.1]
  have hs : Real.sqrt |p.2-p0.2| ≤ 2*h := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [ht]⟩
  unfold parabolicDistance
  linarith only [hx,hs]

theorem chuCausalPatch_pair_distance {n : ℕ} {p0 p q : Point n} {h : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ chuCausalPatch p0 h) (hq : q ∈ chuCausalPatch p0 h) :
    parabolicDistance p q ≤ 8*h := by
  have hp0 := chuCausalPatch_distance_to_center hh hp
  have hq0 := chuCausalPatch_distance_to_center hh hq
  have hSymm : parabolicDistance p0 q=parabolicDistance q p0 := by
    simp only [parabolicDistance,norm_sub_rev,abs_sub_comm]
  have htri := chu_parabolicDistance_triangle p q p0
  rw [hSymm] at htri
  linarith only [htri,hp0,hq0]

theorem chuCausalPatch_subset_low_box {n : ℕ} {p0 : Point n} {h : ℝ}
    (hh : 0 ≤ h) (hSmall : h ≤ (1/32:ℝ)) (hp0 : p0 ∈ backward (1/2)) :
    chuCausalPatch p0 h ⊆ cylinder (Metric.closedBall 0 (5/8)) (-(1/2)) 0 := by
  intro p hp
  have hx : ‖p.1-p0.1‖ < 2*h := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hp.1
  have hc : ‖p0.1‖ < (1/2:ℝ) := by simpa only [dist_zero_right] using Metric.mem_ball.mp hp0.1
  have hnorm : ‖p.1‖ ≤ ‖p.1-p0.1‖+‖p0.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (p.1-p0.1) p0.1
  have hsq : h^2 ≤ (1/32:ℝ)^2 := (sq_le_sq₀ hh (by norm_num)).mpr hSmall
  refine ⟨Metric.mem_closedBall.mpr ?_,?_,hp.2.2.trans hp0.2.2⟩
  · rw [dist_zero_right]
    linarith only [hx,hc,hnorm,hSmall]
  · nlinarith only [hp0.2.1,hp.2.1,hsq]

theorem chu_low_box_subset_backward :
    cylinder (Metric.closedBall (0 : Space n) (5/8)) (-(1/2)) 0 ⊆ backward (3/4) := by
  intro p hp
  refine ⟨Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hp.1).trans_lt (by norm_num)),?_,hp.2.2⟩
  linarith only [hp.2.1]

theorem chuCausalPatch_subset_backward {n : ℕ} {p0 : Point n} {h : ℝ}
    (hh : 0 ≤ h) (hSmall : h ≤ (1/32:ℝ)) (hp0 : p0 ∈ backward (1/2)) :
    chuCausalPatch p0 h ⊆ backward (3/4) :=
  (chuCausalPatch_subset_low_box hh hSmall hp0).trans chu_low_box_subset_backward

theorem chu_near_pair_patch_plateau {n : ℕ} {p0 q : Point n} {h : ℝ} (hh : 0 < h)
    (hTime : q.2 ≤ p0.2) (hNear : parabolicDistance q p0 ≤ h/2) :
    q ∈ chuCausalPatch p0 h ∧
      L16Aux.innerPatchBump h hh p0.1 q.1=1 ∧ chuCausalTimeCutoff (p0.2-4*h^2) p0.2 q.2=1 := by
  have hx : ‖q.1-p0.1‖ ≤ h/2 := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hNear
  have hs : Real.sqrt |q.2-p0.2| ≤ h/2 := (le_add_of_nonneg_left (norm_nonneg _)).trans hNear
  have ht : |q.2-p0.2| ≤ h^2/4 := by
    have hsq := Real.sq_sqrt (abs_nonneg (q.2-p0.2))
    nlinarith only [hs,hsq,Real.sqrt_nonneg |q.2-p0.2|,hh]
  have hl : p0.2-4*h^2 < p0.2 := by nlinarith only [sq_pos_of_pos hh]
  have hqt : p0.2-q.2 ≤ h^2/4 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hTime)] at ht
    linarith only [ht]
  refine ⟨⟨Metric.mem_ball.mpr ?_,?_,hTime⟩,L16Aux.innerPatchBump_eq_one hh (by linarith only [hx,hh]),
    chuCausalTimeCutoff_one_late hl ?_⟩
  · rw [dist_eq_norm]
    linarith only [hx,hh]
  · nlinarith only [hqt,sq_nonneg h]
  · nlinarith only [hqt,sq_nonneg h]

end Yau.LeafProofs.L05Aux
