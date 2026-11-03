import Yau.LeafProofs.L05PerturbationOscillationDecay

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_distance_nonneg {n : ℕ} (p q : Point n) : 0 ≤ parabolicDistance p q :=
  add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem perturb_distance_zero {n : ℕ} {p q : Point n} (h : parabolicDistance p q=0) : p=q := by
  have hx : ‖p.1-q.1‖=0 := by
    dsimp only [parabolicDistance] at h
    nlinarith only [h,norm_nonneg (p.1-q.1),Real.sqrt_nonneg |p.2-q.2|]
  have ht : Real.sqrt |p.2-q.2|=0 := by
    dsimp only [parabolicDistance] at h
    linarith
  have hTime := Real.sq_sqrt (abs_nonneg (p.2-q.2))
  rw [ht] at hTime
  have ht0 : p.2-q.2=0 := abs_eq_zero.mp (by nlinarith only [hTime])
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hx)) (sub_eq_zero.mp ht0)

theorem perturb_distance_rpow_le_weight {n : ℕ} {kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) (p q : Point n) :
    (parabolicDistance p q)^kappa ≤ holderWeight kappa p q := by
  change (‖p.1-q.1‖+Real.sqrt |p.2-q.2|)^kappa ≤
    ‖p.1-q.1‖^kappa+|p.2-q.2|^(kappa/2)
  calc
    _ ≤ ‖p.1-q.1‖^kappa+(Real.sqrt |p.2-q.2|)^kappa :=
      Real.rpow_add_le_add_rpow (norm_nonneg _) (Real.sqrt_nonneg _) hk0 hk1
    _ = _ := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (abs_nonneg _)]
      congr 2
      ring

theorem perturb_pair_mem_closed {n : ℕ} (p q : Point n) :
    p∈perturbClosed p.1 (2*parabolicDistance p q) (max p.2 q.2) ∧
      q∈perturbClosed p.1 (2*parabolicDistance p q) (max p.2 q.2) := by
  let d := parabolicDistance p q
  have hd : 0 ≤ d := perturb_distance_nonneg p q
  have hx : ‖p.1-q.1‖ ≤ d := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have ht : |p.2-q.2| ≤ d^2 := by
    have hs := Real.sq_sqrt (abs_nonneg (p.2-q.2))
    have hn := norm_nonneg (p.1-q.1)
    have hrt := Real.sqrt_nonneg |p.2-q.2|
    dsimp only [d,parabolicDistance]
    nlinarith only [hs,hn,hrt]
  have hpX : p.1∈closedBall p.1 (2*d) := mem_closedBall_self (by positivity)
  have hqX : q.1∈closedBall p.1 (2*d) := by
    rw [mem_closedBall,dist_eq_norm,norm_sub_rev]
    linarith only [hx,hd]
  rcases le_total p.2 q.2 with hpq | hqp
  · rw [max_eq_right hpq]
    have hab : q.2-p.2 ≤ |p.2-q.2| := by simpa only [neg_sub] using neg_le_abs (p.2-q.2)
    exact ⟨⟨hpX,by change q.2-(2*d)^2 ≤ p.2; nlinarith only [ht,hab,sq_nonneg d],hpq⟩,
      ⟨hqX,sub_le_self _ (sq_nonneg _),le_rfl⟩⟩
  · rw [max_eq_left hqp]
    have hab : p.2-q.2 ≤ |p.2-q.2| := le_abs_self _
    exact ⟨⟨hpX,sub_le_self _ (sq_nonneg _),le_rfl⟩,
      ⟨hqX,by change p.2-(2*d)^2 ≤ q.2; nlinarith only [ht,hab,sq_nonneg d],hqp⟩⟩

theorem perturb_half_pair_top {n : ℕ} {p q : Point n}
    (hp : p∈perturbClosed (0 : Space n) (1/2) 0)
    (hq : q∈perturbClosed (0 : Space n) (1/2) 0) :
    (p.1,max p.2 q.2)∈perturbClosed (0 : Space n) (1/2) 0 :=
  ⟨hp.1,hp.2.1.trans (le_max_left _ _),max_le hp.2.2 hq.2.2⟩

theorem perturb_half_buffer {n : ℕ} {z : Point n}
    (hz : z∈perturbClosed (0 : Space n) (1/2) 0) :
    perturbClosed z.1 (1/4) z.2 ⊆ backward 1 := by
  intro p hp
  have hzX : ‖z.1‖ ≤ 1/2 := by simpa using hz.1
  have hpX : ‖p.1-z.1‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
  have hn : ‖p.1‖ ≤ ‖p.1-z.1‖+‖z.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (p.1-z.1) z.1
  have hpTime : z.2-(1/4 : ℝ)^2 ≤ p.2 := hp.2.1
  have hzTime : -(1/2 : ℝ)^2 ≤ z.2 := by simpa only [zero_sub] using hz.2.1
  refine ⟨?_,?_,hp.2.2.trans hz.2.2⟩
  · change dist p.1 0 < 1
    rw [dist_zero_right]
    linarith only [hzX,hpX,hn]
  · change -(1 : ℝ)^2 < p.2
    linarith only [hpTime,hzTime]

theorem perturb_half_subset_back {n : ℕ} :
    perturbClosed (0 : Space n) (1/2) 0 ⊆ backward 1 := by
  intro p hp
  exact perturb_half_buffer hp ⟨mem_closedBall_self (by norm_num),
    sub_le_self _ (sq_nonneg _),le_rfl⟩

end Yau.LeafProofs.L05Aux
