import Yau.LeafProofs.L05PerturbationGeometry

open Filter Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbCorePatchTop {n : ℕ} (p : Point n) (tau : ℝ) : ℝ := min 0 (p.2+(tau/2)^2/8)

def perturbCorePatchCenter {n : ℕ} (p : Point n) (tau : ℝ) : Point n :=
  (p.1,perturbCorePatchTop p tau)

theorem perturb_core_patch_top_bounds {n : ℕ} {tau : ℝ} {p : Point n}
    (hp : p∈perturbCore tau) :
    p.2 ≤ perturbCorePatchTop p tau ∧ perturbCorePatchTop p tau ≤ 0 ∧
      perturbCorePatchTop p tau ≤ p.2+(tau/2)^2/8 := by
  exact ⟨le_min hp.2.2 (by nlinarith only [sq_nonneg (tau/2)]),min_le_left _ _,min_le_right _ _⟩

theorem perturb_core_patch_closed_subset {n : ℕ} {tau : ℝ} (ht : 0 < tau)
    {p : Point n} (hp : p∈perturbCore tau) :
    perturbClosed p.1 (tau/2) (perturbCorePatchTop p tau) ⊆
      perturbBack (0 : Space n) (1/2) 0 := by
  have hTop := perturb_core_patch_top_bounds hp
  have hpNorm : ‖p.1‖ ≤ 1/2-tau := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  intro q hq
  have hqNorm : ‖q.1-p.1‖ ≤ tau/2 := by simpa only [mem_closedBall,dist_eq_norm] using hq.1
  have hTri : ‖q.1‖ ≤ ‖q.1-p.1‖+‖p.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q.1-p.1) p.1
  refine ⟨?_,?_,hq.2.2.trans hTop.2.1⟩
  · change dist q.1 0 < 1/2
    rw [dist_zero_right]
    linarith only [hpNorm,hqNorm,hTri,ht]
  · have hLower := hq.2.1
    have hpLower := hp.2.1
    change 0-(1/2 : ℝ)^2 < q.2
    nlinarith only [hLower,hpLower,hTop.1,sq_pos_of_pos ht]

theorem perturb_core_point_in_half_patch {n : ℕ} {tau : ℝ} (ht : 0 < tau)
    {p : Point n} (hp : p∈perturbCore tau) :
    p∈perturbBack p.1 (tau/4) (perturbCorePatchTop p tau) := by
  have hTop := perturb_core_patch_top_bounds hp
  refine ⟨mem_ball_self (by positivity),?_,hTop.1⟩
  change perturbCorePatchTop p tau-(tau/4)^2 < p.2
  nlinarith only [hTop.2.2,sq_pos_of_pos ht]

theorem perturb_core_point_time_interior_or_top {n : ℕ} {tau : ℝ} (ht : 0 < tau)
    {p : Point n} (hp : p∈perturbCore tau) :
    p.2 < perturbCorePatchTop p tau ∨ perturbCorePatchTop p tau=0 := by
  by_cases hTop : perturbCorePatchTop p tau=0
  · exact Or.inr hTop
  · left
    have he : perturbCorePatchTop p tau=p.2+(tau/2)^2/8 := by
      dsimp only [perturbCorePatchTop] at hTop ⊢
      rcases le_total 0 (p.2+(tau/2)^2/8) with h | h
      · exact False.elim (hTop (min_eq_left h))
      · exact min_eq_right h
    rw [he]
    nlinarith only [sq_pos_of_pos ht]

theorem perturb_back_relative_neighborhood {n : ℕ} {Q : Set (Point n)} {c : Space n} {R T : ℝ}
    (hQ : ∀ q∈Q, q.2 ≤ 0) {p : Point n} (hp : p∈perturbBack c R T)
    (hTop : p.2 < T ∨ T=0) :
    ∃ V : Set (Point n), IsOpen V ∧ p∈V ∧ Q∩V⊆perturbBack c R T := by
  rcases hTop with hTop | hTop
  · refine ⟨ball c R ×ˢ Ioo (T-R^2) T,isOpen_ball.prod isOpen_Ioo,⟨hp.1,hp.2.1,hTop⟩,?_⟩
    intro q hq
    exact ⟨hq.2.1,hq.2.2.1,hq.2.2.2.le⟩
  · refine ⟨ball c R ×ˢ Ioi (T-R^2),isOpen_ball.prod isOpen_Ioi,⟨hp.1,hp.2.1⟩,?_⟩
    intro q hq
    exact ⟨hq.2.1,hq.2.2,by rw [hTop]; exact hQ q hq.1⟩

theorem perturb_back_uniqueDiff {n : ℕ} {c : Space n} {R T : ℝ} {p : Point n}
    (hp : p∈perturbBack c R T) :
    UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈perturbBack c R T} p.2 := by
  have hFiber : {t : ℝ | (p.1,t)∈perturbBack c R T}=Ioc (T-R^2) T := by
    ext t
    simp [perturbBack,hp.1]
  rw [hFiber]
  exact uniqueDiffOn_Ioc _ _ p.2 hp.2

theorem perturb_core_uniqueDiff {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau) (htb : tau ≤ 1/8)
    {p : Point n} (hp : p∈perturbCore tau) :
    UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈perturbCore tau} p.2 := by
  have hFiber : {t : ℝ | (p.1,t)∈perturbCore tau}=Icc (-(1/2 : ℝ)^2+tau^2) 0 := by
    ext t
    simp only [perturbCore,mem_setOf_eq,mem_prod,hp.1,true_and]
  have hTime : -(1/2 : ℝ)^2+tau^2 < 0 := by nlinarith
  rw [hFiber]
  exact uniqueDiffOn_Icc hTime p.2 hp.2

end Yau.LeafProofs.L05Aux
