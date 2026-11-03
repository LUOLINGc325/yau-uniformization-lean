import Yau.LeafProofs.L05PerturbationHolderGeometry

open Filter Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_core_open_subset_core {n : ℕ} (tau : ℝ) :
    perturbCoreOpen (n := n) tau⊆perturbCore tau :=
  fun _ hp => ⟨ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩

theorem perturb_core_open_subset_original {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau) :
    perturbCoreOpen (n := n) tau⊆backward 1 :=
  fun _ hp => perturb_half_subset_back (perturbCore_subset_closed ht (perturb_core_open_subset_core tau hp))

theorem perturb_core_boundary_subset_core {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau) (htb : tau ≤ 1/8) :
    perturbCoreBoundary (n := n) tau⊆perturbCore tau := by
  have hLower : -(1/2 : ℝ)^2+tau^2 ≤ 0 := by nlinarith
  intro p hp
  rcases hp with hp | hp
  · have hpT : p.2=-(1/2 : ℝ)^2+tau^2 := mem_singleton_iff.mp hp.2
    exact ⟨hp.1,by rw [hpT],by rw [hpT]; exact hLower⟩
  · exact ⟨sphere_subset_closedBall hp.1,hp.2⟩

theorem perturb_core_boundary_subset_collar {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau) (htb : tau ≤ 1/8) :
    perturbCoreBoundary (n := n) tau⊆perturbCollar tau := by
  intro p hp
  refine ⟨perturbCore_subset_closed ht (perturb_core_boundary_subset_core ht htb hp),?_⟩
  rcases hp with hp | hp
  · right
    exact (mem_singleton_iff.mp hp.2).le
  · left
    have hpNorm : ‖p.1‖=1/2-tau := by simpa only [mem_sphere,dist_zero_right] using hp.1
    exact hpNorm.ge

theorem perturb_comparison_budget {C K delta t : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hd : 0 ≤ delta) (ht : 0 ≤ t) :
    C*(delta*(2+K*t)) ≤ (1+C*(2+K))*delta*(1+t) := by
  have hExtra : 0 ≤ delta*(1+t)+C*delta*K+2*C*delta*t := by positivity
  nlinarith only [hExtra]

end Yau.LeafProofs.L05Aux
