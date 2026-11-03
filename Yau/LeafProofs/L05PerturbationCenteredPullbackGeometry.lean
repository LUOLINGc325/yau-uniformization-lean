import Yau.LeafProofs.L05PerturbationAffineInverse

open Filter Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_inverse_center_closed_mem {n : ℕ} {r R : ℝ} (hr : 0 < r) (z : Point n)
    {p : Point n} (hp : p∈perturbClosed z.1 R z.2) :
    perturbCenter (perturbInverseCenter z r) r⁻¹ p∈perturbClosed (0 : Space n) (R/r) 0 := by
  have hx : ‖p.1-z.1‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
  have hLo : -R^2 ≤ p.2-z.2 := by linarith only [hp.2.1]
  have hHi : p.2-z.2 ≤ 0 := sub_nonpos.mpr hp.2.2
  have hLoScale : (r⁻¹)^2*(-R^2)=-(R/r)^2 := by field_simp [hr.ne']  <;>  ring
  rw [perturb_inverse_center_apply]
  refine ⟨?_,?_,?_⟩
  · change dist (r⁻¹ • (p.1-z.1)) 0 ≤ R/r
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left hx (inv_pos.mpr hr).le).trans_eq (by ring)
  · change 0-(R/r)^2 ≤ (r⁻¹)^2*(p.2-z.2)
    have hh := mul_le_mul_of_nonneg_left hLo (sq_nonneg (r⁻¹))
    rw [hLoScale] at hh
    simpa only [zero_sub] using hh
  · change (r⁻¹)^2*(p.2-z.2) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hHi

end Yau.LeafProofs.L05Aux
