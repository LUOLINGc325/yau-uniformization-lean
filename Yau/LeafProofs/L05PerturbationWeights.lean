import Yau.LeafProofs.L05PerturbationGeometry

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_scale_weight {n : ℕ} {r sigma : ℝ} (hr : 0<r) (p q : Point n) :
    holderWeight sigma (perturbScale r p) (perturbScale r q)=
      r^sigma*holderWeight sigma p q := by
  have he : (r^2)^(sigma/2)=r^sigma := by
    calc
      _ = (r^(2 : ℝ))^(sigma/2) := by rw [Real.rpow_two]
      _ = r^((2 : ℝ)*(sigma/2)) := (Real.rpow_mul hr.le _ _).symm
      _ = _ := by congr 1; ring
  change ‖r • p.1-r • q.1‖^sigma+|r^2*p.2-r^2*q.2|^(sigma/2)=_
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,← mul_sub,
    abs_mul,abs_of_nonneg (sq_nonneg r),Real.mul_rpow hr.le (norm_nonneg _),
    Real.mul_rpow (sq_nonneg r) (abs_nonneg _),he]
  unfold holderWeight
  ring

theorem perturb_center_weight {n : ℕ} (z : Point n) {r sigma : ℝ} (hr : 0<r)
    (p q : Point n) :
    holderWeight sigma (perturbCenter z r p) (perturbCenter z r q)=
      r^sigma*holderWeight sigma p q := by
  simpa only [holderWeight,perturbCenter,perturbScale,add_sub_add_left_eq_sub] using
    perturb_scale_weight (sigma := sigma) hr p q

theorem perturb_closed_weight_origin {n : ℕ} {sigma : ℝ} (hs : 0<sigma)
    {p : Point n} (hp : p ∈ perturbClosed (0 : Space n) 1 0) :
    holderWeight sigma p (0,0) ≤ 2 := by
  have hx : ‖p.1‖≤1 := by simpa using hp.1
  have ht : |p.2|≤1 := by
    rw [abs_of_nonpos hp.2.2]
    have hh := hp.2.1
    norm_num at hh
    linarith
  have h1 := Real.rpow_le_one (norm_nonneg p.1) hx hs.le
  have h2 := Real.rpow_le_one (abs_nonneg p.2) ht (by linarith : 0 ≤ sigma / 2)
  dsimp only [holderWeight]
  simp only [sub_zero]
  linarith

end Yau.LeafProofs.L05Aux
