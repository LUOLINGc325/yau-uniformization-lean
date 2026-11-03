import Yau.LeafProofs.L05PerturbationCoordinates

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbScaleValue {n : ℕ} (u : Point n → ℝ) (r N : ℝ) (p : Point n) : ℝ :=
  u (perturbScale r p)/N

theorem perturb_scale_back_mem {n : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) : perturbScale r p∈backward 1 := by
  have hx : ‖p.1‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hp.1
  have ht : -1 < p.2 := by simpa only [one_pow] using hp.2.1
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hTime := mul_pos (sq_pos_of_pos hr) (show 0 < p.2+1 by linarith)
  refine ⟨?_,?_,?_⟩
  · change dist (r • p.1) 0 < 1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left hx hr).trans_le (by simpa only [mul_one] using hr1)
  · change -(1 : ℝ)^2 < r^2*p.2
    nlinarith only [hTime,hr2]
  · change r^2*p.2 ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hp.2.2

theorem perturb_scaleValue_time_hasDerivWithinAt {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) :
    HasDerivWithinAt (fun t => perturbScaleValue u r N (p.1,t))
      ((r^2/N)*timeD (backward 1) u (perturbScale r p)) (Ioc (-1 : ℝ) 0) p.2 := by
  have hq := perturb_scale_back_mem hr hr1 hp
  have hqx : r • p.1∈ball (0 : Space n) 1 := hq.1
  have hSlice : {t : ℝ | (r • p.1,t)∈backward 1}=Ioc (-1 : ℝ) 0 := by
    ext t
    simp only [backward,mem_setOf_eq,mem_prod,hqx,true_and,one_pow]
  have hd := (hu.2.2.2.2.2 _ hq).hasDerivWithinAt
  change HasDerivWithinAt (fun t => u (r • p.1,t))
    (timeD (backward 1) u (perturbScale r p))
    {t : ℝ | (r • p.1,t)∈backward 1} (r^2*p.2) at hd
  rw [hSlice] at hd
  have hm : MapsTo (fun t : ℝ => r^2*t) (Ioc (-1 : ℝ) 0) (Ioc (-1 : ℝ) 0) := by
    intro t ht
    have hpt : (p.1,t)∈backward 1 := ⟨hp.1,by simpa only [one_pow] using ht⟩
    simpa only [perturbScale,one_pow] using (perturb_scale_back_mem hr hr1 hpt).2
  have hLine := ((hasDerivAt_id p.2).const_mul (r^2)).hasDerivWithinAt (s := Ioc (-1 : ℝ) 0)
  have hh := (hd.comp p.2 hLine hm).div_const N
  convert! hh using 1
  simp only [mul_one]
  ring

theorem perturb_scaleValue_timeD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) :
    timeD (backward 1) (perturbScaleValue u r N) p=
      (r^2/N)*timeD (backward 1) u (perturbScale r p) := by
  have hSlice : {t : ℝ | (p.1,t)∈backward 1}=Ioc (-1 : ℝ) 0 := by
    ext t
    simp only [backward,mem_setOf_eq,mem_prod,hp.1,true_and,one_pow]
  unfold timeD
  rw [hSlice]
  exact (perturb_scaleValue_time_hasDerivWithinAt hu hr hr1 hp).derivWithin
    (uniqueDiffOn_Ioc _ _ p.2 (by simpa only [one_pow] using hp.2))

end Yau.LeafProofs.L05Aux
