import Yau.LeafProofs.L05PerturbationBoundaryBarriers

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_initial_collar_point {n : ℕ} {xi A : ℝ} (hA : 0 ≤ A)
    {p : Point n} (hp : p∈unitClosed n) (hNear : p.2 ≤ -1+xi^2) :
    ∃ z : Point n, z∈unitClosed n ∧ z.2=(-1 : ℝ) ∧ z.1=p.1 ∧
      |p.2-z.2| ≤ xi^2 ∧ perronInitialShape z A p ≤ A*xi^2 := by
  let z : Point n := (p.1,-1)
  have hLo : 0 ≤ p.2+1 := by linarith [hp.2.1]
  have hHi : p.2+1 ≤ xi^2 := by linarith only [hNear]
  refine ⟨z,⟨hp.1,by norm_num,by norm_num⟩,rfl,rfl,?_,?_⟩
  · change |p.2-(-1)| ≤ xi^2
    rw [sub_neg_eq_add,abs_of_nonneg hLo]
    exact hHi
  · rw [perronInitialShape_apply]
    change ‖p.1-p.1‖^2+A*(p.2-(-1)) ≤ A*xi^2
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),zero_add,sub_neg_eq_add] using
      mul_le_mul_of_nonneg_left hHi hA

theorem perturb_lateral_collar_point {n : ℕ} {xi K : ℝ} (hx : 0 < xi) (hxb : xi ≤ 1/4)
    (hK : 0 ≤ K) {p : Point n} (hp : p∈unitClosed n) (hNear : 1-xi ≤ ‖p.1‖) :
    ∃ z : Point n, z∈unitClosed n ∧ ‖z.1‖=1 ∧ z.2=p.2 ∧
      ‖p.1-z.1‖ ≤ xi ∧ perronLateralShape z K p ≤ (1+2*K)*xi := by
  let r := ‖p.1‖
  have hr : 0 < r := by dsimp only [r]; linarith only [hNear,hxb]
  have hr1 : r ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  let y := r⁻¹ • p.1
  have hy : ‖y‖=1 := by
    dsimp only [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hRep : p.1=r • y := by
    dsimp only [y]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hDist : ‖p.1-y‖=1-r := by
    calc
      _ = ‖(r-1) • y‖ := by rw [sub_smul,one_smul,← hRep]
      _ = 1-r := by
        rw [norm_smul,Real.norm_eq_abs,hy,mul_one,abs_of_nonpos (by linarith only [hr1])]
        ring
  have hInner : inner ℝ p.1 y=r := by
    calc
      _ = inner ℝ (r • y) y := congrArg (fun x => inner ℝ x y) hRep
      _ = r := by simp only [inner_smul_left,conj_trivial,smul_eq_mul,real_inner_self_eq_norm_sq,hy,one_pow,mul_one]
  let z : Point n := (y,p.2)
  have hz : z∈unitClosed n := by
    refine ⟨?_,hp.2⟩
    change dist y 0 ≤ 1
    rw [dist_zero_right,hy]
  refine ⟨z,hz,hy,rfl,?_,?_⟩
  · change ‖p.1-y‖ ≤ xi
    rw [hDist]
    linarith only [hNear]
  · rw [perronLateralShape_apply (p := z) hy p K]
    change 1-inner ℝ p.1 y+K*(1-‖p.1‖^2)+(p.2-p.2)^2 ≤ (1+2*K)*xi
    rw [hInner,sub_self,zero_pow (by norm_num : 2≠0),add_zero]
    change 1-r+K*(1-r^2) ≤ (1+2*K)*xi
    have hOne : 1-r ≤ xi := by linarith only [hNear]
    have hSquare : 1-r^2 ≤ 2*xi := by nlinarith only [sq_nonneg (1-r),hOne]
    have hMul := mul_le_mul_of_nonneg_left hSquare hK
    nlinarith only [hOne,hMul]

end Yau.LeafProofs.L05Aux
