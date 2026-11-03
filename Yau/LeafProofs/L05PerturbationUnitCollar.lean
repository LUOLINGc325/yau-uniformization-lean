import Yau.LeafProofs.L05PerturbationCollarGeometry

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbBoundaryBudget (n : ℕ) (ell L kappa H0 : ℝ) : ℝ :=
  H0+2*(H0*(2+2*perturbShapeMax n ell L))*
    ((1+2*perturbLateralCoefficient n ell)^(kappa/4)+(perturbInitialSpeed n L)^(kappa/4))

theorem perturb_boundary_budget_nonneg {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (kappa : ℝ) {H0 : ℝ} (hH0 : 0 ≤ H0) :
    0 ≤ perturbBoundaryBudget n ell L kappa H0 := by
  have hK := (perturb_lateral_coefficient_pos hn hell).le
  have hA : 0 ≤ perturbInitialSpeed n L := by
    have hh := perturb_initial_speed_ge_two n (hell.le.trans hL)
    linarith
  have hS := perturb_shapeMax_ge_one n ell (hell.le.trans hL)
  have hB : 0 ≤ H0*(2+2*perturbShapeMax n ell L) := mul_nonneg hH0 (by linarith)
  exact add_nonneg hH0 (mul_nonneg (mul_nonneg (by norm_num) hB)
    (add_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1+2*perturbLateralCoefficient n ell) _)
      (Real.rpow_nonneg hA _)))

theorem perturb_square_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x^2)^a=x^(2*a) := by
  simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hx 2 a).symm

theorem perturb_unit_collar {n : ℕ} (hn : 0 < n) {ell L kappa H0 : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hk0 : 0 < kappa) (hk1 : kappa < 1)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {g h : Point n → ℝ} (hG : HolderBound kappa (unitClosed n) g H0)
    (hC : ContinuousOn h (unitClosed n)) (hEq : EqOn h g (parabolicBoundary n))
    (hSol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) h)
    {xi : ℝ} (hx : 0 < xi) (hxb : xi ≤ 1/4) {p : Point n} (hp : p∈unitClosed n)
    (hNear : 1-xi ≤ ‖p.1‖ ∨ p.2 ≤ -1+xi^2) :
    |g p-h p| ≤ perturbBoundaryBudget n ell L kappa H0*xi^(kappa/4) := by
  let K := perturbLateralCoefficient n ell
  let A := perturbInitialSpeed n L
  let Bbar := H0*(2+2*perturbShapeMax n ell L)
  let nu := kappa/4
  have hK : 0 ≤ K := (perturb_lateral_coefficient_pos hn hell).le
  have hA : 0 ≤ A := by
    have hh := perturb_initial_speed_ge_two n (hell.le.trans hL)
    change 0 ≤ perturbInitialSpeed n L
    linarith
  have hS := perturb_shapeMax_ge_one n ell (hell.le.trans hL)
  have hB : 0 ≤ Bbar := mul_nonneg hG.1 (by linarith)
  have hn0 : 0 < nu := by dsimp only [nu]; positivity
  have hnK : nu ≤ kappa := by dsimp only [nu]; linarith
  have hx1 : xi ≤ 1 := by linarith
  have hXpow : xi^kappa ≤ xi^nu := Real.rpow_le_rpow_of_exponent_ge hx hx1 hnK
  have hXp0 := Real.rpow_nonneg hx.le nu
  change |g p-h p| ≤ (H0+2*Bbar*((1+2*K)^nu+A^nu))*xi^nu
  rcases hNear with hNear | hNear
  · obtain ⟨z,hz,hzn,hzt,hDist,hShape⟩ := perturb_lateral_collar_point hx hxb hK hp hNear
    have hHolder := hG.2.2 p hp z hz
    rw [Real.norm_eq_abs,holderWeight,hzt,sub_self,abs_zero,
      Real.zero_rpow (show kappa/2≠0 by positivity),add_zero] at hHolder
    have hDp := Real.rpow_le_rpow (norm_nonneg (p.1-z.1)) hDist hk0.le
    have hData : |g p-g z| ≤ H0*xi^nu :=
      hHolder.trans ((mul_le_mul_of_nonneg_left hDp hG.1).trans
        (mul_le_mul_of_nonneg_left hXpow hG.1))
    have hBarrier := perturb_lateral_boundary_barrier hn hell hL hF hE h0 hk0 hk1 hG hC hEq hSol hz hzn p hp
    change |h p-g z| ≤ 2*Bbar*(perronLateralShape z K p)^nu at hBarrier
    have hShape0 := (perturb_lateral_shape_bounds (L := L) hK hz hzn hp).1
    have hSpow := Real.rpow_le_rpow hShape0 hShape hn0.le
    rw [Real.mul_rpow (by linarith : 0 ≤ 1+2*K) hx.le] at hSpow
    have hBar : |h p-g z| ≤ 2*Bbar*(1+2*K)^nu*xi^nu := by
      have hh := hBarrier.trans (mul_le_mul_of_nonneg_left hSpow (mul_nonneg (by norm_num) hB))
      simpa only [mul_assoc] using hh
    have hTri := abs_sub_le (g p) (g z) (h p)
    rw [abs_sub_comm (g z) (h p)] at hTri
    have hExtra : 0 ≤ 2*Bbar*A^nu*xi^nu := mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hB) (Real.rpow_nonneg hA nu)) hXp0
    nlinarith only [hData,hBar,hTri,hExtra]
  · obtain ⟨z,hz,hzt,hzx,hTime,hShape⟩ := perturb_initial_collar_point hA hp hNear
    have hHolder := hG.2.2 p hp z hz
    rw [Real.norm_eq_abs,holderWeight,hzx,sub_self,norm_zero,Real.zero_rpow hk0.ne',zero_add] at hHolder
    have hTp := Real.rpow_le_rpow (abs_nonneg (p.2-z.2)) hTime
      (show 0 ≤ kappa/2 by positivity)
    rw [perturb_square_rpow hx.le,show 2*(kappa/2)=kappa from by ring] at hTp
    have hData : |g p-g z| ≤ H0*xi^nu :=
      hHolder.trans ((mul_le_mul_of_nonneg_left hTp hG.1).trans
        (mul_le_mul_of_nonneg_left hXpow hG.1))
    have hBarrier := perturb_initial_boundary_barrier hn hell hL hF hE h0 hk0 hk1 hG hC hEq hSol hz hzt p hp
    change |h p-g z| ≤ 2*Bbar*(perronInitialShape z A p)^nu at hBarrier
    have hShape0 := (perturb_initial_shape_bounds (ell := ell) (hell.le.trans hL) hz hzt hp).1
    have hSpow := Real.rpow_le_rpow hShape0 hShape hn0.le
    rw [Real.mul_rpow hA (sq_nonneg xi),perturb_square_rpow hx.le] at hSpow
    have hDouble : xi^(2*nu) ≤ xi^nu :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith only [hn0])
    have hSpow' : (perronInitialShape z A p)^nu ≤ A^nu*xi^nu :=
      hSpow.trans (mul_le_mul_of_nonneg_left hDouble (Real.rpow_nonneg hA nu))
    have hBar : |h p-g z| ≤ 2*Bbar*A^nu*xi^nu := by
      have hh := hBarrier.trans (mul_le_mul_of_nonneg_left hSpow' (mul_nonneg (by norm_num) hB))
      simpa only [mul_assoc] using hh
    have hTri := abs_sub_le (g p) (g z) (h p)
    rw [abs_sub_comm (g z) (h p)] at hTri
    have hExtra : 0 ≤ 2*Bbar*(1+2*K)^nu*xi^nu := mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hB) (Real.rpow_nonneg (by linarith : 0 ≤ 1+2*K) nu)) hXp0
    nlinarith only [hData,hBar,hTri,hExtra]

end Yau.LeafProofs.L05Aux
