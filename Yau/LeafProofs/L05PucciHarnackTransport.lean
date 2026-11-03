import Yau.LeafProofs.L05PucciHarnackAlgebra
import Yau.LeafProofs.L05ABP

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_timeD_add_const {n : ℕ} (phi : Point n → ℝ) (a : ℝ) (p : Point n) :
    timeD univ (fun z => phi z+a) p=timeD univ phi p := by
  simpa only [sub_neg_eq_add] using timeD_sub_const phi (-a) p

theorem harnack_hessian_add_const {n : ℕ} (phi : Point n → ℝ) (a : ℝ) (p : Point n) :
    hessian (fun z => phi z+a) p=hessian phi p := by
  simpa only [sub_neg_eq_add] using hessian_sub_const phi (-a) p

theorem harnack_timeD_const_mul {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) (a : ℝ) :
    timeD univ (fun z => a*phi z) p=a*timeD univ phi p := by
  have hMul : ContDiffAt ℝ 2 (fun z => a*phi z) p := contDiffAt_const.mul hphi
  rw [timeD_univ_eq_joint (hMul.differentiableAt (by norm_num)),
    timeD_univ_eq_joint (hphi.differentiableAt (by norm_num)),
    fderiv_const_mul (hphi.differentiableAt (by norm_num))]
  rfl

theorem harnack_hessian_const_mul {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) (a : ℝ) :
    hessian (fun z => a*phi z) p=a • hessian phi p := by
  rw [jet_hessian_eq_joint_at (contDiffAt_const.mul hphi),jet_hessian_eq_joint_at hphi]
  have hSecond : fderiv ℝ (fderiv ℝ (fun z => a*phi z)) p=a • fderiv ℝ (fderiv ℝ phi) p := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    have h := congrArg (fun A => A ![v,w]) (iteratedFDeriv_const_smul_apply (a := a) hphi)
    simpa only [Pi.smul_def,iteratedFDeriv_two_apply,smul_apply,Pi.smul_apply,
      smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  rw [hSecond,jet_jointHessian_smul]

theorem harnack_super0_div {n : ℕ} {ell L h : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (hh : 0<h) {u : Point n → ℝ} (hu : harnackSuper0 ell L u) :
    harnackSuper0 ell L (fun z => u z/h) := by
  refine ⟨hu.1.div_const h,fun z hz => div_nonneg (hu.2.1 z hz) hh.le,?_⟩
  intro p hp psi hpsi ht
  have hTest : touchBelow (fun z => h*psi z) u p := by
    refine ⟨?_,?_⟩
    · have he := ht.1
      change psi p=u p/h at he
      change h*psi p=u p
      rw [he]
      field_simp [hh.ne']
    · filter_upwards [ht.2] with z hz
      change psi z≤u z/h at hz
      simpa only [mul_comm] using (le_div_iff₀ hh).mp hz
  have hS := hu.2.2 p hp _ (contDiffAt_const.mul hpsi) hTest
  change 0≤timeD univ (fun z => h*psi z) p-
    harnackPucciMinus ell L (hessian (fun z => h*psi z) p) at hS
  rw [harnack_timeD_const_mul hpsi,harnack_hessian_const_mul hpsi,
    harnack_minus_smul hell hL hh.le] at hS
  nlinarith

theorem harnack_boundary_subset_unitClosed {n : ℕ} {z : Point n}
    (hz : z∈parabolicBoundary n) : z∈unitClosed n := by
  rcases hz with hz | hz
  · exact ⟨hz.1,by rw [show z.2=(-1 : ℝ) from hz.2]; norm_num⟩
  · exact ⟨Metric.sphere_subset_closedBall hz.1,hz.2⟩

theorem harnack_smooth_unit_comparison {n : ℕ} {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) {u Phi : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (hPhi : ContDiff ℝ 2 Phi)
    (hSuper : viscositySuper (unitOpen n)
      (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u)
    (hRes : ∀ z∈unitOpen n, timeD univ Phi z-harnackPucciMinus ell L (hessian Phi z)≤0)
    (hBd : ∀ z∈parabolicBoundary n, Phi z≤u z) :
    ∀ z∈unitClosed n, Phi z≤u z := by
  have hw := hPhi.continuous.continuousOn.sub hu
  have hSub := harnack_smooth_minus_super_sub hell.le hL
    (fun z _ => hPhi.contDiffAt) hSuper hRes
  have hBoundary : ∀ z∈parabolicBoundary n, Phi z-u z≤0 := by
    intro z hz
    exact sub_nonpos.mpr (hBd z hz)
  intro z hz
  have h := viscosity_abp_closed hell hL hw continuousOn_const hBoundary hSub hz
  have hz0 : (Phi-u) z≤0 := by
    simpa only [max_self,zero_pow (by omega : 2*n+1≠0),integral_zero,
      Real.zero_rpow (by positivity : (1 : ℝ)/((2*n+1 : ℕ) : ℝ)≠0),mul_zero] using h
  change Phi z-u z≤0 at hz0
  exact sub_nonpos.mp hz0

end Yau.LeafProofs.L05Aux
