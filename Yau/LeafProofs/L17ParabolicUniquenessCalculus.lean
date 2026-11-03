import Yau.LeafProofs.L17ParabolicOperator
import Yau.LeafProofs.L16

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17ParabolicUniquenessAux
open L17Aux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ}

theorem secondFDeriv_sub {f h : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hh : ContDiffAt ℝ 2 h z) :
    fderiv ℝ (fderiv ℝ (fun y => f y-h y)) z =
      fderiv ℝ (fderiv ℝ f) z-fderiv ℝ (fderiv ℝ h) z := by
  have he : fderiv ℝ (fun y => f y-h y) =ᶠ[𝓝 z]
      fun y => fderiv ℝ f y-fderiv ℝ h y := by
    filter_upwards [hf.eventually (by norm_num), hh.eventually (by norm_num)] with y hy hy'
    exact fderiv_fun_sub (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_sub
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem secondFDeriv_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => c*f y)) z = c • fderiv ℝ (fderiv ℝ f) z := by
  have he : fderiv ℝ (fun y => c*f y) =ᶠ[𝓝 z] fun y => c • fderiv ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact fderiv_const_mul (hy.differentiableAt (by norm_num)) c
  rw [he.fderiv_eq]
  exact fderiv_fun_const_smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) c

theorem normSq_secondFDeriv (z : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y : ComplexVector n => ‖y‖^2)) z =
      (2 : ℝ) • L16Aux.realInnerBilinear := by
  have he : (fun y : ComplexVector n => ‖y‖^2) =
      fun y => L16Aux.quadraticBarrierSpace y-1 := by
    funext y
    simp [L16Aux.quadraticBarrierSpace]
  rw [he]
  rw [show fderiv ℝ (fun y : ComplexVector n => L16Aux.quadraticBarrierSpace y-1) =
      fderiv ℝ L16Aux.quadraticBarrierSpace from funext (fun _ => fderiv_sub_const 1)]
  exact congrFun L16Aux.quadraticBarrierSpace_secondFDeriv z

theorem contraction_penalized {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c k : ℝ) (a : Matrix (RIdx n) (RIdx n) ℝ) :
    realHessianContraction a (fun y => c*f y-k*‖y‖^2) z =
      c*realHessianContraction a f z-2*k*(∑ i, a i i) := by
  classical
  have hn : ContDiffAt ℝ 2 (fun y : ComplexVector n => ‖y‖^2) z :=
    (contDiff_id.norm_sq ℝ).contDiffAt
  rw [realHessianContraction, secondFDeriv_sub (contDiffAt_const.mul hf)
    (contDiffAt_const.mul hn), secondFDeriv_const_mul hf,
    secondFDeriv_const_mul hn, normSq_secondFDeriv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, L16Aux.realInnerBilinear_apply, L16Aux.realVec_inner,
    mul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ i, ∑ j, a i j*(c*fderiv ℝ (fderiv ℝ f) z (realVec i) (realVec j))) =
      c*realHessianContraction a f z := by
    simp only [realHessianContraction, Finset.mul_sum]
    congr 1
    funext i
    congr 1
    funext j
    ring
  rw [hfirst]
  congr 1
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem contraction_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (a : Matrix (RIdx n) (RIdx n) ℝ) :
    realHessianContraction a (fun y => c*f y) z = c*realHessianContraction a f z := by
  simpa using contraction_penalized hf c 0 a

theorem contraction_penalized_nonpos {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (k : ℝ) (a : Matrix (RIdx n) (RIdx n) ℝ)
    (ha : a.PosSemidef) (hm : IsLocalMax (fun y => f y-k*‖y‖^2) z) :
    realHessianContraction a f z ≤ 2*k*(∑ i, a i i) := by
  have hn : ContDiffAt ℝ 2 (fun y : ComplexVector n => ‖y‖^2) z :=
    (contDiff_id.norm_sq ℝ).contDiffAt
  have hc := L16Aux.bilinear_contraction_nonpos realVec
    (fderiv ℝ (fderiv ℝ (fun y => f y-k*‖y‖^2)) z) ha
    (L16Aux.secondFDeriv_nonpos_of_isLocalMax (hf.sub (contDiffAt_const.mul hn)) hm)
  change realHessianContraction a (fun y => f y-k*‖y‖^2) z ≤ 0 at hc
  have he := contraction_penalized hf 1 k a
  simp only [one_mul] at he
  rw [he] at hc
  linarith

theorem symbol_trace_le {M : ComplexManifold n} {g : HermitianField M}
    (A : BoundedChartFamily g) (p : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ ball 0 A.radius) :
    (∑ i, scalarSymbol (pullbackMatrix g (A.chart p) z) i i) ≤
      (Fintype.card (RIdx n) : ℝ)*(A.bound 0/4) := by
  classical
  calc
    _ ≤ ∑ _i : RIdx n, A.bound 0/4 := by
      apply Finset.sum_le_sum
      intro i hi
      have hd := (A.scalarSymbol_ellipticity p hz).2.diag_nonneg (i := i)
      simpa using hd
    _ = _ := by simp

end Yau.LeafProofs.L17ParabolicUniquenessAux
