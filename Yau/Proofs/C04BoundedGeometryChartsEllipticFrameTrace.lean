import Yau.Proofs.C04BoundedGeometryChartsFrameTrace

/-! The displayed real-frame trace is exactly the scalar elliptic operator. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem complexLinear_eq_sum (L : ComplexVector n →L[ℝ] ℂ) (v : ComplexVector n) :
    L v = ∑ i : RIdx n, (realCoord v i : ℂ) * L (realVec i) := by
  have H := congrArg L (sum_realCoord_realVec v)
  rw [map_sum] at H
  simp only [map_smul] at H
  apply Complex.ext
  · simpa using congrArg Complex.re H.symm
  · simpa using congrArg Complex.im H.symm

theorem frameDrift_contraction
    (B : ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (L : ComplexVector n →L[ℝ] ℂ) :
    (∑ k : RIdx n, (frameDriftCoefficients B G k : ℂ) * L (realVec k)) =
      -(∑ i : RIdx n, ∑ j : RIdx n,
        (framePrincipalCoefficients B i j : ℂ) * L (G (realVec i) (realVec j))) := by
  calc
    _ = -(∑ k : RIdx n, ∑ i : RIdx n, ∑ j : RIdx n,
        (framePrincipalCoefficients B i j : ℂ) *
          (realCoord (G (realVec i) (realVec j)) k : ℂ) * L (realVec k)) := by
      simp only [frameDriftCoefficients, Complex.ofReal_neg, Complex.ofReal_sum,
        Complex.ofReal_mul, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
    _ = -(∑ i : RIdx n, ∑ j : RIdx n, ∑ k : RIdx n,
        (framePrincipalCoefficients B i j : ℂ) *
          (realCoord (G (realVec i) (realVec j)) k : ℂ) * L (realVec k)) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [complexLinear_eq_sum L]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

def scalarHessianMap (u : ComplexVector n → ℂ) (x : ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℂ :=
  fderiv ℝ (fderiv ℝ u) x -
    ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℂ) (fderiv ℝ u x)).comp G

theorem scalarHessianMap_apply (u : ComplexVector n → ℂ) (x : ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (v w : ComplexVector n) :
    scalarHessianMap u x G v w = C04Aux.scalarCovariantHessian u x G v w := rfl

theorem ellipticOp_eq_frame_trace
    (B : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (u : ComplexVector n → ℂ) (x : ComplexVector n) (hu : ContDiffAt ℝ 2 u x) :
    Yau.LeafCandidates.ellipticOp (fun y => framePrincipalCoefficients (B y))
        (fun y => frameDriftCoefficients (B y) (G y)) u x =
      (1 / 2 : ℂ) * ∑ c : RIdx n,
        C04Aux.scalarCovariantHessian u x (G x) (B x (realVec c)) (B x (realVec c)) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD (i j : RIdx n) :
      fderiv ℝ (fun y => fderiv ℝ u y (realVec j)) x (realVec i) =
        fderiv ℝ (fderiv ℝ u) x (realVec i) (realVec j) := by
    have H := congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L (realVec i))
      (fderiv_clm_apply hdu (differentiableAt_const (realVec j)))
    simpa only [fderiv_const_apply, add_apply, zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, map_zero, zero_add] using H
  have htrace := complexBilin_frame_trace (scalarHessianMap u x (G x)) (B x)
  simp only [scalarHessianMap_apply] at htrace
  rw [← htrace]
  simp only [scalarHessianMap_apply, Yau.LeafCandidates.ellipticOp, hD, frameDrift_contraction]
  simp only [C04Aux.scalarCovariantHessian, mul_sub, Finset.sum_sub_distrib, sub_eq_add_neg]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem ellipticOp_zero_of_covariant_complex
    (B : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (u : ComplexVector n → ℂ) (x : ComplexVector n) (hu : ContDiffAt ℝ 2 u x)
    (hJ : DifferentiableAt ℝ J x)
    (hpar : ∀ v w, fderiv ℝ J x v w + G x v (J x w) = J x (G x v w))
    (hrel : ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (hG : ∀ v w, G x v w = G x w v)
    (hB : ∀ v, B x (Complex.I • v) = J x (B x v)) :
    Yau.LeafCandidates.ellipticOp (fun y => framePrincipalCoefficients (B y))
      (fun y => frameDriftCoefficients (B y) (G y)) u x = 0 := by
  rw [ellipticOp_eq_frame_trace B G u x hu,
    C04Aux.scalar_covariant_hessian_trace_zero u J x hu hJ (G x) hpar hrel hG (B x) hB,
    mul_zero]

end Yau.Proofs.C04ChartsAux
