import Yau.Proofs.C04HermitianHessianTraceDifferential
import Yau.Geometry.Basic

/-! The real trace of the actual scalar covariant Hessian cancels in each
complex-compatible pair. The frame need not be invertible. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hessian_diagonal_complex_pair_neg (H : E → E → ℂ) (J : E → E)
    (hsym : ∀ v w, H v w = H w v)
    (hcomplex : ∀ v w, H v (J w) = Complex.I * H v w) (v : E) :
    H (J v) (J v) = -H v v := by
  calc
    H (J v) (J v) = Complex.I * H (J v) v := hcomplex (J v) v
    _ = Complex.I * H v (J v) := by rw [hsym (J v) v]
    _ = Complex.I * (Complex.I * H v v) := by rw [hcomplex v v]
    _ = -H v v := by rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

theorem scalar_covariant_hessian_trace_zero {n : ℕ}
    (u : E → ℂ) (J : E → E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (hJ : DifferentiableAt ℝ J x)
    (G : E →L[ℝ] E →L[ℝ] E)
    (hpar : ∀ v w, fderiv ℝ J x v w + G v (J x w) = J x (G v w))
    (hrel : ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (hG : ∀ v w, G v w = G w v)
    (B : Yau.ComplexVector n →L[ℝ] E)
    (hB : ∀ v, B (Complex.I • v) = J x (B v)) :
    ∑ a : Yau.RIdx n,
      scalarCovariantHessian u x G (B (Yau.realVec a)) (B (Yau.realVec a)) = 0 := by
  have hdiag (v : E) : scalarCovariantHessian u x G (J x v) (J x v) =
      -scalarCovariantHessian u x G v v :=
    hessian_diagonal_complex_pair_neg (scalarCovariantHessian u x G) (J x)
      (scalar_covariant_hessian_symm u x hu G hG)
      (scalar_covariant_hessian_complex_right u J x hu hJ G hpar hrel) v
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Fin.sum_univ_two]
  have hpair : B (Yau.realVec (j, (1 : Fin 2))) = J x (B (Yau.realVec (j, 0))) := by
    have hv : Yau.realVec (j, (1 : Fin 2)) = Complex.I • Yau.realVec (j, (0 : Fin 2)) := by
      simp [Yau.realVec]
    rw [hv]
    exact hB _
  rw [hpair, hdiag]
  exact add_neg_cancel _

end Yau.Proofs.C04Aux
