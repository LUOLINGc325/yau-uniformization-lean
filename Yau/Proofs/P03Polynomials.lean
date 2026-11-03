import Yau.Blueprint.Analytic

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The centered polynomial appearing in the native jet contract is a smooth
complex map on the actual Euclidean model. -/
theorem centeredPolynomial_contDiff (P : MvPolynomial (Fin n) ℂ)
    (c : ComplexVector n) :
    ContDiff ℂ ⊤ (fun z : ComplexVector n =>
      MvPolynomial.eval (fun i => z i - c i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ ⊤ (fun _ : ComplexVector n => a))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.eval_X, EuclideanSpace.coe_proj] using
      hP.mul ((EuclideanSpace.proj i).contDiff.sub contDiff_const)

theorem centeredPolynomial_differentiable (P : MvPolynomial (Fin n) ℂ)
    (c : ComplexVector n) :
    Differentiable ℂ (fun z : ComplexVector n =>
      MvPolynomial.eval (fun i => z i - c i) P) :=
  (centeredPolynomial_contDiff P c).differentiable (by simp)

theorem centeredPolynomial_real_contDiff (P : MvPolynomial (Fin n) ℂ)
    (c : ComplexVector n) :
    ContDiff ℝ ⊤ (fun z : ComplexVector n =>
      MvPolynomial.eval (fun i => z i - c i) P) :=
  (centeredPolynomial_contDiff P c).restrict_scalars ℝ

theorem centeredPolynomial_center (P : MvPolynomial (Fin n) ℂ)
    (c : ComplexVector n) :
    MvPolynomial.eval (fun i => c i - c i) P = MvPolynomial.constantCoeff P := by
  simp

end Yau.NodeProofs.P03Aux
