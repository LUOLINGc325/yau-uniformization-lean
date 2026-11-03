import Yau.Proofs.C05ComplexMatrixDerivative

/-! Entrywise product differentiation does not require changing the matrix norm. -/

noncomputable section
namespace Yau.Proofs.C05Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_complex_matrix_mul {A B : ℝ → Matrix ι ι ℂ}
    {A' B' : Matrix ι ι ℂ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : ι) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hA i l).mul (hB l j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using hd

end Yau.Proofs.C05Aux
