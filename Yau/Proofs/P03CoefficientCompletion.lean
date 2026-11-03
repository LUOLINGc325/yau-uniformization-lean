import Yau.LeafProofs.L14

open scoped Matrix

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Completing a square in the actual coefficient Hermitian pairing. -/
theorem coefficientInner_real_completion (g : HermitianField M) (h : Metric (M := M) E)
    (x : M.Carrier) (F V : Fin n → Fin r → ℂ) (t : ℝ) :
    (coefficientInner (r := r) E g h x (F + (-t : ℂ) • V) (F + (-t : ℂ) • V)).re =
      (coefficientInner (r := r) E g h x F F).re -
        2 * t * (coefficientInner (r := r) E g h x F V).re +
        t ^ 2 * (coefficientInner (r := r) E g h x V V).re := by
  have hsym := congrArg Complex.re (coefficientInner_conj_symm E g h x F V)
  simp only [Complex.star_def, Complex.conj_re] at hsym
  rw [coefficientInner_add_left, coefficientInner_add_right, coefficientInner_add_right,
    coefficientInner_smul_left, coefficientInner_smul_left,
    coefficientInner_smul_right, coefficientInner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, neg_zero, zero_mul, sub_zero, hsym]
  ring

end Yau.NodeProofs.P03Aux
