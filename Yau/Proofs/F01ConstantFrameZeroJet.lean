import Yau.Proofs.F01WirtingerMatrixCongruence

/-! A constant complex frame change preserves a genuinely differentiable
zero real metric jet. The differentiability hypothesis is explicit. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem constant_congruence_real_jet_zero
    (A : Matrix (Fin n) (Fin n) ℂ)
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : DifferentiableAt ℝ T z)
    (hG : ∀ i j, DifferentiableAt ℝ (fun w => G w i j) (T z))
    (hzero : ∀ i j, fderiv ℝ (fun w => G w i j) (T z) = 0) (i j : Fin n) :
    fderiv ℝ (fun w => (Aᴴ * G (T w) * A) i j) z = 0 := by
  have hentry (p q : Fin n) : HasFDerivAt (fun w => G (T w) p q)
      (0 : ComplexVector n →L[ℝ] ℂ) z := by
    have hd : fderiv ℝ (fun w => G (T w) p q) z = 0 := by
      change fderiv ℝ ((fun w => G w p q) ∘ T) z = 0
      rw [fderiv_comp z (hG p q) hT, hzero p q, ContinuousLinearMap.zero_comp]
    rw [← hd]
    exact ((hG p q).comp z hT).hasFDerivAt
  have hterm (p q : Fin n) :
      HasFDerivAt (fun w => star (A p i) * G (T w) p q * A q j)
        (0 : ComplexVector n →L[ℝ] ℂ) z := by
    convert ((hentry p q).const_mul (star (A p i))).mul_const (A q j) using 1
    ext v
    simp
  have hrow (q : Fin n) :
      HasFDerivAt (fun w => ∑ p, star (A p i) * G (T w) p q * A q j)
        (0 : ComplexVector n →L[ℝ] ℂ) z := by
    simpa using HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ => hterm p q)
  have hs : HasFDerivAt
      (fun w => ∑ q, ∑ p, star (A p i) * G (T w) p q * A q j)
        (0 : ComplexVector n →L[ℝ] ℂ) z := by
    simpa using HasFDerivAt.fun_sum (u := Finset.univ) (fun q _ => hrow q)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul] using hs.fderiv

end Yau.NodeProofs.F01Aux
