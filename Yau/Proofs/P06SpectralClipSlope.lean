import Yau.Proofs.P06SpectralClipAlgebra

noncomputable section

namespace Yau.NodeProofs.P06Aux.Clip

def polynomialSlope {R : Type*} [CommRing R] (p : Polynomial R) (a b : R) : R :=
  ∑ m ∈ p.support, p.coeff m * powerSlope a b m

theorem polynomialSlope_mul_sub {R : Type*} [CommRing R] (p : Polynomial R) (a b : R) :
    polynomialSlope p a b * (a - b) = p.eval a - p.eval b := by
  classical
  rw [polynomialSlope, Finset.sum_mul, Polynomial.eval_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum, Polynomial.sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [mul_assoc, powerSlope_mul_sub]
  ring

theorem polynomialSlope_self {R : Type*} [CommRing R] (p : Polynomial R) (a : R) :
    polynomialSlope p a a = p.derivative.eval a := by
  classical
  simp only [polynomialSlope, powerSlope_self, Polynomial.derivative_eval, Polynomial.sum, mul_assoc]

/-- The actual polynomial divided differences are bounded sharply by one
on the spectral interval, including the derivative at repeated roots. -/
theorem polynomialSlope_abs_le_one (p : Polynomial ℝ) {R a b : ℝ}
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1)
    (ha : a ∈ Set.Icc (-R) R) (hb : b ∈ Set.Icc (-R) R) :
    |polynomialSlope p a b| ≤ 1 := by
  by_cases he : a = b
  · subst b
    rw [polynomialSlope_self]
    exact hder a ha
  · have hLip : |p.eval a - p.eval b| ≤ |a - b| := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun x : ℝ => p.eval x) (C := 1)
        (fun x _ => p.differentiableAt)
        (fun x hx => by rw [Polynomial.deriv, Real.norm_eq_abs]; exact hder x hx)
        (convex_Icc (-R) R) hb ha
      simpa only [Real.norm_eq_abs, one_mul] using h
    have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr he)
    have hs := congrArg abs (polynomialSlope_mul_sub p a b)
    rw [abs_mul] at hs
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      _ = |p.eval a - p.eval b| := hs
      _ ≤ |a - b| := hLip
      _ = 1 * |a - b| := (one_mul _).symm

end Yau.NodeProofs.P06Aux.Clip
