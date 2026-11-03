import Yau.Proofs.Y05CoefficientSeries
import Yau.Proofs.Y05CompositionEstimates

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Blueprint.Alignment
open scoped ContDiff BigOperators

variable {n d : ℕ}

theorem polynomial_expansion_on_scalarMonomials (P : MvPolynomial (Fin n) ℂ)
    (hP : P.totalDegree ≤ d) :
    P = ∑ a ∈ scalarMonomials n d, monomial a (P.coeff a) := by
  classical
  have hS : P.support ⊆ scalarMonomials n d := fun a ha =>
    mem_scalarMonomials.mpr ((le_totalDegree ha).trans hP)
  calc
    P = ∑ a ∈ P.support, monomial a (P.coeff a) := (support_sum_monomial_coeff P).symm
    _ = _ := by
      apply Finset.sum_subset hS
      intro a ha hnot
      rw [notMem_support_iff.mp hnot, monomial_zero]

theorem scalarEval_precomp_expansion (P : MvPolynomial (Fin n) ℂ) (hP : P.totalDegree ≤ d)
    (F : ComplexVector n → ComplexVector n) :
    (fun z => scalarEval P (F z)) = fun z => ∑ a ∈ scalarMonomials n d,
      P.coeff a • scalarEval (monomial a (1 : ℂ)) (F z) := by
  classical
  funext z
  conv_lhs => rw [polynomial_expansion_on_scalarMonomials P hP]
  simp only [scalarEval, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hm : monomial a (P.coeff a) = C (P.coeff a) * monomial a (1 : ℂ) := by
    simp only [C_mul_monomial, mul_one]
  rw [hm, map_mul]
  simp [smul_eq_mul]

theorem iteratedFDeriv_polynomial_precomp_expansion
    (P : MvPolynomial (Fin n) ℂ) (hP : P.totalDegree ≤ d)
    {F : ComplexVector n → ComplexVector n} {m : ℕ} (hF : ContDiffAt ℂ m F 0) :
    iteratedFDeriv ℂ m (fun z => scalarEval P (F z)) 0 =
      ∑ a ∈ scalarMonomials n d, P.coeff a •
        iteratedFDeriv ℂ m (fun z => scalarEval (monomial a (1 : ℂ)) (F z)) 0 := by
  have hsmooth (a : Fin n →₀ ℕ) : ContDiffAt ℂ m
      (fun z => scalarEval (monomial a (1 : ℂ)) (F z)) 0 :=
    ((Yau.Proofs.Y01Aux.polyEval_contDiff (monomial a (1 : ℂ))).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp 0 hF
  rw [scalarEval_precomp_expansion P hP F]
  rw [iteratedFDeriv_fun_sum_apply (fun a ha =>
    (hsmooth a).const_smul (P.coeff a))]
  apply Finset.sum_congr rfl
  intro a ha
  exact iteratedFDeriv_const_smul_apply' (a := P.coeff a) (hsmooth a)

/-- Differentiating a bounded-degree polynomial after a fixed smooth germ
is a finite linear operation on its coefficients. -/
theorem hasSum_polynomial_precomp_jets
    {B : ℕ → MvPolynomial (Fin n) ℂ} {L : MvPolynomial (Fin n) ℂ}
    (hB : ∀ r, (B r).totalDegree ≤ d) (hL : L.totalDegree ≤ d)
    (hcoeff : ∀ a, HasSum (fun r => (B r).coeff a) (L.coeff a))
    {F : ComplexVector n → ComplexVector n} {m : ℕ} (hF : ContDiffAt ℂ m F 0) :
    HasSum (fun r => iteratedFDeriv ℂ m (fun z => scalarEval (B r) (F z)) 0)
      (iteratedFDeriv ℂ m (fun z => scalarEval L (F z)) 0) := by
  rw [iteratedFDeriv_polynomial_precomp_expansion L hL hF]
  have H := hasSum_sum (s := scalarMonomials n d) (fun a ha =>
    (hcoeff a).smul_const (iteratedFDeriv ℂ m
      (fun z => scalarEval (monomial a (1 : ℂ)) (F z)) 0))
  convert H using 1
  funext r
  exact iteratedFDeriv_polynomial_precomp_expansion (B r) (hB r) hF

end Yau.Proofs.Y05Aux
