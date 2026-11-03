import Yau.Proofs.Y05Taylor
import Yau.Proofs.Y02CoefficientBounds
import Yau.Proofs.U02AnalyticRadius

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux MvPolynomial
open scoped BigOperators

variable {n m : ℕ}

theorem coefficientNorm_product_variables (I : Fin m → Fin n) (S : Finset (Fin m)) :
    polynomialCoeffNorm (∏ j ∈ S, (X (I j) : MvPolynomial (Fin n) ℂ)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [polynomialCoeffNorm]
  | @insert j S hj hS =>
    rw [Finset.prod_insert hj]
    have hX : polynomialCoeffNorm (X (I j) : MvPolynomial (Fin n) ℂ) = 1 := by
      simp [X, polynomialCoeffNorm_monomial]
    exact (polynomialCoeffNorm_mul _ _).trans (by simpa only [hX, one_mul] using hS)

theorem coefficientNorm_diagonalPolynomial
    (A : (ComplexVector n) [×m]→L[ℂ] ℂ) :
    polynomialCoeffNorm (diagonalPolynomial A) ≤ (n : ℝ) ^ m * ‖A‖ := by
  classical
  have hterm (I : Fin m → Fin n) : polynomialCoeffNorm
      (C (A (fun j => stdVec (I j))) * ∏ j, (X (I j) : MvPolynomial (Fin n) ℂ)) ≤ ‖A‖ := by
    rw [polynomialCoeffNorm_C_mul]
    apply (mul_le_mul_of_nonneg_left (coefficientNorm_product_variables I Finset.univ)
      (norm_nonneg _)).trans
    rw [mul_one]
    have hA := A.le_opNorm (fun j => stdVec (I j))
    have hnorm (j : Fin m) : ‖stdVec (I j)‖ = 1 := by
      change ‖(PiLp.single 2 (I j) (1 : ℂ) : ComplexVector n)‖ = 1
      simp
    simpa only [hnorm, Finset.prod_const_one, mul_one] using hA
  apply (polynomialCoeffNorm_sum _ _).trans
  calc
    _ ≤ ∑ _I : Fin m → Fin n, ‖A‖ := Finset.sum_le_sum (fun I _ => hterm I)
    _ = (n : ℝ) ^ m * ‖A‖ := by simp

theorem coefficientNorm_taylorPolynomial
    (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) :
    polynomialCoeffNorm (taylorPolynomial p d) ≤
      ∑ m ∈ Finset.range (d + 1), (n : ℝ) ^ m * ‖p m‖ := by
  exact (polynomialCoeffNorm_sum _ _).trans
    (Finset.sum_le_sum (fun m _ => coefficientNorm_diagonalPolynomial (p m)))

def scalarJetNorm (f : ComplexVector n → ℂ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), ‖iteratedFDeriv ℂ m f 0‖

def scalarTaylorConstant (n d : ℕ) : ℝ := ∑ m ∈ Finset.range (d + 1), (n : ℝ) ^ m

theorem coefficientNorm_canonical_taylor (f : ComplexVector n → ℂ) (d : ℕ) :
    polynomialCoeffNorm (taylorPolynomial (U02AnalyticAux.complexTaylorSeries f 0) d) ≤
      scalarTaylorConstant n d * scalarJetNorm f d := by
  apply (coefficientNorm_taylorPolynomial _ d).trans
  rw [scalarTaylorConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg n) m)
  rw [U02AnalyticAux.norm_complexTaylorSeries]
  apply (div_le_self (norm_nonneg _)
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m))).trans
  unfold scalarJetNorm
  exact Finset.single_le_sum (fun j _ => norm_nonneg (iteratedFDeriv ℂ j f 0)) hm

end Yau.Proofs.Y05Aux
