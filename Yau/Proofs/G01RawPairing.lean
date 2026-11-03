import Yau.Proofs.G01RawAlgebra

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ}

/-- Matrix pairing written in the conjugate-first Hermitian convention. -/
def complexMatrixPairing (A : Matrix (Fin n) (Fin n) ℂ)
    (W Z : ComplexVector n) : ℂ :=
  ∑ j, ∑ i, A j i * W i * star (Z j)

/-- Raw realification represents the real part of a complex matrix pairing, without Hermiticity. -/
theorem rawReal_pairing (A : Matrix (Fin n) (Fin n) ℂ) (W Z : ComplexVector n) :
    (∑ d, ∑ c, rawReal A d c * realCoord W c * realCoord Z d) =
      (complexMatrixPairing A W Z).re := by
  simp only [complexMatrixPairing, Complex.re_sum, Fintype.sum_prod_type,
    Fin.sum_univ_two, rawReal, realCoord]
  norm_num only [Fin.zero_eta, Fin.mk.injEq, ↓reduceIte]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im]
  ring

end Yau.NodeProofs.G01Aux
