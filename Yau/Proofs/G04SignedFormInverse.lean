import Yau.Proofs.G04SignedFormAlgebra

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def alternatingBilin (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  ((continuousMultilinearCurryFin1 ℝ (ComplexVector n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap).comp
    P.toContinuousMultilinearMap.curryLeft

theorem alternatingBilin_apply (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexVector n) : alternatingBilin P u v = P ![u, v] := by
  change P (Fin.cons u (Fin.snoc 0 v)) = P ![u, v]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem alternating_two_swap (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexVector n) : P ![v, u] = -P ![u, v] := by
  have he := P.toAlternatingMap.map_swap ![u, v] (show (0 : Fin 2) ≠ 1 by decide)
  have hp : (![u, v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v, u] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hp, ContinuousAlternatingMap.coe_toAlternatingMap] using he

theorem alternating_two_J_mixed (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v, P ![Complex.I • u, Complex.I • v] = P ![u, v])
    (u v : ComplexVector n) : P ![Complex.I • u, v] = -P ![u, Complex.I • v] := by
  have he := hJ (Complex.I • u) v
  have hI : Complex.I • (Complex.I • u) = (-1 : ℝ) • u := by
    rw [smul_smul]
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [hI, ContinuousAlternatingMap.vecCons_smul] at he
  simpa only [neg_one_smul] using he.symm

def alternatingMatrix (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun a b =>
  ((P ![stdVec a, Complex.I • stdVec b] : ℂ) +
    Complex.I * (P ![stdVec a, stdVec b] : ℂ)) / 2

theorem alternatingMatrix_hermitian (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v, P ![Complex.I • u, Complex.I • v] = P ![u, v]) :
    (alternatingMatrix P).IsHermitian := by
  ext a b
  have h₁ := alternating_two_swap P (stdVec a) (stdVec b)
  have h₂ := alternating_two_swap P (Complex.I • stdVec a) (stdVec b)
  have h₃ := alternating_two_J_mixed P hJ (stdVec a) (stdVec b)
  apply Complex.ext <;>
    simp only [Matrix.conjTranspose_apply, alternatingMatrix, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, zero_add, add_zero, sub_zero, mul_one, one_mul] <;> linarith

theorem matrixPairing_std (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    matrixPairing A (stdVec a) (stdVec b) = A a b := by
  simp [matrixPairing, stdVec, EuclideanSpace.single]

theorem alternatingMatrix_basis (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v, P ![Complex.I • u, Complex.I • v] = P ![u, v])
    (a b : RIdx n) :
    alternatingBilin P (realVec a) (realVec b) =
      matrixImagBilin (alternatingMatrix P) (realVec a) (realVec b) := by
  rcases a with ⟨a, ar⟩
  rcases b with ⟨b, br⟩
  have hmix := alternating_two_J_mixed P hJ (stdVec a) (stdVec b)
  have hj := hJ (stdVec a) (stdVec b)
  rw [alternatingBilin_apply, matrixImagBilin_apply]
  fin_cases ar <;> fin_cases br <;> simp [realVec]
  · change P ![stdVec a, stdVec b] =
      2 * (matrixPairing (alternatingMatrix P) (stdVec a) (stdVec b)).im
    rw [matrixPairing_std]
    simp [alternatingMatrix, Complex.mul_im]
    ring
  · change P ![stdVec a, Complex.I • stdVec b] =
      2 * (matrixPairing (alternatingMatrix P) (stdVec a) (Complex.I • stdVec b)).im
    rw [matrixPairing_smul_right, matrixPairing_std]
    simp [alternatingMatrix, Complex.mul_re, Complex.mul_im]
    ring
  · change P ![Complex.I • stdVec a, stdVec b] =
      2 * (matrixPairing (alternatingMatrix P) (Complex.I • stdVec a) (stdVec b)).im
    rw [matrixPairing_smul_left, matrixPairing_std]
    simp [alternatingMatrix, Complex.mul_re, Complex.mul_im]
    linarith
  · change P ![Complex.I • stdVec a, Complex.I • stdVec b] =
      2 * (matrixPairing (alternatingMatrix P) (Complex.I • stdVec a) (Complex.I • stdVec b)).im
    rw [matrixPairing_smul_left, matrixPairing_smul_right, matrixPairing_std]
    simp [alternatingMatrix, Complex.mul_re, Complex.mul_im]
    linarith

theorem alternatingMatrix_represents (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v, P ![Complex.I • u, Complex.I • v] = P ![u, v])
    (u v : ComplexVector n) : P ![u, v] = 2 * (matrixPairing (alternatingMatrix P) u v).im := by
  rw [← alternatingBilin_apply]
  rw [L12Aux.realBilin_eq_sum (alternatingBilin P) u v,
    ← matrixImagBilin_apply, L12Aux.realBilin_eq_sum (matrixImagBilin (alternatingMatrix P)) u v]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [alternatingMatrix_basis P hJ]

def centeredForm (A : RealForm M 2) (x : M.Carrier) :
    (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ :=
  (A x).compContinuousLinearMap (L03.chartRealContinuousLinearMap x x)

theorem centeredForm_apply (A : RealForm M 2) (x : M.Carrier) (u v : ComplexVector n) :
    centeredForm A x ![u, v] = A x ![chartVec x x u, chartVec x x v] := by
  simp only [centeredForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, L03.chartRealContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem centeredForm_J (A : RealForm M 2) (hA : RealOneOne A) (x : M.Carrier) :
    ∀ u v, centeredForm A x ![Complex.I • u, Complex.I • v] = centeredForm A x ![u, v] := by
  intro u v
  rw [centeredForm_apply, centeredForm_apply]
  rw [L12Aux.chartVec_complex_smul, L12Aux.chartVec_complex_smul]
  exact hA x _ _

theorem centeredForm_matrix (A : RealForm M 2) (x : M.Carrier) :
    alternatingMatrix (centeredForm A x) = formHermitianMatrix A x := by
  ext a b
  simp only [alternatingMatrix, formHermitianMatrix, centeredForm_apply,
    L12Aux.chartVec_complex_smul]

theorem representsSelf (A : RealForm M 2) (hA : RealOneOne A) :
    RepresentsIota (formHermitianMatrix A) A ∧ ∀ x, (formHermitianMatrix A x).IsHermitian := by
  refine ⟨?_, ?_⟩
  · intro x u v
    have he := alternatingMatrix_represents (centeredForm A x) (centeredForm_J A hA x) u v
    rw [centeredForm_matrix] at he
    simpa only [centeredForm_apply, matrixPairing] using he
  · intro x
    rw [← centeredForm_matrix]
    exact alternatingMatrix_hermitian (centeredForm A x) (centeredForm_J A hA x)

end Yau.NodeProofs.G04Aux
