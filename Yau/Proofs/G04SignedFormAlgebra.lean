import Yau.LeafProofs.L03
import Yau.LeafProofs.L23TensorMultilinear

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def matrixPairing (A : Matrix (Fin n) (Fin n) ℂ) (u v : ComplexVector n) : ℂ :=
  ∑ a, ∑ b, star (u a) * A a b * v b

theorem matrixPairing_add_left (A : Matrix (Fin n) (Fin n) ℂ) (u v w : ComplexVector n) :
    matrixPairing A (u + v) w = matrixPairing A u w + matrixPairing A v w := by
  simp [matrixPairing, add_mul, Finset.sum_add_distrib]

theorem matrixPairing_add_right (A : Matrix (Fin n) (Fin n) ℂ) (u v w : ComplexVector n) :
    matrixPairing A u (v + w) = matrixPairing A u v + matrixPairing A u w := by
  simp [matrixPairing, mul_add, Finset.sum_add_distrib]

theorem matrixPairing_smul_left (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u v : ComplexVector n) :
    matrixPairing A (c • u) v = star c * matrixPairing A u v := by
  simp [matrixPairing, mul_assoc, Finset.mul_sum]

theorem matrixPairing_smul_right (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u v : ComplexVector n) :
    matrixPairing A u (c • v) = c * matrixPairing A u v := by
  simp only [matrixPairing, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def matrixImagBilin (A : Matrix (Fin n) (Fin n) ℂ) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun u v : ComplexVector n => 2 * (matrixPairing A u v).im)
    (by intro u v w; rw [matrixPairing_add_left, Complex.add_im, mul_add])
    (by
      intro r u v
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), matrixPairing_smul_left]
      simp [Complex.mul_im, smul_eq_mul]
      ring)
    (by intro u v w; rw [matrixPairing_add_right, Complex.add_im, mul_add])
    (by
      intro r u v
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), matrixPairing_smul_right]
      simp [Complex.mul_im, smul_eq_mul]
      ring)).toContinuousBilinearMap

theorem matrixImagBilin_apply (A : Matrix (Fin n) (Fin n) ℂ) (u v : ComplexVector n) :
    matrixImagBilin A u v = 2 * (matrixPairing A u v).im := rfl

def matrixImagMultilinear (A : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ComplexVector n) ℝ :=
  (((continuousMultilinearCurryFin1 ℝ (ComplexVector n) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (matrixImagBilin A)).uncurryLeft

theorem matrixImagMultilinear_apply (A : Matrix (Fin n) (Fin n) ℂ)
    (V : Fin 2 → ComplexVector n) :
    matrixImagMultilinear A V = 2 * (matrixPairing A (V 0) (V 1)).im := rfl

theorem matrixPairing_star (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (u v : ComplexVector n) : star (matrixPairing A u v) = matrixPairing A v u := by
  simp only [matrixPairing, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hA.apply a b]
  ring

def modelIotaForm (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ where
  toContinuousMultilinearMap := matrixImagMultilinear A
  map_eq_zero_of_eq' V i j hij hne := by
    have h01 : V 0 = V 1 := by
      fin_cases i <;> fin_cases j
      · exact False.elim (hne rfl)
      · exact hij
      · exact hij.symm
      · exact False.elim (hne rfl)
    change matrixImagMultilinear A V = 0
    rw [matrixImagMultilinear_apply, h01]
    have he := congrArg Complex.im (matrixPairing_star A hA (V 1) (V 1))
    simp only [Complex.star_def, Complex.conj_im] at he
    linarith

theorem modelIotaForm_apply (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (V : Fin 2 → ComplexVector n) :
    modelIotaForm A hA V = 2 * (matrixPairing A (V 0) (V 1)).im := rfl

theorem modelIotaForm_J (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (u v : ComplexVector n) :
    modelIotaForm A hA ![Complex.I • u, Complex.I • v] = modelIotaForm A hA ![u, v] := by
  simp only [modelIotaForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    matrixPairing_smul_left, matrixPairing_smul_right]
  simp [Complex.mul_re, Complex.mul_im]

def iotaRealForm (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) : RealForm M 2 :=
  fun x => (modelIotaForm (A x) (hA x)).compContinuousLinearMap
    (L03.tangentCoordsRealContinuousLinearMap x x)

theorem iotaRealForm_represents (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) : RepresentsIota A (iotaRealForm A hA) := by
  intro x u v
  simp only [iotaRealForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, L03.tangentCoordsRealContinuousLinearMap_apply,
    modelIotaForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x), matrixPairing]

theorem iotaRealForm_oneOne (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) : RealOneOne (iotaRealForm A hA) := by
  intro x u v
  have hu : tangentCoords x x (Complex.I • u) = Complex.I • tangentCoords x x u := by
    exact map_smul (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x) x) Complex.I u
  have hv : tangentCoords x x (Complex.I • v) = Complex.I • tangentCoords x x v := by
    exact map_smul (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x) x) Complex.I v
  change modelIotaForm (A x) (hA x)
      ![tangentCoords x x (Complex.I • u), tangentCoords x x (Complex.I • v)] =
    modelIotaForm (A x) (hA x) ![tangentCoords x x u, tangentCoords x x v]
  rw [hu, hv]
  exact modelIotaForm_J (A x) (hA x) (tangentCoords x x u) (tangentCoords x x v)

theorem formHermitianMatrix_of_representsIota
    (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ) (α : RealForm M 2)
    (hα : RepresentsIota A α) (x : M.Carrier) : formHermitianMatrix α x = A x := by
  ext a b
  have h₁ : α x ![chartVec x x (stdVec a), chartVec x x (stdVec b)] = 2 * (A x a b).im := by
    simpa [stdVec, EuclideanSpace.single] using hα x (stdVec a) (stdVec b)
  have hI : α x ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] =
      2 * (A x a b).re := by
    have he := hα x (stdVec a) (Complex.I • stdVec b)
    rw [L12Aux.chartVec_complex_smul] at he
    simpa [stdVec, EuclideanSpace.single] using he
  unfold formHermitianMatrix
  rw [h₁, hI]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem reconstructSigned (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) :
    ∃ α : RealForm M 2, RealOneOne α ∧ RepresentsIota A α ∧
      ∀ x, formHermitianMatrix α x = A x :=
  ⟨iotaRealForm A hA, iotaRealForm_oneOne A hA, iotaRealForm_represents A hA,
    formHermitianMatrix_of_representsIota A _ (iotaRealForm_represents A hA)⟩

end Yau.NodeProofs.G04Aux
