import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Entrywise real differentiation of complex matrix fields. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexMatrixDerivative (A : E → Matrix ι ι ℂ) (z v : E) : Matrix ι ι ℂ :=
  fun i j => fderiv ℝ (fun w => A w i j) z v

theorem complexMatrixDerivative_const (A : Matrix ι ι ℂ) (z v : E) :
    complexMatrixDerivative (fun _ : E => A) z v = 0 := by
  ext i j
  simp [complexMatrixDerivative]

theorem complexMatrixDerivative_congr {A B : E → Matrix ι ι ℂ} {z : E}
    (heq : A =ᶠ[𝓝 z] B) (v : E) :
    complexMatrixDerivative A z v = complexMatrixDerivative B z v := by
  ext i j
  have hij : (fun w => A w i j) =ᶠ[𝓝 z] (fun w => B w i j) :=
    heq.mono (fun _ h => congrArg (fun C : Matrix ι ι ℂ => C i j) h)
  exact congrArg (fun f : E →L[ℝ] ℂ => f v) hij.fderiv_eq

theorem complexMatrixDerivative_mul {A B : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) :
    complexMatrixDerivative (fun w => A w * B w) z v =
      complexMatrixDerivative A z v * B z + A z * complexMatrixDerivative B z v := by
  ext i j
  change fderiv ℝ (fun w => ∑ k, A w i k * B w k j) z v = _
  rw [fderiv_fun_sum (A := fun k w => A w i k * B w k j)
    (u := Finset.univ) (fun k _ => (hA i k).mul (hB k j))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_fun_mul (hA i _) (hB _ j)]
  simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.mul_apply, complexMatrixDerivative, Finset.sum_add_distrib]
  simp only [mul_comm, add_comm]

theorem complex_matrix_det_differentiableAt {A : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) :
    DifferentiableAt ℝ (fun w => (A w).det) z := by
  simp_rw [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply (differentiableAt_const _).mul
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun i _ => (hA (σ i) i).hasFDerivAt)).differentiableAt

end Yau.NodeProofs.E01Aux
