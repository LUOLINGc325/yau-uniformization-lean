import Yau.Proofs.E02RealTensorQuadratic
import Yau.Proofs.E02EnvelopeTestTransport

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

def cotangentVector {n : ℕ} (X V : ComplexVector n) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (WithLp.ofLp X) (WithLp.ofLp V)

theorem cotangentDir_combination {n : ℕ} (X V : ComplexVector n) :
    complexDirectionCombination cotangentDir (cotangentVector X V) = (X,V) := by
  apply Prod.ext <;> ext i <;>
    simp [complexDirectionCombination,cotangentDir,cotangentVector,stdVec,
      Prod.fst_sum,Prod.snd_sum,Pi.single_apply,mul_ite]

/-- The complex matrix of the given Peano tensor, in the original
cotangent directions and the actual packed spatial slice. -/
def cotangentTensor {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  realTensorLevi A (fun i => envelopeSpaceCoordinates n (cotangentDir i))
    (fun i => envelopeSpaceCoordinates n (Complex.I • cotangentDir i))

theorem cotangentTensor_isHermitian {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) : (cotangentTensor A).IsHermitian :=
  realTensorLevi_affine_isHermitian A hA (envelopeSpaceCoordinates n) cotangentDir

theorem cotangentTensor_quadratic {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (X V : ComplexVector n) :
    (star (cotangentVector X V) ⬝ᵥ (cotangentTensor A*ᵥcotangentVector X V)).re =
      (A (envelopeSpaceCoordinates n (X,V)) (envelopeSpaceCoordinates n (X,V))+
        A (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V))
          (envelopeSpaceCoordinates n (Complex.I • X,Complex.I • V)))/4 := by
  have h := realTensorLevi_affine_quadratic A hA (envelopeSpaceCoordinates n)
    cotangentDir (cotangentVector X V)
  rw [cotangentDir_combination X V] at h
  exact h

end Yau.NodeProofs.E02Aux
