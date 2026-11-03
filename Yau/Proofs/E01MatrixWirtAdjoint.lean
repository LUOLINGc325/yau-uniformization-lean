import Yau.Proofs.E01MatrixWirtinger
import Yau.Proofs.V03LeviCalculus

/-! The actual transpose and adjoint conventions in the dual Chern calculation. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau
open Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexMatrixWirt_transpose (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirt (fun w => (A w)ᵀ) z v = (complexMatrixWirt A z v)ᵀ := rfl

theorem complexMatrixWirtBar_transpose (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirtBar (fun w => (A w)ᵀ) z v = (complexMatrixWirtBar A z v)ᵀ := rfl

theorem complexMatrixWirt_conjTranspose (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirt (fun w => (A w)ᴴ) z v = (complexMatrixWirtBar A z v)ᴴ := by
  ext i j
  exact wirt_conj (fun w => A w j i) z v

theorem complexMatrixWirtBar_conjTranspose (A : E → Matrix ι ι ℂ) (z v : E) :
    complexMatrixWirtBar (fun w => (A w)ᴴ) z v = (complexMatrixWirt A z v)ᴴ := by
  ext i j
  exact wirtBar_conj (fun w => A w j i) z v

theorem complexMatrixWirtBar_of_hermitian (A : E → Matrix ι ι ℂ)
    (hA : ∀ w, (A w).IsHermitian) (z v : E) :
    complexMatrixWirtBar A z v = (complexMatrixWirt A z v)ᴴ := by
  have heq : (fun w => (A w)ᴴ) = A := funext (fun w => (hA w).eq)
  simpa only [heq] using complexMatrixWirtBar_conjTranspose A z v

end Yau.NodeProofs.E01Aux
