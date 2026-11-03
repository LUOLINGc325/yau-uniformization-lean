import Yau.Proofs.E02MatrixBasic
import Yau.Proofs.E02LogdetSupport

open Matrix Set
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Contact weights are incorporated in the actual columns of one matrix. -/
def weightedColumns {n m : ℕ} (α : Fin m → ℝ) (η : Fin m → ComplexVector n) : Rect n m :=
  fun i j => (Real.sqrt (α j) : ℂ)*(WithLp.ofLp (η j)) i

theorem weightedColumns_gram {n m : ℕ} (α : Fin m → ℝ) (η : Fin m → ComplexVector n)
    (hα : ∀ j, 0 ≤ α j) :
    weightedColumns α η*(weightedColumns α η)ᴴ =
      ∑ j, (α j : ℂ) • Matrix.vecMulVec (WithLp.ofLp (η j)) (star (WithLp.ofLp (η j))) := by
  ext i k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,weightedColumns,
    Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Real.sqrt (α j) : ℂ)^2 = (α j : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hα j)
  have hstar : star (Real.sqrt (α j) : ℂ) = (Real.sqrt (α j) : ℂ) := by simp
  simp only [star_mul,hstar]
  calc
    _ = (Real.sqrt (α j) : ℂ)^2 * ((WithLp.ofLp (η j)) i*star ((WithLp.ofLp (η j)) k)) := by ring
    _ = _ := by rw [hs]

theorem trace_weighted_outer_products {n m : ℕ} (B : Herm n) (α : Fin m → ℝ)
    (η : Fin m → ComplexVector n) :
    (Matrix.trace (B*(∑ j, (α j : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (η j)) (star (WithLp.ofLp (η j)))))).re =
      ∑ j, α j*qform B (η j) := by
  rw [Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul,Matrix.trace_smul,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]
  simp only [qform,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

/-- The fixed chart and the same actual maximizing matrix yield the
weighted pointwise support, without choosing a continuous optimizer. -/
theorem weighted_quadratic_logdet_lower {n m : ℕ} (B : Herm n) (hB : B.PosDef)
    (α : Fin m → ℝ) (η : Fin m → ComplexVector n) (hα : ∀ j, 0 ≤ α j)
    (hv : Fin m → ℝ) (hBound : ∀ j, qform B (η j) ≤ hv j)
    (hGram : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef) :
    (n:ℝ)+Real.log B.det.re+
      Real.log (weightedColumns α η*(weightedColumns α η)ᴴ).det.re ≤ ∑ j, α j*hv j := by
  have hSupport := trace_logdet_support (weightedColumns α η*(weightedColumns α η)ᴴ) B hGram hB
  have hTrace : (Matrix.trace (B*(weightedColumns α η*(weightedColumns α η)ᴴ))).re =
      ∑ j, α j*qform B (η j) := by
    rw [weightedColumns_gram α η hα,trace_weighted_outer_products]
  rw [hTrace] at hSupport
  calc
    _ = (n:ℝ)+Real.log (weightedColumns α η*(weightedColumns α η)ᴴ).det.re+Real.log B.det.re := by ring
    _ ≤ _ := hSupport
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hBound j) (hα j))

end Yau.NodeProofs.E02Aux
