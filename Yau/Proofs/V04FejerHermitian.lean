import Yau.Proofs.V04FejerColumnBounds
import Yau.Proofs.V04MatrixUnitTests

/-! The actual kernel convolution preserves Hermitian matrices. The sum
of quadratic column tests is the actual cyclic trace of its square. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder ContDiff ComplexConjugate
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

theorem fejerMean_isHermitian (A : ℝ → CotangentMatrix n)
    (hA : ∀ i j, Continuous (fun θ => A θ i j))
    (hp : ∀ i j, Function.Periodic (fun θ => A θ i j) (2 * Real.pi))
    (hHerm : ∀ θ, (A θ).IsHermitian) (P : ℕ) (θ : ℝ) : (fejerMean A P θ).IsHermitian := by
  have heq (i j : CotangentIndex n) : fejerMean A P θ i j =
      ∫ y : AddCircle (2 * Real.pi),
        (fejerKernel P ((θ : AddCircle (2 * Real.pi)) - y) : ℂ) * (hp i j).lift y ∂haarAddCircle := by
    rw [fejerMean_entry_eq_scalarFejer A hp]
    exact (fejerKernel_convolution (periodic_lift_continuous (hp i j) (hA i j)) P _).symm
  change (fejerMean A P θ)ᴴ = fejerMean A P θ
  apply Matrix.ext
  intro i j
  change conj (fejerMean A P θ j i) = fejerMean A P θ i j
  rw [heq j i, heq i j, ← integral_conj]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  induction y using Quotient.inductionOn' with
  | h t =>
    simpa only [Function.Periodic.lift_coe, Matrix.conjTranspose_apply, Complex.star_def] using
      congrFun (congrFun (hHerm t) i) j

theorem sum_quadValue_columns (T S : CotangentMatrix n) :
    ∑ i, quadValue T (fun r => S r i) = (Matrix.trace (Sᴴ * T * S)).re := by
  unfold quadValue
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  change (∑ i, star (fun r => S r i) ⬝ᵥ (T *ᵥ fun r => S r i)) =
    ∑ i, (Sᴴ * T * S) i i
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.dotProduct_mulVec]
  rfl

theorem sum_quadValue_columns_hermitian (T S : CotangentMatrix n) (hS : S.IsHermitian) :
    ∑ i, quadValue T (fun r => S r i) = (Matrix.trace (T * S ^ 2)).re := by
  rw [sum_quadValue_columns]
  apply congrArg Complex.re
  rw [hS.eq, pow_two, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm S (T * S)

end Yau.Blueprint.V04Proof
