import Yau.Proofs.C02DirectionalWords
import Yau.LeafProofs.L21MatrixBounds

/-! Scalar coordinate derivative bounds control the actual vector-valued
Fréchet jets, using only fixed coordinate projections. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_multilinear_le_sum_complex_coordinates
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) (ComplexVector n)) :
    ‖L‖ ≤ ∑ k : Fin n,
      ‖((EuclideanSpace.proj k).restrictScalars ℝ).compContinuousMultilinearMap L‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg fun k _ => norm_nonneg _)
  intro v
  calc
    _ ≤ ∑ k, ‖L v k‖ := Yau.LeafProofs.L21Aux.euclidean_norm_le_sum_coordinates _
    _ ≤ ∑ k : Fin n,
        ‖((EuclideanSpace.proj k).restrictScalars ℝ).compContinuousMultilinearMap L‖ *
          ∏ i : Fin m, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact (((EuclideanSpace.proj k).restrictScalars ℝ).compContinuousMultilinearMap L).le_opNorm v
    _ = _ := by rw [Finset.sum_mul]

theorem norm_iteratedFDeriv_le_sum_complex_coordinates
    (F : E → ComplexVector n) (hF : ContDiff ℝ ∞ F) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x‖ := by
  have h := norm_multilinear_le_sum_complex_coordinates (iteratedFDeriv ℝ m F x)
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro k _
  rw [← ContinuousLinearMap.iteratedFDeriv_comp_left _ hF.contDiffAt (by simp)]
  rfl

end Yau.Blueprint.C02Proof
