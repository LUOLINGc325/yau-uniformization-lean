import spec.CHAIN.CONTRACTS
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-! An actual square unitary frame recovers the inverse metric and its
trace contraction, including the empty index set in dimension zero. -/

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem inverseMetric_of_unitaryMatrix (H S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.conjTranspose * H * S = 1) : H⁻¹ = S * S.conjTranspose := by
  apply Matrix.inv_eq_left_inv
  have hLeft : (S.conjTranspose * H) * S = 1 := hS
  have hRight : S * (S.conjTranspose * H) = 1 := mul_eq_one_comm.mp hLeft
  simpa only [Matrix.mul_assoc] using hRight

theorem inverseMetric_entry_unitaryMatrix (H S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.conjTranspose * H * S = 1) (a b : Fin n) :
    ∑ i, star (S a i) * S b i = H⁻¹ b a := by
  rw [inverseMetric_of_unitaryMatrix H S hS]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem traceWith_eq_unitaryMatrix_sum (H R S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.conjTranspose * H * S = 1) :
    traceWith H R = (∑ i, ∑ a, ∑ b, star (S a i) * R a b * S b i).re := by
  rw [traceWith, inverseMetric_of_unitaryMatrix H S hS, Matrix.trace_mul_cycle,
    Matrix.trace_mul_cycle, Matrix.mul_assoc]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Yau.Blueprint.C02Proof
