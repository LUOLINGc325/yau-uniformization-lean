import Yau.Proofs.E02RelativeTrace
import Yau.Proofs.E02WeightedForms

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem tracePair_sum_real_smul_right {n m : ℕ} (B : Herm n)
    (α : Fin m → ℝ) (K : Fin m → Herm n) :
    tracePair B (∑ i, (α i : ℂ) • K i) = ∑ i, α i*tracePair B (K i) := by
  simp only [tracePair,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum,Matrix.mul_smul,
    Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

/-- The genuine vertical bounds and the individual epsilon-free trace
inequalities give the aggregate κ estimate without bounding the jets. -/
theorem weighted_majorant_trace_bound {n m : ℕ}
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (B : Herm n) (d : ℝ) (C K : Fin m → Herm n) (a : Fin m → ℝ)
    (hC : ∀ i, (C i-(d : ℂ) • B).PosSemidef)
    (hK : ∀ i, (K i).PosSemidef) (hTrace : ∀ i, tracePair (C i) (K i) ≤ a i) :
    d*tracePair B (∑ i, (α i : ℂ) • K i) ≤ ∑ i, α i*a i := by
  have hEach : ∀ i, d*tracePair B (K i) ≤ a i := by
    intro i
    have hh := (tracePair_mono_left ((d : ℂ) • B) (C i) (K i) (hC i) (hK i)).trans (hTrace i)
    rwa [tracePair_real_smul_left] at hh
  calc
    d*tracePair B (∑ i, (α i : ℂ) • K i) = ∑ i, α i*(d*tracePair B (K i)) := by
      rw [tracePair_sum_real_smul_right,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, α i*a i := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hEach i) (hα i))

end Yau.NodeProofs.E02Aux
