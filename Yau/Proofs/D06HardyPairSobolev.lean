import Yau.Proofs.D06HardyFirstSobolev
import Yau.Proofs.D06SmoothSourceDifferences

/-! The first Sobolev order is obtained for the same original P/Q coefficient
columns; all auxiliary difference hypotheses have actual smooth-source producers. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def HardySobolev (k : ℕ) (a : HardySeq r) : Prop :=
  Summable (fun q : ℕ × Fin r => (1 + (q.1 : ℝ) ^ 2) ^ k * ‖a q‖ ^ 2)

theorem hardySobolev_zero (a : HardySeq r) : HardySobolev 0 a := by
  simpa only [HardySobolev, pow_zero, one_mul] using hardy_summable_norm_sq a

theorem hardySobolev_one_of_moment (a : HardySeq r)
    (h : Summable (fun q : ℕ × Fin r => (q.1 : ℝ) ^ 2 * ‖a q‖ ^ 2)) : HardySobolev 1 a := by
  simpa only [HardySobolev, pow_one, add_mul, one_mul] using (hardy_summable_norm_sq a).add h

variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyPair_firstSobolev
    (hquadratic : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, circleDifference L (θ : HardyCircle) ≤ C * θ ^ 2)
    (j : Fin r) :
    HardySobolev 1 (hardyPColumns L hLp hHerm m hm hLower M hM hUpper j) ∧
      HardySobolev 1 (hardyQColumns L hLp hHerm m hm hLower M hM hUpper j) := by
  obtain ⟨C, _, hC⟩ := hquadratic
  have hp (θ : ℝ) :
      circleDifference (hardyPTrace L hLp hHerm m hm hLower M hM hUpper) (θ : HardyCircle) ≤
        (1 / (2 * m ^ 3) * C) * θ ^ 2 := by
    have h := (hardyPTrace_difference_sharp L hLp hHerm m hm hLower M hM hUpper (θ : HardyCircle)).trans
      (mul_le_mul_of_nonneg_left (hC θ) (by positivity : 0 ≤ 1 / (2 * m ^ 3)))
    simpa only [mul_assoc] using h
  have hq (θ : ℝ) :
      circleDifference (hardyQTrace L hLp hHerm m hm hLower M hM hUpper) (θ : HardyCircle) ≤
        (M / (2 * m ^ 2) * C) * θ ^ 2 := by
    have h := (hardyQTrace_difference_sharp L hLp hHerm m hm hLower M hM hUpper (θ : HardyCircle)).trans
      (mul_le_mul_of_nonneg_left (hC θ) (by positivity : 0 ≤ M / (2 * m ^ 2)))
    simpa only [mul_assoc] using h
  constructor
  · apply hardySobolev_one_of_moment
    exact hardy_first_moment_of_difference_bound _ _
      (hardy_column_difference_bound _ _ hp j)
  · apply hardySobolev_one_of_moment
    exact hardy_first_moment_of_difference_bound _ _
      (hardy_column_difference_bound _ _ hq j)

end Yau.NodeProofs.D06Aux
