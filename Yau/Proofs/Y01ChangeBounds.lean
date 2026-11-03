import Yau.Proofs.Y03InverseBound

/-! The aligned minus change has the same strict weight support and a genuine
polynomial inverse bound; no inverse estimate is supplied as an extra input. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem minus_change_strict_weight
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {w : ℕ → Fin n → ℝ} {J : ℕ → ℕ} {S : ℕ → ℝ}
    {C c : ℝ} {L : Changes n} {k : ℕ}
    (hL : ChangeAt (diagonal F tk E) w J S C c L k) :
    (∀ i, L.minus k i i = 1) ∧
      ∀ i l, i ≠ l → L.minus k i l ≠ 0 → w k i < w k l := by
  have hDinv : (diagonal F tk E k)⁻¹ =
      Matrix.diagonal (fun i => (singularLength F tk E k i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    unfold diagonal
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (ne_of_gt ((hE k).2.2.2.2.2.1 i).1))
  have hentry (i l : Fin n) : L.minus k i l =
      ((singularLength F tk E k i : ℂ)⁻¹ * L.plus k i l) * (singularLength F tk E k l : ℂ) := by
    rw [hL.2.2.1, hDinv]
    simp only [diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine ⟨?_, ?_⟩
  · intro i
    rw [hentry, hL.1 i, mul_one]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (ne_of_gt ((hE k).2.2.2.2.2.1 i).1))
  · intro i l hil hne
    apply hL.2.1 i l hil
    intro hz
    apply hne
    rw [hentry, hz, mul_zero, zero_mul]

theorem plus_change_isUnit
    {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ} {J : ℕ → ℕ} {S : ℕ → ℝ}
    {C c : ℝ} {L : Changes n} {k : ℕ} (hL : ChangeAt D w J S C c L k) :
    IsUnit (L.plus k) := strict_weight_isUnit _ _ hL.1 hL.2.1

theorem minus_change_isUnit
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {w : ℕ → Fin n → ℝ} {J : ℕ → ℕ} {S : ℕ → ℝ}
    {C c : ℝ} {L : Changes n} {k : ℕ}
    (hL : ChangeAt (diagonal F tk E) w J S C c L k) : IsUnit (L.minus k) := by
  have htri := minus_change_strict_weight hE hL
  exact strict_weight_isUnit _ _ htri.1 htri.2

theorem minus_change_polynomial_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {w : ℕ → Fin n → ℝ} {J : ℕ → ℕ} {S : ℕ → ℝ}
    {C c : ℝ} (hc : 0 < c) {L : Changes n} {k : ℕ}
    (hL : ChangeAt (diagonal F tk E) w J S C c L k) :
    matOpNorm (L.minus k) + matOpNorm (L.minus k)⁻¹ ≤
      (n + 1 : ℝ) * ((1 + (J k : ℝ)) ^ C + 2) ^ (n + 1) := by
  have hP : 0 ≤ (1 + (J k : ℝ)) ^ C := Real.rpow_nonneg (by positivity) _
  have hExp : Real.exp (-c * Real.sqrt (S (J k)) / (J k : ℝ) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hc.le) (Real.sqrt_nonneg _)
    · positivity
  have hsmall : matOpNorm (L.minus k - 1) ≤ (1 + (J k : ℝ)) ^ C :=
    hL.2.2.2.2.2.trans ((mul_le_mul_of_nonneg_left hExp hP).trans_eq (mul_one _))
  have hnorm : matOpNorm (L.minus k) ≤ 1 + (1 + (J k : ℝ)) ^ C := by
    have htriangle : matOpNorm (L.minus k) ≤ matOpNorm (L.minus k - 1) + matOpNorm (1 : Herm n) := by
      have heq : L.minus k = (L.minus k - 1) + 1 := by abel
      conv_lhs => rw [heq]
      exact norm_add_le (L.minus k - 1) (1 : Herm n)
    have hI := matOpNorm_one_le (n := n)
    linarith
  have htri := minus_change_strict_weight hE hL
  have hb := strict_weight_change_polynomial_bound (L.minus k) (w k) htri.1 htri.2
    (show 0 ≤ 1 + (1 + (J k : ℝ)) ^ C by positivity) hnorm
  convert hb using 1 <;> congr 2 <;> ring

end Yau.Proofs.Y01Aux
