import Yau.Proofs.Y03Conjugation
import Yau.Proofs.Y03StepRicci
import Yau.Proofs.Y03InverseBound

/-! Install a constructed matrix at one step and retain every later change exactly. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def updateChanges (next : Changes n) (k : ℕ) (P M : Herm n) : Changes n where
  plus := fun r => if r = k then P else next.plus r
  minus := fun r => if r = k then M else next.minus r

theorem updateChanges_future (next : Changes n) (k : ℕ) (P M : Herm n) :
    ∀ r, k + 1 ≤ r → (updateChanges next k P M).plus r = next.plus r ∧
      (updateChanges next k P M).minus r = next.minus r := by
  intro r hr
  have hne : r ≠ k := by omega
  simp only [updateChanges, ite_eq_right hne, and_self]

theorem local_extension_from_matrix_change (E : Frames n) (D : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (J : ℕ → ℕ) (S : ℕ → ℝ) (C c : ℝ)
    (next : Changes n) (k : ℕ) (P M : Herm n)
    (hchange : ChangeAt D w J S C c (⟨fun _ => P, fun _ => M⟩ : Changes n) k)
    (hzero : ∀ i l, w (k + 1) i < w k l → (next.minus (k + 1) * jump E k * P⁻¹) i l = 0) :
    ∃ L : Changes n, ChangeAt D w J S C c L k ∧ JumpAt E w L k ∧
      ∀ r, k + 1 ≤ r → L.plus r = next.plus r ∧ L.minus r = next.minus r := by
  refine ⟨updateChanges next k P M, ?_, ?_, updateChanges_future next k P M⟩
  · simpa only [ChangeAt, updateChanges, ite_true] using hchange
  · intro i l hil
    change ((if k + 1 = k then M else next.minus (k + 1)) * jump E k *
      (if k = k then P else next.plus k)⁻¹) i l = 0
    simpa only [ite_eq_right (by omega : k + 1 ≠ k), ite_true] using hzero i l hil

theorem identity_changeAt_of_singularFrames {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (w : ℕ → Fin n → ℝ) (J : ℕ → ℕ) (S : ℕ → ℝ) (C c : ℝ) (k : ℕ)
    (hbudget : (2 : ℝ) ≤ (1 + (J k : ℝ)) ^ C) :
    ChangeAt (diagonal F tk E) w J S C c (⟨fun _ => 1, fun _ => 1⟩ : Changes n) k := by
  have hD : IsUnit (diagonal F tk E k) := by
    rw [diagonal_eq_endpointDiagonal hE]
    exact endpointDiagonal_isUnit _ _
  have hleft : (diagonal F tk E k)⁻¹ * diagonal F tk E k = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hD)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Matrix.one_apply_eq i
  · intro i l hil hne
    exact (hne (Matrix.one_apply_ne hil)).elim
  · change (1 : Herm n) = (diagonal F tk E k)⁻¹ * 1 * diagonal F tk E k
    rw [Matrix.mul_one, hleft]
  · change (1 : Herm n) * diagonal F tk E k * (1 : Herm n)⁻¹ = diagonal F tk E k
    rw [inv_one, Matrix.one_mul, Matrix.mul_one]
  · have hnorm : matOpNorm (1 : Herm n) + matOpNorm ((1 : Herm n)⁻¹) ≤ 2 := by
      rw [inv_one]
      have h := matOpNorm_one_le (n := n)
      linarith
    exact hnorm.trans hbudget
  · change matOpNorm ((1 : Herm n) - 1) ≤ _
    rw [sub_self]
    change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (0 : Herm n)‖ ≤ _
    rw [map_zero, norm_zero]
    positivity

end Yau.Blueprint.Alignment.Y03Proof
