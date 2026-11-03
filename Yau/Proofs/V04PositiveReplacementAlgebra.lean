import Yau.Proofs.V04SymplecticSubmeanMatrix

/-! Algebra of the literal frozen cost and the same given frame. -/
open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint
open SymplecticSubmeanAux

variable {n : ℕ}

theorem bivectorCost_real_smul (c : ℝ) (A J : CotangentMatrix n) :
    bivectorCost ((c : ℂ) • A) J = c ^ 2 * bivectorCost A J := by
  unfold bivectorCost
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l,
      J i j * star (J k l) * ((c : ℂ) * A k i) * ((c : ℂ) * A l j)) =
      (c ^ 2 : ℝ) * (∑ i, ∑ j, ∑ k, ∑ l, J i j * star (J k l) * A k i * A l j) := by
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsum, Complex.re_ofReal_mul]
  ring

theorem bivectorCost_congruence (A J E : CotangentMatrix n) (hE : IsUnit E.det) :
    bivectorCost (Eᴴ * A * E) (E⁻¹ * J * E⁻¹ᵀ) = bivectorCost A J := by
  rw [bivectorCost_eq_half_trace, bivectorCost_eq_half_trace]
  have he : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE
  have hestar : E⁻¹ᴴ * Eᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose he
  have het : E⁻¹ᵀ * Eᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose he
  have hebar : Eᴴᵀ * E⁻¹ᵀᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.conjTranspose_one, Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose] using
      congrArg (fun B : CotangentMatrix n => Bᴴᵀ) he
  have hcancel : (E⁻¹ * J * E⁻¹ᵀ)ᴴ * (Eᴴ * A * E) *
      (E⁻¹ * J * E⁻¹ᵀ) * (Eᴴ * A * E)ᵀ =
      E⁻¹ᵀᴴ * (Jᴴ * A * J * Aᵀ) * Eᴴᵀ := by
    simp only [Matrix.conjTranspose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc] at hestar het ⊢
    rw [← Matrix.mul_assoc E⁻¹ᴴ Eᴴ, hestar, Matrix.one_mul,
      ← Matrix.mul_assoc E E⁻¹, he, Matrix.one_mul,
      ← Matrix.mul_assoc E⁻¹ᵀ Eᵀ, het, Matrix.one_mul]
  rw [hcancel]
  congr 2
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hebar, Matrix.one_mul]

theorem canonicalBivector_star (i j : CotangentIndex n) :
    star (canonicalBivector i j) = canonicalBivector i j := by
  cases i <;> cases j <;> simp [canonicalBivector, apply_ite]

theorem canonicalBivector_sum (f : CotangentIndex n → CotangentIndex n → ℂ) :
    (∑ i, ∑ j, canonicalBivector i j * f i j) =
      ∑ i : Fin n, (f (Sum.inl i) (Sum.inr i) - f (Sum.inr i) (Sum.inl i)) := by
  classical
  simp [Fintype.sum_sum_type, canonicalBivector, ite_mul, Finset.sum_sub_distrib]
  ring

theorem bivectorCost_canonical (A : CotangentMatrix n) (hA : A.IsHermitian) :
    bivectorCost A canonicalBivector = symplecticP A := by
  classical
  have hs (i j : Fin n) : A (Sum.inr i) (Sum.inl j) = star (A (Sum.inl j) (Sum.inr i)) := by
    simpa only [Matrix.conjTranspose_apply] using
      (congrFun (congrFun hA (Sum.inr i)) (Sum.inl j)).symm
  let R : ℂ := ∑ i : Fin n, ∑ k : Fin n, A (Sum.inl i) (Sum.inl k) * A (Sum.inr i) (Sum.inr k)
  let S : ℂ := ∑ i : Fin n, ∑ k : Fin n, A (Sum.inl i) (Sum.inr k) * star (A (Sum.inl k) (Sum.inr i))
  have hdiag : (∑ i : Fin n, ∑ k : Fin n, A (Sum.inl k) (Sum.inl i) * A (Sum.inr k) (Sum.inr i)) = R :=
    Finset.sum_comm
  have hdiag' : (∑ i : Fin n, ∑ k : Fin n, A (Sum.inr k) (Sum.inr i) * A (Sum.inl k) (Sum.inl i)) = R := by
    simpa only [mul_comm] using hdiag
  have hcross : (∑ i : Fin n, ∑ k : Fin n, A (Sum.inr k) (Sum.inl i) * A (Sum.inl k) (Sum.inr i)) = S := by
    simp_rw [hs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcross' : (∑ i : Fin n, ∑ k : Fin n, A (Sum.inl k) (Sum.inr i) * A (Sum.inr k) (Sum.inl i)) = S := by
    simpa only [mul_comm] using hcross
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l,
      canonicalBivector i j * star (canonicalBivector k l) * A k i * A l j) =
      ∑ i, ∑ j, canonicalBivector i j *
        (∑ k, ∑ l, canonicalBivector k l * (A k i * A l j)) := by
    simp only [Finset.mul_sum, canonicalBivector_star]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hsym : symplecticP A = (R - S).re := by
    simp only [symplecticP, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.of_apply, R, S]
  rw [bivectorCost, hsum, canonicalBivector_sum, hsym]
  simp_rw [canonicalBivector_sum]
  simp only [Finset.sum_sub_distrib]
  rw [hdiag, hdiag', hcross, hcross']
  simp only [Complex.sub_re]
  ring

end Yau.Blueprint.V04Proof.PositiveReplacementAux
