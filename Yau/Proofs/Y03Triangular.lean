import Yau.Blueprint.Alignment

/-! Strict support in the fixed real weights forces nilpotence and a finite inverse. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def weightRank (w : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => w j < w i)).card

theorem weightRank_lt (w : Fin n → ℝ) (i : Fin n) : weightRank w i < n := by
  have hsub : Finset.univ.filter (fun j => w j < w i) ⊂ (Finset.univ : Finset (Fin n)) := by
    apply Finset.ssubset_iff_subset_ne.2
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have : i ∈ Finset.univ.filter (fun j => w j < w i) := by rw [heq]; simp
    simp at this
  simpa only [weightRank, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hsub

theorem weightRank_strict {w : Fin n → ℝ} {i j : Fin n} (hij : w i < w j) :
    weightRank w i < weightRank w j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.2
  refine ⟨?_, ?_⟩
  · intro k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hk).2.trans hij⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun k => w k < w j) := by simp [hij]
    rw [← heq] at hi
    simp at hi

theorem strict_weight_power_support (A : Herm n) (w : Fin n → ℝ)
    (hA : ∀ i j, A i j ≠ 0 → w i < w j) (m : ℕ) :
    ∀ i j, (A ^ m) i j ≠ 0 → weightRank w i + m ≤ weightRank w j := by
  induction m with
  | zero =>
    intro i j hij
    have heq : i = j := by simpa only [pow_zero, Matrix.one_apply, ne_eq, ite_eq_right_iff,
      one_ne_zero, imp_false, not_not] using hij
    subst j
    omega
  | succ m ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply] at hij
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
    have hp := ih i k (mul_ne_zero_iff.1 hk).1
    have hq := weightRank_strict (hA k j (mul_ne_zero_iff.1 hk).2)
    omega

theorem strict_weight_pow_eq_zero (A : Herm n) (w : Fin n → ℝ)
    (hA : ∀ i j, A i j ≠ 0 → w i < w j) : A ^ n = 0 := by
  ext i j
  by_contra hn
  have hsupport := strict_weight_power_support A w hA n i j hn
  have hbound := weightRank_lt w j
  omega

theorem strict_weight_isNilpotent (A : Herm n) (w : Fin n → ℝ)
    (hA : ∀ i j, A i j ≠ 0 → w i < w j) : IsNilpotent A :=
  ⟨n, strict_weight_pow_eq_zero A w hA⟩

theorem strict_weight_difference_pow_eq_zero (L : Herm n) (w : Fin n → ℝ)
    (hdiag : ∀ i, L i i = 1)
    (hsupport : ∀ i j, i ≠ j → L i j ≠ 0 → w i < w j) : (L - 1) ^ n = 0 := by
  apply strict_weight_pow_eq_zero (L - 1) w
  intro i j hij
  by_cases heq : i = j
  · subst j
    simp [Matrix.sub_apply, hdiag] at hij
  · apply hsupport i j heq
    simpa only [Matrix.sub_apply, Matrix.one_apply, ite_eq_right heq, sub_zero] using hij

end Yau.Blueprint.Alignment.Y03Proof
