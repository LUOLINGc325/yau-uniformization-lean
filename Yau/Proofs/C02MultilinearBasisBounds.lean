import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! Finite coordinate bounds control the literal multilinear operator
norm, with constants fixed before the tensor. Empty bases are included. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_clm_le_card_mul_basis_bound (b : OrthonormalBasis ι ℝ E)
    (L : E →L[ℝ] F) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, ‖L (b i)‖ ≤ B) :
    ‖L‖ ≤ (Fintype.card ι : ℝ) * B := by
  classical
  apply L.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hB)
  intro z
  have hSum : L z = ∑ i, (b.repr z i) • L (b i) := by
    calc
      _ = L (∑ i, b.repr z i • b i) := congrArg L (b.sum_repr z).symm
      _ = _ := by simp only [map_sum, map_smul]
  rw [hSum]
  calc
    _ ≤ ∑ i, ‖(b.repr z i) • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖z‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul ((PiLp.norm_apply_le (b.repr z) i).trans_eq (b.repr.norm_map z))
        (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem norm_multilinear_le_card_pow_basis_bound (b : OrthonormalBasis ι ℝ E)
    (m : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a : Fin m → ι, ‖L (fun j => b (a j))‖ ≤ B) :
    ‖L‖ ≤ (Fintype.card ι : ℝ) ^ m * B := by
  induction m with
  | zero =>
    have h := hb (fun j => Fin.elim0 j)
    rw [L.fin0_apply_norm] at h
    simpa only [pow_zero, one_mul] using h
  | succ m ih =>
    rw [← L.curryLeft_norm]
    have hPoint (i : ι) : ‖L.curryLeft (b i)‖ ≤ (Fintype.card ι : ℝ) ^ m * B := by
      apply ih (L.curryLeft (b i))
      intro a
      have hTuple : (Fin.cons (b i) (fun j => b (a j))) =
          (fun j : Fin (m + 1) => b ((Fin.cons i a : Fin (m + 1) → ι) j)) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j <;> simp
      change ‖L (Fin.cons (b i) (fun j => b (a j)))‖ ≤ B
      rw [hTuple]
      exact hb (Fin.cons i a)
    have h := norm_clm_le_card_mul_basis_bound b L.curryLeft
      ((Fintype.card ι : ℝ) ^ m * B) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hB) hPoint
    exact h.trans_eq (by rw [pow_succ]; ring)

end Yau.Blueprint.C02Proof
