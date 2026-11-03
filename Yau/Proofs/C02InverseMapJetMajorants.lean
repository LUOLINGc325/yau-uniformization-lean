import Yau.Proofs.C02FiniteJetEnvelope

/-! A triangular scalar recursion for the jets of an actual inverse
coordinate map. Its order m+1 uses map jets only through order m. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem finiteJetEnvelope_mono_of_nonnegative {a b : ℕ → ℝ} (m : ℕ)
    (ha : ∀ i ≤ m, 0 ≤ a i) (hb : ∀ i ≤ m, 0 ≤ b i)
    (hle : ∀ i ≤ m, a i ≤ b i) : finiteJetEnvelope a m ≤ finiteJetEnvelope b m := by
  dsimp only [finiteJetEnvelope]
  apply add_le_add (le_refl (1 : ℝ))
  apply Finset.sum_le_sum
  intro i _
  have hi : (i : ℕ) ≤ m := by omega
  rw [abs_of_nonneg (ha i hi), abs_of_nonneg (hb i hi)]
  exact hle i hi

def inverseMapJetMajorant (c : ℕ → ℝ) (R : ℝ) (m : ℕ) : ℝ :=
  Nat.strongRecOn m fun m previous => if _hm : m = 0 then |R| + 1 else
    let v := fun i => if hi : i < m then previous i hi else 0
    ((m - 1).factorial : ℝ) * finiteJetEnvelope c (m - 1) * finiteJetEnvelope v (m - 1) ^ (m - 1)

theorem inverseMapJetMajorant_unfold (c : ℕ → ℝ) (R : ℝ) (m : ℕ) :
    inverseMapJetMajorant c R m = if _hm : m = 0 then |R| + 1 else
      let v := fun i => if _hi : i < m then inverseMapJetMajorant c R i else 0
      ((m - 1).factorial : ℝ) * finiteJetEnvelope c (m - 1) * finiteJetEnvelope v (m - 1) ^ (m - 1) := by
  rw [inverseMapJetMajorant, Nat.strongRecOn_eq]
  rfl

theorem inverseMapJetMajorant_nonnegative (c : ℕ → ℝ) (R : ℝ) (m : ℕ) :
    0 ≤ inverseMapJetMajorant c R m := by
  rw [inverseMapJetMajorant_unfold]
  split_ifs
  · positivity
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (zero_le_one.trans (finiteJetEnvelope_one_le c _)))
      (pow_nonneg (zero_le_one.trans (finiteJetEnvelope_one_le _ _)) _)

theorem inverseMapJetMajorant_dominates (a c : ℕ → ℝ) (R : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hInitial : a 0 ≤ |R| + 1)
    (hStep : ∀ m, a (m + 1) ≤
      (m.factorial : ℝ) * finiteJetEnvelope c m * finiteJetEnvelope a m ^ m) :
    ∀ m, a m ≤ inverseMapJetMajorant c R m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [inverseMapJetMajorant_unfold]
    cases m with
    | zero => simpa using hInitial
    | succ m =>
      simp only [Nat.succ_ne_zero, Nat.add_sub_cancel]
      let v := fun i => if _hi : i < m + 1 then inverseMapJetMajorant c R i else 0
      have hv (i : ℕ) : 0 ≤ v i := by
        dsimp only [v]
        split_ifs
        · exact inverseMapJetMajorant_nonnegative c R i
        · exact le_rfl
      have hle (i : ℕ) (hi : i ≤ m) : a i ≤ v i := by
        dsimp only [v]
        rw [dite_eq_left (Nat.lt_succ_of_le hi)]
        exact ih i (Nat.lt_succ_of_le hi)
      exact (hStep m).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (finiteJetEnvelope_one_le a m))
          (finiteJetEnvelope_mono_of_nonnegative m (fun i _ => ha i) (fun i _ => hv i) hle) m)
        (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (finiteJetEnvelope_one_le c m))))

end Yau.Blueprint.C02Proof
