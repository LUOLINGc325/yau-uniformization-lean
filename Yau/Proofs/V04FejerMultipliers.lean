import Yau.Proofs.V04OrderedLimits

/-! The error multiplier includes both the retained-mode attenuation and
the omitted high frequencies of the frozen Fejér mean. -/

noncomputable section
namespace Yau.Blueprint.V04Proof

def fejerMultiplier (P : ℕ) (k : ℤ) : ℝ :=
  if k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ) then 1 - |(k : ℝ)| / (P + 1) else 0

theorem fejerMultiplier_bounds (P : ℕ) (k : ℤ) :
    0 ≤ fejerMultiplier P k ∧ fejerMultiplier P k ≤ 1 := by
  dsimp [fejerMultiplier]
  split_ifs with hmem
  · have hk := Finset.mem_Icc.mp hmem
    have hklo : -(P : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hkhi : (k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hk.2
    have habs : |(k : ℝ)| ≤ P := abs_le.mpr ⟨hklo, hkhi⟩
    have hden : (0 : ℝ) < P + 1 := by positivity
    have hr0 : 0 ≤ |(k : ℝ)| / (P + 1) := div_nonneg (abs_nonneg _) hden.le
    have hr1 : |(k : ℝ)| / (P + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    constructor <;> linarith
  · exact ⟨le_rfl, zero_le_one⟩

theorem fejerMultiplier_error_sq (P : ℕ) (k : ℤ) :
    |1 - fejerMultiplier P k| ^ 2 ≤ |(k : ℝ)| / (P + 1) := by
  have hden : (0 : ℝ) < P + 1 := by positivity
  dsimp [fejerMultiplier]
  split_ifs with hmem
  · have hk := Finset.mem_Icc.mp hmem
    have hklo : -(P : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hkhi : (k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hk.2
    have habs : |(k : ℝ)| ≤ P := abs_le.mpr ⟨hklo, hkhi⟩
    have hr0 : 0 ≤ |(k : ℝ)| / (P + 1) := div_nonneg (abs_nonneg _) hden.le
    have hr1 : |(k : ℝ)| / (P + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    rw [sub_sub_cancel, sq_abs]
    nlinarith
  · have habs : (P : ℝ) + 1 ≤ |(k : ℝ)| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with hlo | hhi
      · have hk : k ≤ -(P : ℤ) - 1 := by omega
        have hkR : (k : ℝ) ≤ -(P : ℝ) - 1 := by exact_mod_cast hk
        linarith [neg_abs_le (k : ℝ)]
      · have hk : (P : ℤ) + 1 ≤ k := by omega
        have hkR : (P : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
        exact hkR.trans (le_abs_self _)
    simpa using (le_div_iff₀ hden).2 (show 1 * (P + 1 : ℝ) ≤ |(k : ℝ)| by simpa using habs)

end Yau.Blueprint.V04Proof
