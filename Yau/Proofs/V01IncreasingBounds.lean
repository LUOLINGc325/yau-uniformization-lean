import spec.CHAIN.CONTRACTS

/-! V01 scratch source: the localization radii are chosen once to dominate
arbitrary previously fixed scalar tail bounds, with strict increase. -/

noncomputable section
open Filter Finset
open scoped Topology

namespace Yau.Blueprint.V01Proof

def increasingBound (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) + 1 + ∑ i ∈ Finset.range (j + 1), max 0 (f i)

theorem increasingBound_ge_index (f : ℕ → ℝ) (j : ℕ) :
    (j : ℝ) + 1 ≤ increasingBound f j := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range (j + 1), max 0 (f i) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  dsimp [increasingBound]
  linarith

theorem increasingBound_pos (f : ℕ → ℝ) (j : ℕ) :
    0 < increasingBound f j := by
  have h := increasingBound_ge_index f j
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem increasingBound_ge (f : ℕ → ℝ) (j : ℕ) : f j ≤ increasingBound f j := by
  have hsum : max 0 (f j) ≤ ∑ i ∈ Finset.range (j + 1), max 0 (f i) :=
    Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_range.mpr (Nat.lt_succ_self j))
  have hmax := le_max_right 0 (f j)
  have hj := Nat.cast_nonneg (α := ℝ) j
  dsimp [increasingBound]
  linarith

theorem increasingBound_strictMono (f : ℕ → ℝ) : StrictMono (increasingBound f) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [increasingBound, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  have hmax := le_max_left 0 (f (j + 1))
  linarith

theorem increasingBound_tendsto_atTop (f : ℕ → ℝ) :
    Tendsto (increasingBound f) atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ))
  intro j
  have h := increasingBound_ge_index f j
  linarith

end Yau.Blueprint.V01Proof
