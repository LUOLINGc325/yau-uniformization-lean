import Yau.Proofs.V04OrderedLimits
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! The fibre coefficient is fixed before the enlarged radii. No estimate in
this construction has a coefficient depending on the newly selected radius. -/

open Filter
open scoped Topology

noncomputable section
namespace Yau.Blueprint.V04Proof

def enlargedFiberRadius (B C : ℕ → ℝ) (j : ℕ) : ℝ :=
  B j + (j + 1 : ℝ) * (1 + Real.log (C j))

theorem enlargedFiberRadius_ge (B C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j) (j : ℕ) :
    B j ≤ enlargedFiberRadius B C j := by
  have hlog : 0 ≤ Real.log (C j) := Real.log_nonneg (hC j)
  dsimp [enlargedFiberRadius]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (by linarith))

theorem enlargedFiberRadius_log_bound (B C : ℕ → ℝ)
    (hB : ∀ j : ℕ, (j + 1 : ℝ) ≤ B j) (hC : ∀ j, 1 ≤ C j) (j : ℕ) :
    0 ≤ Real.log (C j) / enlargedFiberRadius B C j ^ 2 ∧
    Real.log (C j) / enlargedFiberRadius B C j ^ 2 ≤ ((j + 1 : ℝ)⁻¹) ^ 2 := by
  have hu : (0 : ℝ) < j + 1 := by positivity
  have hb : 0 < B j := hu.trans_le (hB j)
  have hlog : 0 ≤ Real.log (C j) := Real.log_nonneg (hC j)
  have he : 0 < enlargedFiberRadius B C j :=
    hb.trans_le (enlargedFiberRadius_ge B C hC j)
  have hscale : (j + 1 : ℝ) * (1 + Real.log (C j)) ≤ enlargedFiberRadius B C j := by
    dsimp [enlargedFiberRadius]
    linarith
  have hscale0 : 0 ≤ (j + 1 : ℝ) * (1 + Real.log (C j)) := by positivity
  have hsquared := mul_self_le_mul_self hscale0 hscale
  have hpoly : Real.log (C j) ≤ (1 + Real.log (C j)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (C j))]
  have hmul := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (j + 1 : ℝ))
  refine ⟨div_nonneg hlog (sq_nonneg _), ?_⟩
  rw [inv_pow, ← one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hu)).2
  nlinarith [hsquared, hmul]

theorem enlargedFiberRadius_log_tendsto (B C : ℕ → ℝ)
    (hB : ∀ j : ℕ, (j + 1 : ℝ) ≤ B j) (hC : ∀ j, 1 ≤ C j) :
    Tendsto (fun j => Real.log (C j) / enlargedFiberRadius B C j ^ 2)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun j : ℕ => ((j + 1 : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  exact squeeze_zero (fun j => (enlargedFiberRadius_log_bound B C hB hC j).1)
    (fun j => (enlargedFiberRadius_log_bound B C hB hC j).2) hi

end Yau.Blueprint.V04Proof
