import Yau.Proofs.F05ExhaustionApproximants

/-! A countable family of genuine positive-time slabs covers every
positive time below the original finite horizon. -/

open Filter Set
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux

def F05ExhaustionTime (T : ℝ) (j : ℕ) : ℝ := (T/2)*F05ExhaustionError j

theorem F05_exhaustion_time_pos {T : ℝ} (hT : 0 < T) (j : ℕ) : 0 < F05ExhaustionTime T j :=
  mul_pos (by positivity) (F05_exhaustion_error_pos j)

theorem F05_exhaustion_time_lt {T : ℝ} (hT : 0 < T) (j : ℕ) : F05ExhaustionTime T j < T := by
  have h := mul_le_mul_of_nonneg_left (F05_exhaustion_error_le_one j) (by positivity : 0 ≤ T/2)
  dsimp only [F05ExhaustionTime]
  linarith

theorem F05_exhaustion_time_tendsto (T : ℝ) : Tendsto (F05ExhaustionTime T) atTop (𝓝 0) := by
  change Tendsto (fun j => (T/2)*F05ExhaustionError j) atTop (𝓝 0)
  have h := tendsto_const_nhds.mul F05_exhaustion_error_tendsto (a := T/2)
  simpa only [mul_zero] using h

theorem F05_exhaustion_time_cover (T : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ j : ℕ, F05ExhaustionTime T j < t :=
  ((F05_exhaustion_time_tendsto T).eventually (gt_mem_nhds ht)).exists

end Yau.Proofs.F05Aux
