import Yau.Proofs.D02PotentialL1

/-! Actual compact L¹ convergence supplies an all-index compact L¹ bound,
including the finitely many indices before any later mass estimate. -/

open scoped Topology
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem uniform_compact_L1_of_L1_tendsto {S : Set ℂ} (hS : IsCompact S)
    (v : ℕ → ℂ → ℝ) (u : ℂ → ℝ) (hv : ∀ j, ContinuousOn (v j) S)
    (hu : IntegrableOn u S volume)
    (hconv : Tendsto (fun j => ∫ z in S, |v j z - u z|) atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ∫ z in S, |v j z| ≤ M := by
  obtain ⟨B, hB⟩ := hconv.bddAbove_range
  let M : ℝ := max B 0 + ∫ z in S, |u z|
  refine ⟨M, add_nonneg (le_max_right B 0) (integral_nonneg fun _ => abs_nonneg _), fun j => ?_⟩
  have hiv : IntegrableOn (v j) S volume := (hv j).integrableOn_compact hS
  have hidiff : IntegrableOn (fun z => |v j z - u z|) S volume := by
    simpa only [IntegrableOn, Pi.sub_apply, Real.norm_eq_abs] using (hiv.sub hu).norm
  have hiu : IntegrableOn (fun z => |u z|) S volume := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using hu.norm
  have hivabs : IntegrableOn (fun z => |v j z|) S volume := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using hiv.norm
  calc
    _ ≤ ∫ z in S, |v j z - u z| + |u z| := by
      apply integral_mono hivabs (hidiff.add hiu)
      intro z
      change |v j z| ≤ |v j z - u z| + |u z|
      simpa only [Real.norm_eq_abs, sub_add_cancel] using norm_add_le (v j z - u z) (u z)
    _ = (∫ z in S, |v j z - u z|) + ∫ z in S, |u z| := integral_add hidiff hiu
    _ ≤ M := by
      dsimp only [M]
      linarith [hB ⟨j, rfl⟩, le_max_left B 0]

end Yau.NodeProofs.D02Aux
