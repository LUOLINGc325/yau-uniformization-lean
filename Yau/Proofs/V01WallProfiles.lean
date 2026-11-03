import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! V01 scratch source: actual smooth wall cutoffs with exactly the open
positivity regions and plateaus in the original localization contract. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

def wallProfile (k r : ℝ) : ℝ := Real.smoothTransition (k * (1 - r))

theorem wallProfile_contDiff (k : ℝ) : ContDiff ℝ ∞ (wallProfile k) := by
  unfold wallProfile
  fun_prop

theorem wallProfile_properties {k : ℝ} (hk : 0 < k) (r : ℝ) :
    0 ≤ wallProfile k r ∧ wallProfile k r ≤ 1 ∧
      (0 < wallProfile k r ↔ r < 1) := by
  refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, ?_⟩
  constructor
  · intro hp
    by_contra! hr
    have harg : k * (1 - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
    have hz : wallProfile k r = 0 := Real.smoothTransition.zero_of_nonpos harg
    linarith
  · intro hr
    exact Real.smoothTransition.pos_of_pos (mul_pos hk (sub_pos.mpr hr))

theorem wallProfile_base_plateau {r : ℝ} (hr : r ≤ 2 / 3) : wallProfile 3 r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem wallProfile_fiber_plateau {r : ℝ} (hr : r ≤ 1 / 2) : wallProfile 2 r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem wallProfiles_actual {n q : ℕ} {X : KahlerManifold n} (d : VariationData X q) :
    WallProfiles {d with profileBase := wallProfile 3, profileFiber := wallProfile 2} := by
  refine ⟨wallProfile_contDiff 3, wallProfile_contDiff 2, ?_, ?_⟩
  · intro r
    obtain ⟨hn, hu, hp⟩ := wallProfile_properties (by norm_num : (0 : ℝ) < 3) r
    exact ⟨hn, hu, hp, fun hr => wallProfile_base_plateau hr⟩
  · intro r
    obtain ⟨hn, hu, hp⟩ := wallProfile_properties (by norm_num : (0 : ℝ) < 2) r
    exact ⟨hn, hu, hp, fun hr => wallProfile_fiber_plateau hr⟩

end Yau.Blueprint.V01Proof
