import Yau.Proofs.P04PoleWeights

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem poleMultiplier_sub_one_compact {P : M.Carrier → ℝ} (hc : HasCompactSupport P) :
    HasCompactSupport (fun x => Real.exp (-P x/2)-1) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx hzero
  exact hx (by simp only [hzero,neg_zero,zero_div,Real.exp_zero,sub_self])

/-- Each fixed regularized multiplier is bounded because it is exactly one
off the actual compact support. The constant is allowed to depend on P. -/
theorem exists_bound_poleMultiplier {P : M.Carrier → ℝ} (hP : SmoothFn P)
    (hc : HasCompactSupport P) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |Real.exp (-P x/2)| ≤ C := by
  have hcontinuous := L18Aux.continuous_of_smoothFn hP
  have hm : Continuous (fun x => Real.exp (-P x/2)-1) :=
    ((Real.continuous_exp.comp (hcontinuous.neg.div_const 2)).sub continuous_const)
  obtain ⟨B,hB⟩ := (poleMultiplier_sub_one_compact hc).exists_bound_of_continuous hm
  refine ⟨max B 0+2,by positivity,fun x => ?_⟩
  have HH : |Real.exp (-P x/2)-1| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  have HA := abs_add_le (Real.exp (-P x/2)-1) (1 : ℝ)
  rw [sub_add_cancel,abs_one] at HA
  linarith [le_max_left B 0]

theorem one_le_poleMultiplier {P : M.Carrier → ℝ} (hP : ∀ x, P x ≤ 0) (x : M.Carrier) :
    1 ≤ Real.exp (-P x/2) := Real.one_le_exp_iff.mpr (by linarith [hP x])

end Yau.Proofs.P04Aux
