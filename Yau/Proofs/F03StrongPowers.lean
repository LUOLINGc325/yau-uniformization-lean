import Yau.Proofs.F03L2FilterConvergence

/-! Strong convergence of genuine contraction powers. -/
noncomputable section
open Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
set_option maxHeartbeats 1000000

theorem contraction_powers_strong_tendsto {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : ℕ → H →L[ℝ] H) (B : H →L[ℝ] H)
    (hA : ∀ j x, ‖A j x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun j => A j x) atTop (𝓝 (B x)))
    (m : ℕ) (f : H) : Tendsto (fun j => ((A j)^m) f) atTop (𝓝 ((B^m) f)) := by
  induction m with
  | zero => simpa only [pow_zero,one_apply_eq_self] using tendsto_const_nhds
  | succ m hm =>
    have hdiff := tendsto_iff_norm_sub_tendsto_zero.mp hm
    have hzero : Tendsto (fun j => A j (((A j)^m) f-(B^m) f)) atTop (𝓝 0) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [sub_zero]
      exact squeeze_zero (fun j => norm_nonneg _) (fun j => hA j _) hdiff
    have hsum := hzero.add (hlim ((B^m) f))
    simpa only [zero_add,map_sub,sub_add_cancel,pow_succ',mul_apply_eq_comp] using hsum

end Yau.Proofs.F03Aux
