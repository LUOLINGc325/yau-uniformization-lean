import Yau.Proofs.C01ExitBarrier

/-! The exact square-root-time first-exit barrier tends to infinity
with the original radius. All differential inputs concern genuine upper
touching path lengths rather than a derivative of their infimum. -/

noncomputable section

open scoped Topology

namespace Yau.NodeProofs.C01Aux

open Set Filter

theorem exit_profile_exponential_lower_bound
    (l : ℝ → ℝ) (L C T : ℝ) (hT : 0 ≤ T) (hC : 0 < C)
    (hl : ContinuousOn l (Icc 0 T)) (hzero : l 0 = L)
    (hpaths : ∀ t ∈ Ioc 0 T, ∃ (f : ℝ → ℝ) (d : ℝ),
      f t = l t ∧ (∀ u ∈ Icc 0 T, l u ≤ f u) ∧
      HasDerivAt f d t ∧ -(C / Real.sqrt t) * (1 + l t) ≤ d) :
    ∀ t ∈ Icc 0 T, (1 + L) * Real.exp (-2 * C * Real.sqrt t) - 1 ≤ l t := by
  let b : ℝ → ℝ := fun t => (1 + L) * Real.exp (-2 * C * Real.sqrt t) - 1
  have hb : ContinuousOn b (Icc 0 T) := by
    apply Continuous.continuousOn
    dsimp only [b]
    fun_prop
  have hb0 : b 0 ≤ l 0 := by simp only [b, Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one, add_sub_cancel_left, hzero]; exact le_rfl
  exact lower_bound_of_touching_lengths l b (fun t => C / Real.sqrt t) hT hl hb hb0
    (fun t ht => exitExponential_hasDerivAt L C ht.1)
    (fun t ht => div_pos hC (Real.sqrt_pos.mpr ht.1)) hpaths

theorem exit_exponential_unbounded_radius (C t R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ R < (1 + L) * Real.exp (-2 * C * Real.sqrt t) - 1 := by
  let a := Real.exp (-2 * C * Real.sqrt t)
  have ha : 0 < a := Real.exp_pos _
  let L := max 0 ((R + 2) / a)
  have hL : 0 ≤ L := le_max_left _ _
  have hscaled : R + 2 ≤ L * a := (div_le_iff₀ ha).mp (le_max_right _ _)
  refine ⟨L, hL, ?_⟩
  change R < (1 + L) * a - 1
  nlinarith

end Yau.NodeProofs.C01Aux
