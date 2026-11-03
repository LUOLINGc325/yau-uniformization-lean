import spec.CHAIN.CONTRACTS

/-! Every positive terminal horizon admits a genuine native backward
scale inside the actual bounded-chart radius. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem exists_native_terminal_scale {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ 1 ∧
      ρ ^ 2 ≤ T - (ρ * (1 / 4)) ^ 2 / 4 := by
  let ρ : ℝ := min R (min 1 (Real.sqrt T / 2))
  have hρ : 0 < ρ := lt_min hR (lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr hT) (by norm_num)))
  have hρR : ρ ≤ R := min_le_left _ _
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρS : ρ ≤ Real.sqrt T / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hSquare : ρ ^ 2 ≤ (Real.sqrt T / 2) ^ 2 := pow_le_pow_left₀ hρ.le hρS 2
  have hRoot : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  refine ⟨ρ, hρ, hρR, hρ1, ?_⟩
  nlinarith

end Yau.NodeProofs.F01Aux
