import Yau.Proofs.F04SublevelMass

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

theorem negative_nat_power_bound {R s : ℝ} (hR : 0 < R) (hRs : R ≤ s) (k : ℕ) :
    s ^ (-(k : ℤ)) ≤ 1 / R ^ k := by
  rw [zpow_neg, zpow_natCast, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos hR k) (pow_le_pow_left₀ hR.le hRs k)

theorem polynomial_mass_error_decay {n k : ℕ} {R : ℝ} (hR : 1 ≤ R) (hk : 2 * n ≤ k) :
    R ^ (2 * n + 1) / (R ^ k * R ^ 2) ≤ 1 / R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp : R ^ (2 * n + 1) ≤ R ^ (k + 1) :=
    pow_le_pow_right₀ hR (Nat.add_le_add_right hk 1)
  calc
    _ ≤ R ^ (k + 1) / (R ^ k * R ^ 2) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = 1 / R := by
      rw [pow_succ]
      field_simp [hRp.ne']

end Yau.F04Proof
