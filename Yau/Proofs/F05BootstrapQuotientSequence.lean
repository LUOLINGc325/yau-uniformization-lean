import Yau.Proofs.F05BootstrapDefinitions

/-! One positive quotient sequence stays inside every fixed numerical
buffer and tends to zero. The buffer is fixed before the sequence index. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux

def F05QuotientScale (η : ℝ) (k : ℕ) : ℝ := η/((k+1 : ℕ) : ℝ)

theorem F05_quotient_scale_pos {η : ℝ} (hη : 0 < η) (k : ℕ) : 0 < F05QuotientScale η k := by
  unfold F05QuotientScale
  positivity

theorem F05_quotient_scale_le {η : ℝ} (hη : 0 ≤ η) (k : ℕ) : F05QuotientScale η k ≤ η := by
  have hDen : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  unfold F05QuotientScale
  exact (div_le_self hη hDen)

theorem F05_quotient_scale_tendsto (η : ℝ) : Tendsto (F05QuotientScale η) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => η/((k+1 : ℕ) : ℝ)) atTop (𝓝 0)
  have hInv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (hInv.comp (tendsto_add_atTop_nat 1)).const_mul η
  simpa only [F05QuotientScale,Function.comp_def,div_eq_mul_inv,mul_zero] using h

end Yau.Proofs.F05Aux
