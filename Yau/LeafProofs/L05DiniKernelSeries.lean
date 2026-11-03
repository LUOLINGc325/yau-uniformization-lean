import Yau.LeafProofs.L05DiniKernelDefinitions

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniDyadicAverage_summable {psi : ℝ → ℝ} {eta B R : ℝ}
    (_he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hR : 0 < R)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) :
    Summable (fun k : ℕ => (1/4:ℝ)^k*psi ((2:ℝ)^k*R)) ∧ diniDyadicAverage psi R ≤ 2*B*R^eta := by
  have hBR : 0 ≤ B*R^eta := mul_nonneg hB (Real.rpow_nonneg hR.le _)
  have hnonneg (k : ℕ) : 0 ≤ (1/4:ℝ)^k*psi ((2:ℝ)^k*R) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (hpsi _ (mul_pos (pow_pos (by norm_num) _) hR)).1
  have hbound (k : ℕ) : (1/4:ℝ)^k*psi ((2:ℝ)^k*R) ≤ (B*R^eta)*(1/2:ℝ)^k := by
    have htwo : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have hpow : ((2:ℝ)^k)^eta ≤ (2:ℝ)^k := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le htwo he1.le
    have hgeom : (1/4:ℝ)^k*(2:ℝ)^k=(1/2:ℝ)^k := by rw [← mul_pow]; norm_num
    calc
      _ ≤ (1/4:ℝ)^k*(B*((2:ℝ)^k*R)^eta) :=
        mul_le_mul_of_nonneg_left (hpsi _ (mul_pos (pow_pos (by norm_num) _) hR)).2 (pow_nonneg (by norm_num) _)
      _ = (B*R^eta)*((1/4:ℝ)^k*((2:ℝ)^k)^eta) := by
        rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hR.le]
        ring
      _ ≤ (B*R^eta)*((1/4:ℝ)^k*(2:ℝ)^k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _)) hBR
      _ = _ := by rw [hgeom]
  have hgeom := (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left (B*R^eta)
  have hs := Summable.of_nonneg_of_le hnonneg hbound hgeom
  refine ⟨hs,?_⟩
  unfold diniDyadicAverage
  have hh := hs.tsum_le_tsum hbound hgeom
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)] at hh
  exact hh.trans_eq (by norm_num; ring)

end Yau.LeafProofs.L05Aux
