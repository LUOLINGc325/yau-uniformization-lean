import Yau.LeafProofs.L05DiniKernelDyadicIntegrals

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniDyadicAverage_recent_age_data {psi : ℝ → ℝ} {eta B R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi) (hzero : psi 0=0)
    (hmono : MonotoneOn psi (Set.Ioi (0:ℝ)))
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hR : 0 < R) :
    IntervalIntegrable (fun a : ℝ => a⁻¹*diniDyadicAverage psi (Real.sqrt a)) volume 0 (R^2) ∧
      (∫ a in (0:ℝ)..R^2, a⁻¹*diniDyadicAverage psi (Real.sqrt a)) ≤ 4*diniBudget psi R := by
  have hd := diniDyadicAverage_data he he1 hB hm hzero hmono hpsi
  have hAmp : 0 ≤ 2*B := mul_nonneg (by norm_num) hB
  have hs := dini_recent_scalar_data he he1 hAmp hd.1 hd.2.2.2 zero_lt_one hR
  simp only [one_mul] at hs
  refine ⟨hs.1,?_⟩
  have hb := diniDyadicAverage_near_le he he1 hB hm hpsi hR
  linarith only [hs.2,hb]

theorem diniDyadicAverage_old_age_data {psi : ℝ → ℝ} {eta B R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi) (hzero : psi 0=0)
    (hmono : MonotoneOn psi (Set.Ioi (0:ℝ)))
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hR : 0 < R) :
    IntegrableOn (fun a : ℝ => a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a)) (Set.Ioi (R^2)) ∧
      (∫ a in Set.Ioi (R^2), a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a)) ≤
        4*(∫ s in Set.Ioi R, psi s/s^2) := by
  have hd := diniDyadicAverage_data he he1 hB hm hzero hmono hpsi
  have hAmp : 0 ≤ 2*B := mul_nonneg (by norm_num) hB
  have hs := dini_old_scalar_data he he1 hAmp hd.1 hd.2.2.2 zero_lt_one hR
  simp only [one_mul,mul_one] at hs
  refine ⟨hs.1,?_⟩
  have hb := diniDyadicAverage_far_le he he1 hB hm hpsi hR
  linarith only [hs.2,hb]

end Yau.LeafProofs.L05Aux
