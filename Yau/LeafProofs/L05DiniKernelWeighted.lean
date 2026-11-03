import Yau.LeafProofs.L05DiniKernelAnnuliMass
import Yau.LeafProofs.L05DiniKernelMoments
import Yau.LeafProofs.L05DiniKernelSpatialMoment
import Yau.LeafProofs.L05DiniKernelTimeMoment

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelWeightedDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelWeightedDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelWeightedHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelWeightedHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_age_power_succ {a : ℝ} (ha : 0 < a) (p : ℝ) : a^p*a=a^(p+1) := by
  rw [Real.rpow_add ha,Real.rpow_one]

theorem diniHeatD2_weighted {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ (eta B : ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → Measurable psi → psi 0=0 →
      MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      ∀ a : ℝ, 0 < a → Integrable (fun y : Space n => ‖diniHeatD2 a y‖*psi ‖y‖) ∧
        (∫ y : Space n, ‖diniHeatD2 a y‖*psi ‖y‖) ≤ 4*M*a⁻¹*diniDyadicAverage psi (Real.sqrt a) := by
  obtain ⟨M,hM,hMom⟩ := diniHeatD2_two_moments (n := n)
  refine ⟨M,hM,?_⟩
  intro eta B psi he he1 hB hm hz hmono hp a ha
  have hs := hMom a ha
  have hQ : 0 ≤ M/a := div_nonneg hM.le ha.le
  have hEq : (M/a)*(Real.sqrt a)^2=M := by rw [Real.sq_sqrt ha.le,div_mul_cancel₀ _ ha.ne']
  have hh := two_moments_dini_integral he he1 hB hQ (Real.sqrt_pos.mpr ha) hm hz hmono hp
    (fun y => norm_nonneg (diniHeatD2 a y)) hs.1 hs.2.1 hs.2.2.1 (hs.2.2.2.trans_eq hEq.symm)
  exact ⟨hh.1,hh.2.trans_eq (by simp only [div_eq_mul_inv]; ring)⟩

theorem diniHeatD2_shift_weighted {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ (eta B : ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → Measurable psi → psi 0=0 →
      MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      ∀ a : ℝ, 0 < a → ∀ h : Space n, ‖h‖ ≤ Real.sqrt a →
      Integrable (fun y : Space n => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖) ∧
        (∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖) ≤
          4*M*‖h‖*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a) := by
  obtain ⟨M,hM,hMom⟩ := diniHeatD2_shift_two_moments (n := n)
  refine ⟨M,hM,?_⟩
  intro eta B psi he he1 hB hm hz hmono hp a ha h hh
  have hs := hMom a ha h hh
  have hQ : 0 ≤ M*‖h‖*a^(-(3/2:ℝ)) := by positivity
  have hPow : a^(-(3/2:ℝ))*a=a^(-(1/2:ℝ)) := by
    convert! dini_age_power_succ ha (-(3/2:ℝ)) using 1 <;> norm_num
  have hEq : (M*‖h‖*a^(-(3/2:ℝ)))*(Real.sqrt a)^2=M*‖h‖*a^(-(1/2:ℝ)) := by
    rw [Real.sq_sqrt ha.le]
    calc
      _=(M*‖h‖)*(a^(-(3/2:ℝ))*a) := by ring
      _=_ := by rw [hPow]
  have hb := two_moments_dini_integral he he1 hB hQ (Real.sqrt_pos.mpr ha) hm hz hmono hp
    (fun y => norm_nonneg (diniHeatD2 a (y+h)-diniHeatD2 a y)) hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.trans_eq hEq.symm)
  exact ⟨hb.1,hb.2.trans_eq (by ring)⟩

theorem diniHeatD2_time_weighted {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ (eta B : ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → Measurable psi → psi 0=0 →
      MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      ∀ a : ℝ, 0 < a → ∀ delta : ℝ, 0 ≤ delta →
      Integrable (fun y : Space n => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖) ∧
        (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖) ≤
          4*M*delta*a^(-(2:ℝ))*diniDyadicAverage psi (Real.sqrt a) := by
  obtain ⟨M,hM,hMom⟩ := diniHeatD2_time_two_moments (n := n)
  refine ⟨M,hM,?_⟩
  intro eta B psi he he1 hB hm hz hmono hp a ha delta hd
  have hs := hMom a ha delta hd
  have hQ : 0 ≤ M*delta*a^(-(2:ℝ)) := by positivity
  have hPow : a^(-(2:ℝ))*a=a⁻¹ := by
    convert! dini_age_power_succ ha (-(2:ℝ)) using 1 <;> norm_num [Real.rpow_neg_one]
  have hEq : (M*delta*a^(-(2:ℝ)))*(Real.sqrt a)^2=M*delta/a := by
    rw [Real.sq_sqrt ha.le]
    calc
      _=(M*delta)*(a^(-(2:ℝ))*a) := by ring
      _=_ := by rw [hPow,div_eq_mul_inv]
  have hb := two_moments_dini_integral he he1 hB hQ (Real.sqrt_pos.mpr ha) hm hz hmono hp
    (fun y => norm_nonneg (diniHeatD2 (a+delta) y-diniHeatD2 a y)) hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.trans_eq hEq.symm)
  exact ⟨hb.1,hb.2.trans_eq (by ring)⟩

end Yau.LeafProofs.L05Aux
