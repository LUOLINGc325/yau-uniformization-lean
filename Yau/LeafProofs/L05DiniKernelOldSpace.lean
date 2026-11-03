import Yau.LeafProofs.L05DiniKernelRecent

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelOldSpaceDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOldSpaceDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOldSpaceHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelOldSpaceHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_old_age_geometry {r a : ℝ} (hr : 0 < r) (ha : a ∈ Set.Ioi (r^2)) :
    0 < a ∧ r ≤ Real.sqrt a := by
  have ha0 : 0 < a := (sq_pos_of_pos hr).trans ha
  exact ⟨ha0,Real.le_sqrt_of_sq_le ha.le⟩

theorem diniHeatD2_old_space_integral {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (eta B r : ℝ) (psi : ℝ → ℝ) (h : Space n),
      0 < eta → eta < 1 → 0 ≤ B → 0 < r → ‖h‖ ≤ r →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      Integrable (fun z : ℝ × Space n => ‖diniHeatD2 z.1 (z.2+h)-diniHeatD2 z.1 z.2‖*psi ‖z.2‖)
        ((volume.restrict (Set.Ioi (r^2))).prod volume) ∧
      (∫ a in Set.Ioi (r^2), ∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖) ≤
        C*diniBudget psi r := by
  obtain ⟨M,hM,hWeight⟩ := diniHeatD2_shift_weighted (n := n)
  refine ⟨16*M,by positivity,?_⟩
  intro eta B r psi h he he1 hB hr hh hm hz hmono hp
  have hAge := diniDyadicAverage_old_age_data he he1 hB hm hz hmono hp hr
  have hJI : IntegrableOn (fun a : ℝ => 4*M*‖h‖*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a))
      (Set.Ioi (r^2)) := by
    simpa only [IntegrableOn,mul_assoc] using hAge.1.const_mul (4*M*‖h‖)
  have hPI := dini_positive_product_integrable (n := n) (F := fun a y => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖) measurableSet_Ioi
    (dini_modulus_product_measurable (S := Set.Ioi (r^2)) (kappa := fun a y => ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖) measurableSet_Ioi
      (diniHeatD2_shift_norm_joint_continuous (fun _ ha => (dini_old_age_geometry hr ha).1) h) hm)
    (fun a ha y => mul_nonneg (norm_nonneg _) (dini_modulus_nonneg_norm hz (fun s hs => (hp s hs).1) y))
    (fun a ha => (hWeight eta B psi he he1 hB hm hz hmono hp a (dini_old_age_geometry hr ha).1
      h (hh.trans (dini_old_age_geometry hr ha).2)).1)
    hJI (fun a ha => (hWeight eta B psi he he1 hB hm hz hmono hp a (dini_old_age_geometry hr ha).1
      h (hh.trans (dini_old_age_geometry hr ha).2)).2)
  refine ⟨hPI.1,?_⟩
  have hFar := dini_far_nonneg hr (fun s hs => (hp s hs).1)
  calc
    _ ≤ ∫ a in Set.Ioi (r^2), 4*M*‖h‖*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a) := hPI.2
    _ = (4*M*‖h‖)*(∫ a in Set.Ioi (r^2), a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a)) := by
      rw [← integral_const_mul]
      congr 1
      ext a
      ring
    _ ≤ (4*M*‖h‖)*(4*(∫ s in Set.Ioi r, psi s/s^2)) :=
      mul_le_mul_of_nonneg_left hAge.2 (by positivity)
    _ ≤ (16*M)*(r*(∫ s in Set.Ioi r, psi s/s^2)) := by nlinarith only [mul_le_mul_of_nonneg_right hh hFar,hM]
    _ ≤ (16*M)*diniBudget psi r :=
      mul_le_mul_of_nonneg_left (dini_far_part_le_budget hr (fun s hs => (hp s hs).1)) (by positivity)

end Yau.LeafProofs.L05Aux
