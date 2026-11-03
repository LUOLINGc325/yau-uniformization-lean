import Yau.LeafProofs.L05DiniKernelOldSpace

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelOldTimeDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOldTimeDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOldTimeHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelOldTimeHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_old_time_scalar_le {r a delta : ℝ} (hr : 0 < r) (ha : a ∈ Set.Ioi (r^2))
    (hd : delta ≤ r^2) : delta*a^(-(2:ℝ)) ≤ r*a^(-(3/2:ℝ)) := by
  have hg := dini_old_age_geometry hr ha
  have hdelta : delta ≤ r*Real.sqrt a := hd.trans (by nlinarith only [mul_le_mul_of_nonneg_left hg.2 hr.le])
  have hPow : Real.sqrt a*a^(-(2:ℝ))=a^(-(3/2:ℝ)) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hg.1]
    congr 1
    ring
  calc
    _ ≤ (r*Real.sqrt a)*a^(-(2:ℝ)) :=
      mul_le_mul_of_nonneg_right hdelta (Real.rpow_nonneg hg.1.le _)
    _ = r*(Real.sqrt a*a^(-(2:ℝ))) := by ring
    _ = _ := by rw [hPow]

theorem diniHeatD2_old_time_integral {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (eta B r delta : ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → 0 < r → 0 ≤ delta → delta ≤ r^2 →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      Integrable (fun z : ℝ × Space n => ‖diniHeatD2 (z.1+delta) z.2-diniHeatD2 z.1 z.2‖*psi ‖z.2‖)
        ((volume.restrict (Set.Ioi (r^2))).prod volume) ∧
      (∫ a in Set.Ioi (r^2), ∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖) ≤
        C*diniBudget psi r := by
  obtain ⟨M,hM,hWeight⟩ := diniHeatD2_time_weighted (n := n)
  refine ⟨16*M,by positivity,?_⟩
  intro eta B r delta psi he he1 hB hr hd hd2 hm hz hmono hp
  have hAge := diniDyadicAverage_old_age_data he he1 hB hm hz hmono hp hr
  have hData := diniDyadicAverage_data he he1 hB hm hz hmono hp
  have hJI : IntegrableOn (fun a : ℝ => 4*M*r*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a))
      (Set.Ioi (r^2)) := by
    simpa only [IntegrableOn,mul_assoc] using hAge.1.const_mul (4*M*r)
  have hBound (a : ℝ) (ha : a ∈ Set.Ioi (r^2)) :
      (∫ y : Space n, ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖) ≤
        4*M*r*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a) := by
    have ha0 := (dini_old_age_geometry hr ha).1
    apply (hWeight eta B psi he he1 hB hm hz hmono hp a ha0 delta hd).2.trans
    have hmul := mul_le_mul_of_nonneg_left (dini_old_time_scalar_le hr ha hd2) (by positivity : 0 ≤ 4*M)
    have hh := mul_le_mul_of_nonneg_right hmul (hData.2.2.2 _ (Real.sqrt_pos.mpr ha0)).1
    convert! hh using 1 <;> ring
  have hPI := dini_positive_product_integrable (n := n)
    (F := fun a y => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖*psi ‖y‖) measurableSet_Ioi
    (dini_modulus_product_measurable (S := Set.Ioi (r^2))
      (kappa := fun a y => ‖diniHeatD2 (a+delta) y-diniHeatD2 a y‖) measurableSet_Ioi
      (diniHeatD2_time_norm_joint_continuous (fun _ ha => (dini_old_age_geometry hr ha).1) hd) hm)
    (fun a ha y => mul_nonneg (norm_nonneg _) (dini_modulus_nonneg_norm hz (fun s hs => (hp s hs).1) y))
    (fun a ha => (hWeight eta B psi he he1 hB hm hz hmono hp a (dini_old_age_geometry hr ha).1 delta hd).1)
    hJI hBound
  refine ⟨hPI.1,?_⟩
  calc
    _ ≤ ∫ a in Set.Ioi (r^2), 4*M*r*a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a) := hPI.2
    _ = (4*M*r)*(∫ a in Set.Ioi (r^2), a^(-(3/2:ℝ))*diniDyadicAverage psi (Real.sqrt a)) := by
      rw [← integral_const_mul]
      congr 1
      ext a
      ring
    _ ≤ (4*M*r)*(4*(∫ s in Set.Ioi r, psi s/s^2)) :=
      mul_le_mul_of_nonneg_left hAge.2 (by positivity)
    _ = (16*M)*(r*(∫ s in Set.Ioi r, psi s/s^2)) := by ring
    _ ≤ (16*M)*diniBudget psi r :=
      mul_le_mul_of_nonneg_left (dini_far_part_le_budget hr (fun s hs => (hp s hs).1)) (by positivity)

end Yau.LeafProofs.L05Aux
