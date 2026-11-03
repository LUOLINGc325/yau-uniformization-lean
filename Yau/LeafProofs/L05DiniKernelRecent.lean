import Yau.LeafProofs.L05DiniKernelProduct

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelRecentDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelRecentDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelRecentHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelRecentHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_modulus_nonneg_norm {n : ℕ} {psi : ℝ → ℝ} (hz : psi 0=0)
    (hp : ∀ s : ℝ, 0 < s → 0 ≤ psi s) (y : Space n) : 0 ≤ psi ‖y‖ := by
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h,hz]
  · exact hp _ h

theorem diniHeatD2_recent_integral {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (eta B R : ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → 0 < R →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      Integrable (fun z : ℝ × Space n => ‖diniHeatD2 z.1 z.2‖*psi ‖z.2‖)
        ((volume.restrict (Set.Ioc (0:ℝ) (R^2))).prod volume) ∧
      (∫ a in (0:ℝ)..R^2, ∫ y : Space n, ‖diniHeatD2 a y‖*psi ‖y‖) ≤ C*diniBudget psi R := by
  obtain ⟨M,hM,hWeight⟩ := diniHeatD2_weighted (n := n)
  refine ⟨16*M,by positivity,?_⟩
  intro eta B R psi he he1 hB hR hm hz hmono hp
  have hAge := diniDyadicAverage_recent_age_data he he1 hB hm hz hmono hp hR
  have hJI : IntegrableOn (fun a : ℝ => 4*M*a⁻¹*diniDyadicAverage psi (Real.sqrt a))
      (Set.Ioc 0 (R^2)) := by
    have hh := hAge.1.1.const_mul (4*M)
    simpa only [IntegrableOn,mul_assoc] using hh
  have hPI := dini_positive_product_integrable (n := n) (F := fun a y => ‖diniHeatD2 a y‖*psi ‖y‖) measurableSet_Ioc
    (dini_modulus_product_measurable (S := Set.Ioc 0 (R^2)) (kappa := fun a y => ‖diniHeatD2 a y‖) measurableSet_Ioc
      (diniHeatD2_norm_joint_continuous (fun _ ha => ha.1)) hm)
    (fun a ha y => mul_nonneg (norm_nonneg _) (dini_modulus_nonneg_norm hz (fun s hs => (hp s hs).1) y))
    (fun a ha => (hWeight eta B psi he he1 hB hm hz hmono hp a ha.1).1)
    hJI (fun a ha => (hWeight eta B psi he he1 hB hm hz hmono hp a ha.1).2)
  refine ⟨hPI.1,?_⟩
  rw [intervalIntegral.integral_of_le (sq_nonneg R)]
  calc
    _ ≤ ∫ a in Set.Ioc 0 (R^2), 4*M*a⁻¹*diniDyadicAverage psi (Real.sqrt a) := hPI.2
    _ = 4*M*(∫ a in (0:ℝ)..R^2, a⁻¹*diniDyadicAverage psi (Real.sqrt a)) := by
      rw [intervalIntegral.integral_of_le (sq_nonneg R),← integral_const_mul]
      congr 1
      ext a
      ring
    _ ≤ 4*M*(4*diniBudget psi R) := mul_le_mul_of_nonneg_left hAge.2 (by positivity)
    _ = _ := by ring

end Yau.LeafProofs.L05Aux
