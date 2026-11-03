import Yau.LeafProofs.L05DiniKernelDefinitions

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem diniHeatD2_two_moments {n : ℕ} :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, 0 < a →
      Integrable (fun y : Space n => ‖diniHeatD2 a y‖) ∧
      Integrable (fun y : Space n => ‖diniHeatD2 a y‖*‖y‖^2) ∧
      (∫ y : Space n, ‖diniHeatD2 a y‖) ≤ M/a ∧
      (∫ y : Space n, ‖diniHeatD2 a y‖*‖y‖^2) ≤ M := by
  obtain ⟨C0,hC0,h0⟩ := L16Aux.gaussianKernel_secondFDeriv_weight_bound (n := n) (s := 0) le_rfl
  obtain ⟨C2,hC2,h2⟩ := L16Aux.gaussianKernel_secondFDeriv_weight_bound (n := n) (s := 2) (by norm_num)
  refine ⟨1+C0+C2,by positivity,?_⟩
  intro a ha
  have h0a := h0 a ha
  have h2a := h2 a ha
  have hi0 : Integrable (fun y : Space n => ‖diniHeatD2 a y‖) := by
    simpa only [diniHeatD2,Real.rpow_zero,mul_one] using h0a.1
  have hi2 : Integrable (fun y : Space n => ‖diniHeatD2 a y‖*‖y‖^2) := by
    simpa only [diniHeatD2,Real.rpow_two] using h2a.1
  have hb0 : (∫ y : Space n, ‖diniHeatD2 a y‖) ≤ C0/a := by
    convert! h0a.2 using 1 <;> norm_num [diniHeatD2,Real.rpow_neg_one,div_eq_mul_inv]
  have hb2 : (∫ y : Space n, ‖diniHeatD2 a y‖*‖y‖^2) ≤ C2 := by
    convert! h2a.2 using 1 <;> norm_num [diniHeatD2,Real.rpow_two]
  exact ⟨hi0,hi2,hb0.trans (div_le_div_of_nonneg_right (by linarith only [hC2]) ha.le),
    hb2.trans (by linarith only [hC0])⟩

end Yau.LeafProofs.L05Aux
