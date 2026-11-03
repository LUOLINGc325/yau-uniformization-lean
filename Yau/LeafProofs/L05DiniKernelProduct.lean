import Yau.LeafProofs.L05DiniKernelWeighted
import Yau.LeafProofs.L05DiniKernelDyadicAges

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelProductDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelProductDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelProductHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelProductHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_modulus_product_measurable {n : ℕ} {S : Set ℝ} {kappa : ℝ → Space n → ℝ}
    {psi : ℝ → ℝ} (hS : MeasurableSet S)
    (hc : ContinuousOn (Function.uncurry kappa) (S ×ˢ Set.univ)) (hm : Measurable psi) :
    AEStronglyMeasurable (fun z : ℝ × Space n => kappa z.1 z.2*psi ‖z.2‖)
      ((volume.restrict S).prod volume) := by
  have hProd : (volume.restrict S).prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict (S ×ˢ Set.univ) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Space n))) S Set.univ)
  rw [hProd]
  exact (hc.aestronglyMeasurable (hS.prod MeasurableSet.univ)).mul
    ((hm.comp (measurable_norm.comp measurable_snd)).aestronglyMeasurable)

theorem dini_positive_product_integrable {n : ℕ} {S : Set ℝ} {F : ℝ → Space n → ℝ}
    {J : ℝ → ℝ} (hS : MeasurableSet S)
    (hm : AEStronglyMeasurable (Function.uncurry F) ((volume.restrict S).prod volume))
    (hpos : ∀ a ∈ S, ∀ y, 0 ≤ F a y) (hFI : ∀ a ∈ S, Integrable (F a))
    (hJI : IntegrableOn J S) (hbound : ∀ a ∈ S, (∫ y, F a y) ≤ J a) :
    Integrable (Function.uncurry F) ((volume.restrict S).prod volume) ∧
      (∫ a in S, ∫ y, F a y) ≤ ∫ a in S, J a := by
  have hFnI : Integrable (fun a : ℝ => ∫ y : Space n, ‖F a y‖) (volume.restrict S) := by
    apply hJI.mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem hS] with a ha
    have heq : (fun y : Space n => ‖F a y‖) = F a := by
      funext y
      exact Real.norm_of_nonneg (hpos a ha y)
    change ‖∫ y : Space n, ‖F a y‖‖ ≤ J a
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hpos a ha))]
    exact hbound a ha
  have hprod : Integrable (Function.uncurry F) ((volume.restrict S).prod volume) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem hS] with a ha
    exact hFI a ha
  refine ⟨hprod,integral_mono_ae hprod.integral_prod_left hJI ?_⟩
  filter_upwards [ae_restrict_mem hS] with a ha
  exact hbound a ha

theorem diniHeatD2_norm_joint_continuous {n : ℕ} {S : Set ℝ} (hS : S ⊆ Set.Ioi 0) :
    ContinuousOn (fun z : ℝ × Space n => ‖diniHeatD2 z.1 z.2‖) (S ×ˢ Set.univ) := by
  intro p hp
  exact ((L16Aux.gaussianKernel_secondFDeriv_joint_smooth (hS hp.1) p.2).continuousAt.norm).continuousWithinAt

theorem diniHeatD2_shift_norm_joint_continuous {n : ℕ} {S : Set ℝ}
    (hS : S ⊆ Set.Ioi 0) (h : Space n) :
    ContinuousOn (fun z : ℝ × Space n => ‖diniHeatD2 z.1 (z.2+h)-diniHeatD2 z.1 z.2‖)
      (S ×ˢ Set.univ) := by
  intro p hp
  have hc : ContinuousAt (fun z : ℝ × Space n => diniHeatD2 z.1 (z.2+h)) p :=
    ContinuousAt.comp (f := fun z : ℝ × Space n => (z.1,z.2+h))
      (g := fun z : ℝ × Space n => diniHeatD2 z.1 z.2)
      (L16Aux.gaussianKernel_secondFDeriv_joint_smooth (hS hp.1) (p.2+h)).continuousAt
      (by fun_prop)
  exact (hc.sub (L16Aux.gaussianKernel_secondFDeriv_joint_smooth (hS hp.1) p.2).continuousAt).norm.continuousWithinAt

theorem diniHeatD2_time_norm_joint_continuous {n : ℕ} {S : Set ℝ}
    (hS : S ⊆ Set.Ioi 0) {delta : ℝ} (hd : 0 ≤ delta) :
    ContinuousOn (fun z : ℝ × Space n => ‖diniHeatD2 (z.1+delta) z.2-diniHeatD2 z.1 z.2‖)
      (S ×ˢ Set.univ) := by
  intro p hp
  have hc : ContinuousAt (fun z : ℝ × Space n => diniHeatD2 (z.1+delta) z.2) p :=
    ContinuousAt.comp (f := fun z : ℝ × Space n => (z.1+delta,z.2))
      (g := fun z : ℝ × Space n => diniHeatD2 z.1 z.2)
      (L16Aux.gaussianKernel_secondFDeriv_joint_smooth (add_pos_of_pos_of_nonneg (hS hp.1) hd) p.2).continuousAt
      (by fun_prop)
  exact (hc.sub (L16Aux.gaussianKernel_secondFDeriv_joint_smooth (hS hp.1) p.2).continuousAt).norm.continuousWithinAt

theorem dini_far_part_le_budget {psi : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s) :
    r*(∫ s in Set.Ioi r, psi s/s^2) ≤ diniBudget psi r := by
  apply le_add_of_nonneg_left
  apply intervalIntegral.integral_nonneg hr.le
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · simp [← h]
  · exact div_nonneg (hpsi s h) h.le

end Yau.LeafProofs.L05Aux
