import Yau.Proofs.C04BoundedGeometryChartsVolterra

/-! The Volterra identity is a consequence of the actual two derivative equations. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux

theorem second_order_integral_identity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Y V Z : ℝ → E)
    (hY : ∀ u, HasDerivAt Y (V u) u) (hV : ∀ u, HasDerivAt V (Z u) u)
    (t : ℝ) (hZ : IntervalIntegrable Z volume 0 t) :
    Y t = Y 0 + t • V 0 + ∫ u in 0..t, (t - u) • Z u := by
  have hW (u : ℝ) : HasDerivAt (fun s => (t - s) • V s + Y s)
      ((t - u) • Z u) u := by
    have H : HasDerivAt (fun s => (t - s) • V s + Y s)
        ((t - u) • Z u + (0 - 1 : ℝ) • V u + V u) u :=
      (((hasDerivAt_const u t).sub (hasDerivAt_id u)).smul (hV u)).add (hY u)
    simpa only [zero_sub, neg_one_smul, sub_add_cancel, ← sub_eq_add_neg] using H
  have hint : IntervalIntegrable (fun u => (t - u) • Z u) volume 0 t :=
    hZ.continuousOn_smul (continuous_const.sub continuous_id).continuousOn
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hW u) hint
  simp only [sub_self, zero_smul, zero_add, sub_zero] at H
  rw [H]
  abel

theorem volterra_identity_of_jacobi_equations {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (R Y V : ℝ → A) (hY : ∀ u, HasDerivAt Y (V u) u)
    (hV : ∀ u, HasDerivAt V (-(R u * Y u)) u)
    (hY₀ : Y 0 = 0) (hV₀ : V 0 = 1)
    {α : ℝ} (hR : ∀ u ∈ Icc (0 : ℝ) 1, ‖R u‖ ≤ α) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      Y t = t • (1 : A) - ∫ u in 0..t, (t - u) • (R u * Y u) := by
  have hcont : Continuous Y := continuous_iff_continuousAt.mpr fun u => (hY u).continuousAt
  obtain ⟨C, hC, hb⟩ := (isCompact_Icc.image hcont).isBounded.exists_pos_norm_le
  have hbY (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖Y u‖ ≤ C := hb _ ⟨u, hu, rfl⟩
  intro t ht
  have hZmeas : StronglyMeasurable (fun u => -(R u * Y u)) := by
    have heq : (fun u => -(R u * Y u)) = deriv V := by
      funext u
      exact (hV u).deriv.symm
    rw [heq]
    exact stronglyMeasurable_deriv V
  have hZ : IntervalIntegrable (fun u => -(R u * Y u)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    apply Integrable.of_bound hZmeas.aestronglyMeasurable (max α 0 * C)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
    rw [norm_neg]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ((hR u hu').trans (le_max_left _ _)) (hbY u hu')
        (norm_nonneg _) (le_max_right _ _))
  have H := second_order_integral_identity Y V (fun u => -(R u * Y u)) hY hV t hZ
  simpa only [hY₀, hV₀, zero_add, smul_neg, intervalIntegral.integral_neg,
    sub_eq_add_neg] using H

end Yau.Proofs.C04ChartsAux
