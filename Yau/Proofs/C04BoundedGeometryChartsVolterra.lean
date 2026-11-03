import Mathlib

/-! The quantitative Volterra estimate for the actual radial Jacobi equation. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

theorem jacobi_volterra_norm_bound (R Y : ℝ → A) (hY : ContinuousOn Y (Icc 0 1))
    {α : ℝ} (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2)
    (hR : ∀ u ∈ Icc (0 : ℝ) 1, ‖R u‖ ≤ α)
    (hVolterra : ∀ t ∈ Icc (0 : ℝ) 1,
      Y t = t • (1 : A) - ∫ u in 0..t, (t - u) • (R u * Y u)) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖Y t‖ ≤ 2) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖Y t - t • (1 : A)‖ ≤ 2 * α := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hY.norm
  let M := ‖Y s‖
  have hM : 0 ≤ M := norm_nonneg _
  have hsup (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖Y u‖ ≤ M := hmax hu
  have hI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖∫ u in 0..t, (t - u) • (R u * Y u)‖ ≤ α * M := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := α * M) (f := fun u => (t - u) • (R u * Y u)) (by
        intro u hu
        rw [uIoc_of_le ht.1] at hu
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.trans ht.2⟩
        have hdiff : |t - u| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hu.2)]
          linarith [hu'.1, ht.2]
        have hprod : ‖R u * Y u‖ ≤ α * M :=
          (norm_mul_le _ _).trans (mul_le_mul (hR u hu') (hsup u hu') (norm_nonneg _) hα)
        calc
          ‖(t - u) • (R u * Y u)‖ = |t - u| * ‖R u * Y u‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * (α * M) := mul_le_mul hdiff hprod (norm_nonneg _) (by norm_num)
          _ = α * M := one_mul _)
    calc
      _ ≤ (α * M) * |t - 0| := H
      _ = (α * M) * t := by rw [sub_zero, abs_of_nonneg ht.1]
      _ ≤ α * M := mul_le_of_le_one_right (mul_nonneg hα hM) ht.2
  have hYbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖Y t‖ ≤ 1 + α * M := by
    rw [hVolterra t ht]
    have hlin : ‖t • (1 : A)‖ ≤ 1 := by simpa [norm_smul, abs_of_nonneg ht.1] using ht.2
    exact (norm_sub_le _ _).trans (add_le_add hlin (hI t ht))
  have hMle : M ≤ 1 + α * M := hYbound s hs
  have hM2 : M ≤ 2 := by
    have hh : 0 ≤ (1 / 2 - α) * M := mul_nonneg (sub_nonneg.mpr hsmall) hM
    nlinarith
  refine ⟨fun t ht => (hsup t ht).trans hM2, ?_⟩
  intro t ht
  rw [hVolterra t ht, sub_sub_cancel_left, norm_neg]
  exact (hI t ht).trans (by nlinarith [mul_nonneg hα (sub_nonneg.mpr hM2)])

theorem jacobi_volterra_close_at_one (R Y : ℝ → A) (hY : ContinuousOn Y (Icc 0 1))
    {α : ℝ} (hα : 0 ≤ α) (hsmall : α ≤ 1 / 8)
    (hR : ∀ u ∈ Icc (0 : ℝ) 1, ‖R u‖ ≤ α)
    (hVolterra : ∀ t ∈ Icc (0 : ℝ) 1,
      Y t = t • (1 : A) - ∫ u in 0..t, (t - u) • (R u * Y u)) :
    ‖Y 1 - (1 : A)‖ ≤ (1 / 4 : ℝ) := by
  have H := (jacobi_volterra_norm_bound R Y hY hα (hsmall.trans (by norm_num)) hR hVolterra).2
    1 (by norm_num)
  simp only [one_smul] at H
  linarith

end Yau.Proofs.C04ChartsAux
