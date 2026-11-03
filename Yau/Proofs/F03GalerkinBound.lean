import Yau.Proofs.F03ExhaustionResolvent

/-! Explicit scalar coercivity bounds avoid any change of operator topology. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem coercive_real_error_bound {x y α C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hα : 0 < α) (hC : 0 ≤ C) (h : α*x^2 ≤ C*x*y) : x ≤ C/α*y := by
  by_cases hz : x=0
  · rw [hz]
    exact mul_nonneg (div_nonneg hC hα.le) hy
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hcancel : α*x ≤ C*y := (mul_le_mul_iff_right₀ hxp).mp (by nlinarith only [h])
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hcancel)

theorem scalarResolventForm_explicit_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : ℝ)
    (u v : ScalarEnergySpace g μ hμ) :
    |scalarResolventForm g μ hμ h u v| ≤ (|h|+|1-h|)*‖u‖*‖v‖ := by
  have heq : scalarResolventForm g μ hμ h u v=
      h*inner ℝ u v+(1-h)*inner ℝ (scalarEnergyL2 g μ hμ u) (scalarEnergyL2 g μ hμ v) := by
    rw [scalarResolventForm_apply,scalarClosedEnergy]
    ring
  have hu := scalarEnergyL2_norm_le g μ hμ u
  have hv := scalarEnergyL2_norm_le g μ hμ v
  have hJ : |inner ℝ (scalarEnergyL2 g μ hμ u) (scalarEnergyL2 g μ hμ v)| ≤ ‖u‖*‖v‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hu hv (norm_nonneg _) (norm_nonneg _))
  rw [heq]
  calc
    _ ≤ |h*inner ℝ u v|+|(1-h)*inner ℝ (scalarEnergyL2 g μ hμ u) (scalarEnergyL2 g μ hμ v)| :=
      abs_add_le _ _
    _ ≤ |h| *(‖u‖*‖v‖)+|1-h| *(‖u‖*‖v‖) := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hJ (abs_nonneg _))
    _ = _ := by ring

end Yau.Proofs.F03Aux
