import Yau.LeafProofs.L17BootstrapTransportPullback

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {T gamma : ℝ}

theorem translatedPoint_parabolicDistance_le (q : ChartCylinder P T) :
    parabolicDistance q (translatedChartPoint D htheta q) ≤ ‖theta‖ := by
  have h := D.coordinate_displacement_norm_le theta (q.1 : ComplexVector n)
  simpa only [parabolicDistance,translatedChartPoint,sub_self,abs_zero,Real.sqrt_zero,add_zero,
    norm_sub_rev] using h

theorem localPullback_difference_value_bound (hgamma : 0 ≤ gamma)
    (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    ‖localFun F u (translatedLocalPoint D htheta q)-localFun F u q‖ ≤
      ‖u‖*(‖theta‖/P.radius)^gamma := by
  have h := local_difference_bound u q.1 q.2 (translatedChartPoint D htheta q.2)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg u)
  apply Real.rpow_le_rpow
    (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _ hgamma
  exact div_le_div_of_nonneg_right (translatedPoint_parabolicDistance_le D htheta q.2) P.radius_pos.le

include htheta in
theorem theta_norm_le_radius_rpow (hgamma1 : gamma ≤ 1) :
    ‖theta‖ ≤ P.radius*(‖theta‖/P.radius)^gamma := by
  have heps := Real.self_le_rpow_of_le_one (BootstrapPatch.parameter_fraction_nonneg (P := P) theta)
    (D.parameter_fraction_lt_one htheta).le hgamma1
  exact ((div_le_iff₀ P.radius_pos).mp heps).trans_eq (mul_comm _ _)

end Yau.LeafProofs.L17BootstrapTransportAux
