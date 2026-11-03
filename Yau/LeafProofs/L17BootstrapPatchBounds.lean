import Yau.LeafProofs.L17BootstrapPatchBasic

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapPatchAux
open L17Aux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
namespace BootstrapPatch
variable (D : BootstrapPatch P x)

theorem coordinate_mapsTo {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (S : Set (ComplexVector n)) (hS : tsupport D.bump ⊆ S) :
    MapsTo (cutoffTranslation D.bump θ) S S :=
  cutoffTranslation_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) S (by
      intro z hz
      by_contra hn
      exact hz (hS (subset_closure hn)))

theorem coordinate_inverse_mapsTo {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (S : Set (ComplexVector n)) (hS : tsupport D.bump ⊆ S) :
    MapsTo (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
      D.derivative_bound θ) S S :=
  cutoffInverse_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) S (by
      intro z hz
      by_contra hn
      exact hz (hS (subset_closure hn)))

theorem bump_support_ball_quarter : tsupport D.bump ⊆ ball (0 : ComplexVector n) (P.radius/4) :=
  D.bump_support.trans ((closedBall_subset_closedBall
    (by linarith [D.radius_pos] : 2*D.radius ≤ 3*D.radius)).trans D.collar_mem)

theorem coordinate_mapsTo_ball_quarter {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    MapsTo (cutoffTranslation D.bump θ) (ball (0 : ComplexVector n) (P.radius/4))
      (ball (0 : ComplexVector n) (P.radius/4)) :=
  D.coordinate_mapsTo hθ _ D.bump_support_ball_quarter

theorem coordinate_mapsTo_ball {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    MapsTo (cutoffTranslation D.bump θ) (ball (0 : ComplexVector n) P.radius)
      (ball (0 : ComplexVector n) P.radius) :=
  D.coordinate_mapsTo hθ _ (D.bump_support_ball_quarter.trans
    (ball_subset_ball (by linarith [P.radius_pos])))

theorem coordinate_inverse_mapsTo_ball {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    MapsTo (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
      D.derivative_bound θ) (ball (0 : ComplexVector n) P.radius)
      (ball (0 : ComplexVector n) P.radius) :=
  D.coordinate_inverse_mapsTo hθ _ (D.bump_support_ball_quarter.trans
    (ball_subset_ball (by linarith [P.radius_pos])))

theorem coordinate_displacement_norm_le (θ z : ComplexVector n) :
    ‖cutoffTranslation D.bump θ z-z‖ ≤ ‖θ‖ := by
  simp only [cutoffTranslation,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (D.bump_range z).1]
  exact (mul_le_mul_of_nonneg_right (D.bump_range z).2 (norm_nonneg θ)).trans_eq (one_mul _)

theorem coordinate_sub_norm_le {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (z w : ComplexVector n) :
    ‖cutoffTranslation D.bump θ z-cutoffTranslation D.bump θ w‖ ≤ 2*‖z-w‖ := by
  have hL := smallTranslation_parameter_bound (zero_le_one.trans D.bound_ge_one)
    (hθ.trans_le D.smallRadius_le_translation)
  have hEq : cutoffTranslation D.bump θ z-cutoffTranslation D.bump θ w=
      (z-w)+(D.bump z-D.bump w) • θ := by
    simp only [cutoffTranslation,sub_smul]
    abel
  rw [hEq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs]
  have hB := mul_le_mul_of_nonneg_right
    (cutoff_lipschitz D.bump_smooth D.derivative_bound z w) (norm_nonneg θ)
  nlinarith [norm_nonneg (z-w)]

theorem bump_hessian_norm_le (z : ComplexVector n) :
    ‖fderiv ℝ (fderiv ℝ D.bump) z‖ ≤ D.bound := by
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact D.low_jet_bound 2 (by omega) z

theorem bump_gradient_sub_norm_le (z w : ComplexVector n) :
    ‖fderiv ℝ D.bump z-fderiv ℝ D.bump w‖ ≤ D.bound*‖z-w‖ := by
  have hDfSmooth : ContDiff ℝ ∞ (fderiv ℝ D.bump) := D.bump_smooth.fderiv_right (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ (univ : Set (ComplexVector n))) =>
      (hDfSmooth.differentiable (by simp)) y)
    (fun y (_ : y ∈ (univ : Set (ComplexVector n))) => D.bump_hessian_norm_le y)
    convex_univ (mem_univ w) (mem_univ z)

theorem bump_hessian_sub_norm_le (z w : ComplexVector n) :
    ‖fderiv ℝ (fderiv ℝ D.bump) z-fderiv ℝ (fderiv ℝ D.bump) w‖ ≤ D.bound*‖z-w‖ := by
  have hDfSmooth : ContDiff ℝ ∞ (fderiv ℝ D.bump) := D.bump_smooth.fderiv_right (by simp)
  have hD2Smooth : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ D.bump)) := hDfSmooth.fderiv_right (by simp)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ (univ : Set (ComplexVector n))) =>
      (hD2Smooth.differentiable (by simp)) y)
    (fun y (_ : y ∈ (univ : Set (ComplexVector n))) => ?_)
    convex_univ (mem_univ w) (mem_univ z)
  rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
  exact D.low_jet_bound 3 (by omega) y

theorem coordinate_fderiv_norm_le {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (z : ComplexVector n) : ‖fderiv ℝ (cutoffTranslation D.bump θ) z‖ ≤ 2 := by
  rw [cutoffTranslation_fderiv D.bump_smooth θ z]
  apply (norm_add_le _ _).trans
  have hId := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ComplexVector n)
  have hErr := cutoffTranslation_error_norm_lt (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) z
  linarith

theorem coordinate_fderiv_error_norm_le (θ z : ComplexVector n) :
    ‖fderiv ℝ (cutoffTranslation D.bump θ) z-ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤
      D.bound*‖θ‖ := by
  rw [cutoffTranslation_fderiv D.bump_smooth θ z]
  simp only [cutoffTranslationJacobian,add_sub_cancel_left,ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_right (D.derivative_bound z) (norm_nonneg θ)

theorem coordinate_eq_id_near_of_not_mem_support (θ : ComplexVector n)
    {z : ComplexVector n} (hz : z ∉ tsupport D.bump) :
    cutoffTranslation D.bump θ =ᶠ[𝓝 z] id := by
  filter_upwards [(isClosed_tsupport D.bump).isOpen_compl.mem_nhds hz] with w hw
  have hχ : D.bump w=0 := by
    by_contra h
    exact hw (subset_closure h)
  exact cutoffTranslation_fixed_of_zero D.bump θ hχ

theorem coordinate_fderiv_eq_id_of_not_mem_support (θ : ComplexVector n)
    {z : ComplexVector n} (hz : z ∉ tsupport D.bump) :
    fderiv ℝ (cutoffTranslation D.bump θ) z=ContinuousLinearMap.id ℝ (ComplexVector n) := by
  have h := (D.coordinate_eq_id_near_of_not_mem_support θ hz).fderiv_eq (𝕜 := ℝ)
  simpa only [fderiv_id] using h

theorem coordinate_second_fderiv_eq_zero_of_not_mem_support (θ : ComplexVector n)
    {z : ComplexVector n} (hz : z ∉ tsupport D.bump) :
    fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) z=0 := by
  have h := ((D.coordinate_eq_id_near_of_not_mem_support θ hz).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hId : fderiv ℝ (id : ComplexVector n → ComplexVector n)=
      fun _ => ContinuousLinearMap.id ℝ (ComplexVector n) := funext (fun _ => fderiv_id)
  rw [hId,fderiv_const_apply] at h
  exact h

def scalarFormLift (θ : ComplexVector n) :
    (ComplexVector n →L[ℝ] ℝ) →L[ℝ] (ComplexVector n →L[ℝ] ComplexVector n) :=
  (ContinuousLinearMap.smulRightL ℝ (ComplexVector n) (ComplexVector n)).flip θ

theorem scalarFormLift_norm_le (θ : ComplexVector n) : ‖scalarFormLift θ‖ ≤ ‖θ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg θ)
  intro L
  change ‖L.smulRight θ‖ ≤ ‖θ‖*‖L‖
  rw [ContinuousLinearMap.norm_smulRight_apply,mul_comm]

theorem coordinate_second_fderiv_eq (θ z : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) z=
      (scalarFormLift θ).comp (fderiv ℝ (fderiv ℝ D.bump) z) := by
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  exact cutoffTranslation_second_derivative D.bump_smooth θ z a b

theorem coordinate_second_fderiv_norm_le (θ z : ComplexVector n) :
    ‖fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) z‖ ≤ D.bound*‖θ‖ := by
  rw [D.coordinate_second_fderiv_eq]
  apply ((scalarFormLift θ).opNorm_comp_le _).trans
  exact (mul_le_mul (scalarFormLift_norm_le θ) (D.bump_hessian_norm_le z)
    (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg θ)).trans_eq (mul_comm _ _)

theorem coordinate_second_fderiv_sub_norm_le (θ z w : ComplexVector n) :
    ‖fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) z-
      fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) w‖ ≤ D.bound*‖θ‖*‖z-w‖ := by
  rw [D.coordinate_second_fderiv_eq,D.coordinate_second_fderiv_eq]
  rw [←ContinuousLinearMap.comp_sub]
  apply ((scalarFormLift θ).opNorm_comp_le _).trans
  exact (mul_le_mul (scalarFormLift_norm_le θ) (D.bump_hessian_sub_norm_le z w)
    (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg θ)).trans_eq (by ring)

theorem parameter_fraction_nonneg (θ : ComplexVector n) : 0 ≤ ‖θ‖/P.radius :=
  div_nonneg (norm_nonneg θ) P.radius_pos.le

theorem parameter_fraction_lt_one {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    ‖θ‖/P.radius < 1 :=
  (div_lt_one P.radius_pos).mpr (hθ.trans_le D.smallRadius_le_radius)

end BootstrapPatch
end Yau.LeafProofs.L17BootstrapPatchAux
