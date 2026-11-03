import Yau.LeafProofs.L17BootstrapPatchBasic

open Set Metric Filter
open scoped Topology ContDiff Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapPatchAux
open L17Aux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
namespace BootstrapPatch
variable (D : BootstrapPatch P x)

def forward (θ : ComplexVector n) (y : M.Carrier) : M.Carrier :=
  if y ∈ (P.charts.chart D.center).target then
    P.charts.chart D.center (cutoffTranslation D.bump θ ((P.charts.chart D.center).symm y)) else y

def inverse (θ : ComplexVector n) (y : M.Carrier) : M.Carrier :=
  if y ∈ (P.charts.chart D.center).target then P.charts.chart D.center
    (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one) D.derivative_bound θ
      ((P.charts.chart D.center).symm y)) else y

theorem forward_of_mem_target (θ : ComplexVector n) {y : M.Carrier}
    (hy : y ∈ (P.charts.chart D.center).target) :
    D.forward θ y=P.charts.chart D.center
      (cutoffTranslation D.bump θ ((P.charts.chart D.center).symm y)) := ite_eq_left hy

theorem inverse_of_mem_target (θ : ComplexVector n) {y : M.Carrier}
    (hy : y ∈ (P.charts.chart D.center).target) :
    D.inverse θ y=P.charts.chart D.center
      (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one) D.derivative_bound θ
        ((P.charts.chart D.center).symm y)) := ite_eq_left hy

theorem coordinate_bump_zero_of_not_mem_support {y : M.Carrier}
    (hy : y ∈ (P.charts.chart D.center).target) (hK : y ∉ D.supportSet) :
    D.bump ((P.charts.chart D.center).symm y)=0 := by
  by_contra hn
  exact hK ⟨(P.charts.chart D.center).symm y,subset_closure hn,(P.charts.chart D.center).right_inv hy⟩

theorem forward_eq_self_of_not_mem_support (θ : ComplexVector n) {y : M.Carrier}
    (hy : y ∉ D.supportSet) : D.forward θ y=y := by
  by_cases ht : y ∈ (P.charts.chart D.center).target
  · rw [D.forward_of_mem_target θ ht,cutoffTranslation_fixed_of_zero D.bump θ
      (D.coordinate_bump_zero_of_not_mem_support ht hy),(P.charts.chart D.center).right_inv ht]
  · exact ite_eq_right ht

theorem inverse_eq_self_of_not_mem_support {θ : ComplexVector n} (hθ : ‖θ‖<D.smallRadius)
    {y : M.Carrier} (hy : y ∉ D.supportSet) : D.inverse θ y=y := by
  have hSmall := hθ.trans_le D.smallRadius_le_translation
  by_cases ht : y ∈ (P.charts.chart D.center).target
  · rw [D.inverse_of_mem_target θ ht,
      cutoffInverse_fixed_of_zero D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
        D.derivative_bound hSmall (D.coordinate_bump_zero_of_not_mem_support ht hy),
      (P.charts.chart D.center).right_inv ht]
  · exact ite_eq_right ht

theorem coordinate_forward_mem_source {θ z : ComplexVector n} (hθ : ‖θ‖<D.smallRadius)
    (hz : z ∈ (P.charts.chart D.center).source) :
    cutoffTranslation D.bump θ z ∈ (P.charts.chart D.center).source :=
  cutoffTranslation_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) (P.charts.chart D.center).source
      (fun _ hz => D.bump_zero_outside_source hz) hz

theorem coordinate_inverse_mem_source {θ z : ComplexVector n} (hθ : ‖θ‖<D.smallRadius)
    (hz : z ∈ (P.charts.chart D.center).source) :
    cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one) D.derivative_bound θ z ∈
      (P.charts.chart D.center).source :=
  cutoffInverse_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) (P.charts.chart D.center).source
      (fun _ hz => D.bump_zero_outside_source hz) hz

theorem inverse_forward {θ : ComplexVector n} (hθ : ‖θ‖<D.smallRadius) (y : M.Carrier) :
    D.inverse θ (D.forward θ y)=y := by
  let e := P.charts.chart D.center
  have hSmall := hθ.trans_le D.smallRadius_le_translation
  by_cases hy : y ∈ e.target
  · have hz := e.symm.map_source hy
    have hF := D.coordinate_forward_mem_source hθ hz
    rw [D.forward_of_mem_target θ hy,D.inverse_of_mem_target θ (e.map_source hF),e.left_inv hF,
      cutoffInverse_translation D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
        D.derivative_bound hSmall,e.right_inv hy]
  · change D.inverse θ (if y ∈ e.target then _ else y)=y
    rw [ite_eq_right hy]
    exact ite_eq_right hy

theorem forward_inverse {θ : ComplexVector n} (hθ : ‖θ‖<D.smallRadius) (y : M.Carrier) :
    D.forward θ (D.inverse θ y)=y := by
  let e := P.charts.chart D.center
  have hSmall := hθ.trans_le D.smallRadius_le_translation
  by_cases hy : y ∈ e.target
  · have hz := e.symm.map_source hy
    have hF := D.coordinate_inverse_mem_source hθ hz
    rw [D.inverse_of_mem_target θ hy,D.forward_of_mem_target θ (e.map_source hF),e.left_inv hF,
      cutoffTranslation_inverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
        D.derivative_bound hSmall,e.right_inv hy]
  · change D.forward θ (if y ∈ e.target then _ else y)=y
    rw [ite_eq_right hy]
    exact ite_eq_right hy

theorem forward_continuous {θ : ComplexVector n} (hθ : ‖θ‖<D.smallRadius) : Continuous (D.forward θ) := by
  let e := P.charts.chart D.center
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ e.target
  · have hz := e.symm.map_source hy
    have hF := D.coordinate_forward_mem_source hθ hz
    have hc : ContinuousAt (fun y => e (cutoffTranslation D.bump θ (e.symm y))) y :=
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hF)).comp
        (f := fun y : M.Carrier => cutoffTranslation D.bump θ (e.symm y))
        ((cutoffTranslation_contDiff D.bump_smooth θ).continuous.continuousAt.comp
          (f := fun y : M.Carrier => e.symm y)
          (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hy)))
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact D.forward_of_mem_target θ hz
  · have hK : y ∉ D.supportSet := fun h => hy (D.supportSet_subset_target h)
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [D.supportSet_isCompact.isClosed.isOpen_compl.mem_nhds hK] with z hz
    exact D.forward_eq_self_of_not_mem_support θ hz

theorem inverse_continuous {θ : ComplexVector n} (hθ : ‖θ‖<D.smallRadius) : Continuous (D.inverse θ) := by
  let e := P.charts.chart D.center
  let H := cutoffTranslationHomeomorph D.bump D.bump_smooth D.bound
    (zero_le_one.trans D.bound_ge_one) D.derivative_bound θ (hθ.trans_le D.smallRadius_le_translation)
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ e.target
  · have hz := e.symm.map_source hy
    have hF := D.coordinate_inverse_mem_source hθ hz
    have hc : ContinuousAt (fun y => e (H.symm (e.symm y))) y :=
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hF)).comp
        (f := fun y : M.Carrier => H.symm (e.symm y))
        (H.symm.continuous.continuousAt.comp
          (f := fun y : M.Carrier => e.symm y)
          (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hy)))
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact D.inverse_of_mem_target θ hz
  · have hK : y ∉ D.supportSet := fun h => hy (D.supportSet_subset_target h)
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [D.supportSet_isCompact.isClosed.isOpen_compl.mem_nhds hK] with z hz
    exact D.inverse_eq_self_of_not_mem_support hθ hz

def homeomorph (θ : ComplexVector n) (hθ : ‖θ‖<D.smallRadius) : M.Carrier ≃ₜ M.Carrier where
  toFun := D.forward θ
  invFun := D.inverse θ
  left_inv := D.inverse_forward hθ
  right_inv := D.forward_inverse hθ
  continuous_toFun := D.forward_continuous hθ
  continuous_invFun := D.inverse_continuous hθ

theorem forward_chart (θ : ComplexVector n) {z : ComplexVector n}
    (hz : z ∈ (P.charts.chart D.center).source) :
    D.forward θ (P.charts.chart D.center z)=P.charts.chart D.center (cutoffTranslation D.bump θ z) := by
  rw [D.forward_of_mem_target θ ((P.charts.chart D.center).map_source hz),
    (P.charts.chart D.center).left_inv hz]

theorem inverse_chart (θ : ComplexVector n) {z : ComplexVector n}
    (hz : z  ∈  (P.charts.chart D.center).source) :
    D.inverse θ (P.charts.chart D.center z)=P.charts.chart D.center
      (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
        D.derivative_bound θ z) := by
  rw [D.inverse_of_mem_target θ ((P.charts.chart D.center).map_source hz),
    (P.charts.chart D.center).left_inv hz]

theorem forward_zero_parameter (y : M.Carrier) : D.forward 0 y=y := by
  by_cases hy : y  ∈  (P.charts.chart D.center).target
  · rw [D.forward_of_mem_target 0 hy,cutoffTranslation_zero_parameter,
      (P.charts.chart D.center).right_inv hy]
  · exact ite_eq_right hy

theorem inverse_zero_parameter (y : M.Carrier) : D.inverse 0 y=y := by
  have hθ : ‖(0 : ComplexVector n)‖ < D.smallRadius := by simpa using D.smallRadius_pos
  have h := D.inverse_forward hθ y
  rw [D.forward_zero_parameter] at h
  exact h

theorem forward_supportSet_mapsTo {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    MapsTo (D.forward θ) D.supportSet D.supportSet := by
  rintro y ⟨z,hz,rfl⟩
  rw [D.forward_chart θ (D.bump_support_source hz)]
  refine ⟨cutoffTranslation D.bump θ z,?_,rfl⟩
  exact cutoffTranslation_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) (tsupport D.bump)
      (fun w hw => by by_contra hn;exact hw (subset_closure hn)) hz

theorem inverse_supportSet_mapsTo {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius) :
    MapsTo (D.inverse θ) D.supportSet D.supportSet := by
  rintro y ⟨z,hz,rfl⟩
  rw [D.inverse_chart θ (D.bump_support_source hz)]
  refine ⟨cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
      D.derivative_bound θ z,?_,rfl⟩
  exact cutoffInverse_mapsTo D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound (hθ.trans_le D.smallRadius_le_translation) (tsupport D.bump)
      (fun w hw => by by_contra hn;exact hw (subset_closure hn)) hz

theorem forward_center_translation (θ : ComplexVector n) :
    D.forward θ x=P.charts.chart D.center (D.coord+θ) := by
  have hz := D.bump_support_source (show D.coord ∈ tsupport D.bump from by
    apply subset_closure
    change D.bump D.coord≠0
    rw [D.bump_one D.coord (mem_closedBall_self D.radius_pos.le)]
    norm_num)
  calc
    D.forward θ x=D.forward θ (P.charts.chart D.center D.coord) :=
      congrArg (D.forward θ) D.center_eq.symm
    _=P.charts.chart D.center (cutoffTranslation D.bump θ D.coord) := D.forward_chart θ hz
    _=P.charts.chart D.center (D.coord+θ) := by
      rw [cutoffTranslation_of_one D.bump θ (D.bump_one D.coord (mem_closedBall_self D.radius_pos.le))]

end BootstrapPatch
end Yau.LeafProofs.L17BootstrapPatchAux
