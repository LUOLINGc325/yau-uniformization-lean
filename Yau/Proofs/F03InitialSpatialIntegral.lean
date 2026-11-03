import Yau.Proofs.F03InitialSpatialWordBounds
import Yau.Proofs.F03SpatialWordIntegral
import Yau.Proofs.F03RegularClosedMeasure

/-! Literal spatial initial jets justify C-infinity of the actual zero-endpoint time integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
namespace Yau.Proofs.F03Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [LocallyCompactSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem initial_spatial_integral_package
    (u : E × ℝ → ℝ) (f : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi 0)) (hf : ContDiffOn ℝ ∞ f O)
    (hu0 : ∀ x,u (x,0)=f x)
    (hInitial : ∀ K : Set E,IsCompact K → K ⊆ O → ∀ m : ℕ,∀ ε : ℝ,0 < ε →
      ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => u (y,t)-f y) x‖ < ε)
    {R : ℝ} (hR : 0 ≤ R) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0:ℝ)..R,u (x,t)) O ∧
      ∀ x ∈ O,∃ D : E →L[ℝ] ℝ,
        HasFDerivAt (fun z => ∫ t in (0:ℝ)..R,u (z,t)) D x ∧
        ∀ v,D v=∫ t in (0:ℝ)..R,fderiv ℝ (fun z => u (z,t)) x v := by
  let μ : Measure (Ioc (0:ℝ) R) := volume.comap Subtype.val
  have hFin : (volume : Measure ℝ) (Ioc 0 R) < ⊤ :=
    (measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  letI : IsFiniteMeasure μ := comap_subtype_isFiniteMeasure_of_measure_lt_top volume
    (Ioc (0:ℝ) R) measurableSet_Ioc hFin
  let F : Ioc (0:ℝ) R → E → ℝ := fun t x => u (x,t.val)
  have hF (t : Ioc (0:ℝ) R) : ContDiffOn ℝ ∞ (F t) O :=
    hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,t.property.1⟩)
  have hWord (w : List E) := joint_spatial_word_contDiffOn u (hO.prod isOpen_Ioi) hu w
  have hMeas (w : List E) (x : E) (hx : x ∈ O) :
      AEStronglyMeasurable (fun t : Ioc (0:ℝ) R => directionalWordDerivative (F t) w x) μ := by
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro t
    have hc : ContinuousAt
        (fun p : E × ℝ => directionalWordDerivative (fun y => u (y,p.2)) w p.1) (x,t.val) :=
      (hWord w).continuousOn.continuousAt ((hO.prod isOpen_Ioi).mem_nhds
        (show (x,t.val) ∈ O ×ˢ Ioi 0 from ⟨hx,t.property.1⟩))
    have hMap : Continuous (fun q : Ioc (0:ℝ) R => (x,q.val)) :=
      continuous_const.prodMk continuous_subtype_val
    exact hc.comp (f := fun q : Ioc (0:ℝ) R => (x,q.val)) hMap.continuousAt
  have hMeasD (w : List E) (x : E) (hx : x ∈ O) :
      AEStronglyMeasurable (fun t : Ioc (0:ℝ) R => fderiv ℝ (directionalWordDerivative (F t) w) x) μ := by
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro t
    have hh := joint_spatial_fderiv_contDiffAt (m := ∞) (p := (x,t.val))
      ((hWord w).contDiffAt ((hO.prod isOpen_Ioi).mem_nhds
        (show (x,t.val) ∈ O ×ˢ Ioi 0 from ⟨hx,t.property.1⟩)))
    have hMap : Continuous (fun q : Ioc (0:ℝ) R => (x,q.val)) :=
      continuous_const.prodMk continuous_subtype_val
    exact hh.continuousAt.comp (f := fun q : Ioc (0:ℝ) R => (x,q.val)) hMap.continuousAt
  have hLocal (x : E) (hx : x ∈ O) : ∃ r : ℝ,0 < r ∧ Metric.ball x r ⊆ O ∧
      ∀ w : List E,∃ C : ℝ,∀ t : Ioc (0:ℝ) R,∀ z ∈ Metric.ball x r,
        |directionalWordDerivative (F t) w z| ≤ C := by
    obtain ⟨V,hV,hxV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO
      (singleton_subset_iff.mpr hx)
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hV x (hxV (mem_singleton _))
    refine ⟨r,hr,fun z hz => hVO (subset_closure (hBall hz)),fun w => ?_⟩
    obtain ⟨C,_hC,hC⟩ := compact_spatial_word_bound_through_initial u f hO hu hf hu0 hInitial
      (closure V) hVc hVO R w
    exact ⟨C,fun t z hz => hC t.val ⟨t.property.1.le,t.property.2⟩ z (subset_closure (hBall hz))⟩
  have hSmooth := spatialWordIntegral_contDiffOn μ F hO hF hMeas hMeasD hLocal []
  have hEq (w : List E) : spatialWordIntegral μ F w=
      (fun x => ∫ t in (0:ℝ)..R,directionalWordDerivative (fun y => u (y,t)) w x) := by
    funext x
    dsimp only [spatialWordIntegral,F,μ]
    rw [intervalIntegral.integral_of_le hR]
    exact integral_subtype_comap measurableSet_Ioc
      (fun t : ℝ => directionalWordDerivative (fun y => u (y,t)) w x)
  constructor
  · simpa only [hEq [],directionalWordDerivative] using hSmooth
  · intro x hx
    obtain ⟨D,hD,hEval⟩ := spatialWordIntegral_hasFDerivAt μ F hO hF hMeas hMeasD hLocal [] hx
    refine ⟨D,?_,fun v => ?_⟩
    · simpa only [hEq [],directionalWordDerivative] using hD
    · simpa only [hEq (v::[]),directionalWordDerivative] using hEval v

theorem initial_spatial_integral_contDiffOn
    (u : E × ℝ → ℝ) (f : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi 0)) (hf : ContDiffOn ℝ ∞ f O)
    (hu0 : ∀ x,u (x,0)=f x)
    (hInitial : ∀ K : Set E,IsCompact K → K ⊆ O → ∀ m : ℕ,∀ ε : ℝ,0 < ε →
      ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => u (y,t)-f y) x‖ < ε)
    {R : ℝ} (hR : 0 ≤ R) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0:ℝ)..R,u (x,t)) O :=
  (initial_spatial_integral_package u f hO hu hf hu0 hInitial hR).1

end Yau.Proofs.F03Aux
