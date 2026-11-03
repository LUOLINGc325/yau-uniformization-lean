import Yau.Proofs.B01Complete
import Yau.Proofs.B01Distance

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1}

theorem cuspExhaustion_lipschitz (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (x y : M.Carrier) :
    |cuspExhaustion c x - cuspExhaustion c y| ≤ inducedDistance (cuspDiscField c hc) x y :=
  inducedDistance_function_bound (cuspDiscField c hc) (cuspDiscField_smooth c hc)
    (cuspExhaustion c) (cuspExhaustion_smooth c hc) (cuspExhaustion_mfderiv_bound c hc) x y

theorem cusp_closedBall_isCompact (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (x : M.Carrier) (R : ℝ) :
    letI := LeafProofs.L23Aux.metricSpaceOfField (cuspDiscField c hc) (cuspDiscField_smooth c hc)
    IsCompact (Metric.closedBall x R) := by
  letI := LeafProofs.L23Aux.metricSpaceOfField (cuspDiscField c hc) (cuspDiscField_smooth c hc)
  let A : ℝ := cuspExhaustion c x - R
  let B : ℝ := cuspExhaustion c x + R
  let K : Set ℂ := Metric.closedBall 0 (Real.exp (-Real.exp A)) ∩
    {z | Real.exp (-Real.exp B) ≤ ‖z‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hKD : K ⊆ puncturedUnitDisc := by
    intro z hz
    have hu : ‖z‖ ≤ Real.exp (-Real.exp A) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact ⟨(Real.exp_pos _).trans_le hz.2,
      hu.trans_lt (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos A)))⟩
  have hI : IsCompact (c.symm '' K) :=
    hK.image_of_continuousOn ((hc.2.1 ▸ c.continuousOn_symm).mono hKD)
  apply hI.of_isClosed_subset Metric.isClosed_closedBall
  intro y hy
  have hd : inducedDistance (cuspDiscField c hc) x y ≤ R := by
    change inducedDistance (cuspDiscField c hc) y x ≤ R at hy
    rwa [LeafProofs.L23Aux.inducedDistance_symm (cuspDiscField c hc) (cuspDiscField_smooth c hc) y x] at hy
  have hb := (cuspExhaustion_lipschitz c hc x y).trans hd
  rw [abs_sub_comm] at hb
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  have ha : A ≤ cuspExhaustionScalar (c y) := by
    change cuspExhaustion c x - R ≤ cuspExhaustion c y
    linarith
  have hb' : cuspExhaustionScalar (c y) ≤ B := by
    change cuspExhaustion c y ≤ cuspExhaustion c x + R
    linarith
  have hrad := cuspExhaustionScalar_annulus (disc_mem c hc y) A B ha hb'
  refine ⟨c y, ⟨?_, hrad.1⟩, disc_left_inv c hc y⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hrad.2

theorem cusp_complete_distance (c : DiscCoordinate M) (hc : IsDiscCoordinate c) :
    IsCompleteDistance (inducedDistance (cuspDiscField c hc)) := by
  letI := LeafProofs.L23Aux.metricSpaceOfField (cuspDiscField c hc) (cuspDiscField_smooth c hc)
  letI : ProperSpace M.Carrier := ⟨cusp_closedBall_isCompact c hc⟩
  intro s hs
  have hcs : CauchySeq s := Metric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    exact ⟨N, fun m hm k hk => hN m k hm hk⟩)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  exact ⟨x, Metric.tendsto_atTop.mp hx⟩

theorem completeDiscMetricRealization : CompleteDiscMetricRealization := by
  intro M c hc
  let h := cuspDiscField c hc
  have hh : MetricSmooth h := cuspDiscField_smooth c hc
  letI := LeafProofs.L23Aux.metricSpaceOfField h hh
  let g : Yau.SmoothMetric M :=
    { form := h
      coordinate_smooth := discPullbackMetric_coordinate_smooth c hc _ _ completeDiscDensity_contDiffOn
      curve_nonempty := fun x y => by
        obtain ⟨γ⟩ := LeafProofs.L23Aux.integrable_curve_nonempty h hh x y
        exact ⟨γ.1⟩
      integrable_curve_nonempty := LeafProofs.L23Aux.integrable_curve_nonempty h hh
      chart_transition := hermitianField_chartTransition h
      induced_distance_nonneg := LeafProofs.L23Aux.inducedDistance_nonneg h hh
      induced_distance_eq_zero := by
        intro x y
        exact (dist_eq_zero : dist x y = 0 ↔ x = y)
      induced_distance_symm := LeafProofs.L23Aux.inducedDistance_symm h hh
      induced_distance_triangle := LeafProofs.L23Aux.inducedDistance_triangle h hh
      induced_distance_topology := by
        intro x s
        constructor
        · intro hs
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance h y x < ε
          rwa [LeafProofs.L23Aux.inducedDistance_symm h hh y x]
        · rintro ⟨ε, hε, hball⟩
          apply Metric.mem_nhds_iff.mpr
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance h x y < ε
          change inducedDistance h y x < ε at hy
          rwa [LeafProofs.L23Aux.inducedDistance_symm h hh y x] at hy
      complete_distance := cusp_complete_distance c hc
      kahler_equations := hermitianField_kahler_one h }
  refine ⟨g, discPullbackMeasure c completeDiscDensity, ?_, ?_⟩
  · exact discPullbackMetric_volume c hc completeDiscDensity (fun _ hz => completeDiscDensity_pos hz)
  · intro x u v
    rfl

end Yau.Proofs.B01Aux
