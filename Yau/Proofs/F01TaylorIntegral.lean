import Yau.Proofs.F01IntegralCurrying

/-! Fixed-interval integration preserves a genuine smooth Taylor family.
All derivatives are actual native HasFDerivWithinAt data. Compactness supplies
the local dominating constants, so no desired regularity is an input. -/
open Set Filter MeasureTheory
open scoped ContDiff Interval Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasFTaylorSeriesUpToOn_intervalIntegral
    {U : Set E} (hU : IsOpen U) {f : E → ℝ → F}
    {p : E → ℝ → FormalMultilinearSeries ℝ E F}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFTaylorSeriesUpToOn ∞ (fun x => f x t) (fun x => p x t) U)
    (hc : ∀ m : ℕ, ContinuousOn (fun w : E × ℝ => p w.1 w.2 m) (U ×ˢ Icc 0 1)) :
    HasFTaylorSeriesUpToOn ∞ (fun x => ∫ t in (0 : ℝ)..1, f x t)
      (fun x m => ∫ t in (0 : ℝ)..1, p x t m) U := by
  have hslic (m : ℕ) {x : E} (hx : x ∈ U) :
      ContinuousOn (fun t : ℝ => p x t m) (Icc 0 1) :=
    (hc m).comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx, ht⟩)
  have hint (m : ℕ) {x : E} (hx : x ∈ U) :
      IntervalIntegrable (fun t => p x t m) volume 0 1 :=
    (hslic m hx).intervalIntegrable_of_Icc zero_le_one
  have hder (m : ℕ) {x : E} (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, p y t m)
        ((∫ t in (0 : ℝ)..1, p x t (m + 1)).curryLeft) x := by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let r := ε / 2
    have hr : 0 < r := half_pos hε
    have hclosed : Metric.closedBall x r ⊆ U := by
      intro y hy
      apply hεU
      exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt (by dsimp [r]; linarith))
    have hprod : Metric.closedBall x r ×ˢ Icc (0 : ℝ) 1 ⊆ U ×ˢ Icc 0 1 :=
      Set.prod_mono hclosed Subset.rfl
    obtain ⟨B, hB⟩ := ((isCompact_closedBall x r).prod isCompact_Icc).exists_bound_of_continuousOn ((hc (m + 1)).mono hprod)
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
    have hcurved_meas : AEStronglyMeasurable (fun t : ℝ => (p x t (m + 1)).curryLeft)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      C.continuous.comp_aestronglyMeasurable (hint (m + 1) hx).1.aestronglyMeasurable
    have hraw := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume) (s := Metric.ball x r)
      (F := fun y t => p y t m) (F' := fun y t => (p y t (m + 1)).curryLeft)
      (bound := fun _ => B) (Metric.ball_mem_nhds x hr)
      (by
        filter_upwards [hU.mem_nhds hx] with y hy
        simpa only [uIoc_of_le zero_le_one] using (hint m hy).1.aestronglyMeasurable)
      (hint m hx)
      (by simpa only [uIoc_of_le zero_le_one] using hcurved_meas)
      (by
        exact Filter.Eventually.of_forall fun t ht y hy => by
          rw [uIoc_of_le zero_le_one] at ht
          have hb := hB (y, t) ⟨Metric.closedBall_subset_closedBall le_rfl
            (Metric.ball_subset_closedBall hy), ⟨ht.1.le, ht.2⟩⟩
          rw [norm_curryLeft_eq]
          exact hb)
      intervalIntegrable_const
      (by
        exact Filter.Eventually.of_forall fun t ht y hy => by
          rw [uIoc_of_le zero_le_one] at ht
          exact ((hp t ⟨ht.1.le, ht.2⟩).fderivWithin m
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m) y
            (hclosed (Metric.ball_subset_closedBall hy))).hasFDerivAt
            (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall hy))))
    simpa only [Function.comp_def, intervalIntegral_curryLeft m (hint (m + 1) hx)] using hraw
  constructor
  · intro x hx
    rw [← intervalIntegral_curryZero (hint 0 hx)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hp t (by simpa only [uIcc_of_le zero_le_one] using ht)).zero_eq x hx
  · exact fun m _ x hx => (hder m hx).hasFDerivWithinAt
  · exact fun m _ x hx => (hder m hx).continuousAt.continuousWithinAt

end Yau.NodeProofs.F01Aux
