import Yau.LeafProofs.L21WeightedDomainsCutoffLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

/-- One diagonal of the actual cutoff/Friedrichs families is a genuine
common compact core for the entire finite row system. -/
theorem weightedDomains_graph_core {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (v : ι → X n)
    (a p : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (hFactor : ∀ r c i x, a r c i x = (rho x : ℂ)*p r c i x)
    (hp : ∀ r c i, ContinuousOn (p r c i) (Metric.ball 0 1))
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ r c i x, x ∈ Metric.ball (0 : X n) 1 → ‖p r c i x‖ ≤ C)
    (u : X n → α → ℂ) (w : X n → β → ℂ)
    (hu : ∀ c, MemLp (fun x => u x c) 2 (weightedBallMeasure n K))
    (hw : ∀ r, MemLp (fun x => w x r) 2 (weightedBallMeasure n K))
    (hRow : ∀ r (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 1 →
      (∫ x, (ψ x : ℂ)*w x r ∂Yau.lebesgueC n) =
        ∫ x, ∑ c, u x c*Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow v a b r c ψ x ∂Yau.lebesgueC n) :
    ∃ U : ℕ → α → CompactTest (Metric.ball (0 : X n) 1),
      (∀ c, (∀ m, MemLp (fun x => U m c x-u x c) 2 (weightedBallMeasure n K)) ∧
        Tendsto (fun m => ∫ x, ‖U m c x-u x c‖^2 ∂weightedBallMeasure n K) atTop (𝓝 0)) ∧
      ∀ r, (∀ m, MemLp (fun x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b
          (fun y c => U m c y) x r-w x r) 2 (weightedBallMeasure n K)) ∧
        Tendsto (fun m => ∫ x, ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b
          (fun y c => U m c y) x r-w x r‖^2 ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  classical
  choose L V hL hLB hSmooth hInput hOutput using
    (fun m => weightedDomains_cutoff_graph_approx K hK v a b ha hb u w hu hw hRow m)
  let ε : ℕ → ℝ := fun m => 1/((m : ℝ)+1)
  have hε (m : ℕ) : 0 < ε m := by dsimp only [ε]; positivity
  have hεLim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hThreshold (m : ℕ) : ∃ j : ℕ,
      (∀ c, (∫ x, ‖V m j x c-(boundaryCutoff m x : ℂ)*u x c‖^2 ∂weightedBallMeasure n K) < ε m) ∧
      ∀ r, (∫ x, ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (V m j) x r-
        Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r‖^2
          ∂weightedBallMeasure n K) < ε m := by
    have hIn : ∀ᶠ j in atTop, ∀ c,
        (∫ x, ‖V m j x c-(boundaryCutoff m x : ℂ)*u x c‖^2 ∂weightedBallMeasure n K) < ε m :=
      Filter.eventually_all.mpr (fun c => (hInput m c).2.eventually (gt_mem_nhds (hε m)))
    have hOut : ∀ᶠ j in atTop, ∀ r,
        (∫ x, ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (V m j) x r-
          Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r‖^2
            ∂weightedBallMeasure n K) < ε m :=
      Filter.eventually_all.mpr (fun r => (hOutput m r).2.eventually (gt_mem_nhds (hε m)))
    exact (hIn.and hOut).exists
  choose N hNInput hNOutput using hThreshold
  let U : ℕ → α → CompactTest (Metric.ball (0 : X n) 1) := fun m c =>
    ⟨fun x => V m (N m) x c,(hSmooth m (N m) c).1,
      (hL m).of_isClosed_subset (isClosed_tsupport _) (hSmooth m (N m) c).2,
      ((hSmooth m (N m) c).2).trans (hLB m)⟩
  refine ⟨U,?_,?_⟩
  · intro c
    have hMoll : Tendsto (fun m => ∫ x, ‖U m c x-(boundaryCutoff m x : ℂ)*u x c‖^2
        ∂weightedBallMeasure n K) atTop (𝓝 0) :=
      squeeze_zero (fun m => integral_nonneg (fun x => sq_nonneg _))
        (fun m => (hNInput m c).le) hεLim
    have hCut := weightedBoundaryCutoff_error_tendsto K (hu c)
    have hAdd := weightedDomains_L2_add_error_tendsto (weightedBallMeasure n K)
      (fun m x => U m c x-(boundaryCutoff m x : ℂ)*u x c)
      (fun m x => (boundaryCutoff m x : ℂ)*u x c-u x c)
      (fun m => (hInput m c).1 (N m)) hCut.1 hMoll hCut.2
    simpa only [sub_add_sub_cancel] using hAdd
  · intro r
    have hMoll : Tendsto (fun m => ∫ x,
        ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (fun y c => U m c y) x r-
          Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r‖^2
            ∂weightedBallMeasure n K) atTop (𝓝 0) :=
      squeeze_zero (fun m => integral_nonneg (fun x => sq_nonneg _))
        (fun m => (hNOutput m r).le) hεLim
    have hCut := weightedDomains_cutoff_output_tendsto K hK v a p hFactor hp hC hBound u w hu hw r
    have hAdd := weightedDomains_L2_add_error_tendsto (weightedBallMeasure n K)
      (fun m x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (fun y c => U m c y) x r-
        Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r)
      (fun m x => Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r-w x r)
      (fun m => (hOutput m r).1 (N m)) hCut.1 hMoll hCut.2
    simpa only [sub_add_sub_cancel] using hAdd

end Yau.LeafProofs.L21Aux
