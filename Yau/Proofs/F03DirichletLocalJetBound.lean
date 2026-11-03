import Yau.Proofs.F03DirichletCompactJetBound

/-! One actual local ball supports all finite-word source bounds. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The ball is chosen from actual interior chart geometry, before every
word and source. Each finite word has its own internally proved constant. -/
theorem dirichletClassicalChartHeat_local_jet_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball p δ ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) ∧
      ∀ w : List (Parabolic.Point n), ∃ C : ℝ, 0 < C ∧
        ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ q ∈ Metric.ball p δ,
          |directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w q| ≤ C * ‖f‖ := by
  obtain ⟨O,hO,hpO,hOD,hOc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (dirichletChartInterior_open Ω hΩ a) (Set.singleton_subset_iff.mpr hp.1)
  have hOt : closure O ⊆ chartTarget a := fun z hz => (hOD hz).1
  have hOΩ : chartInv a '' O ⊆ Ω := by
    rintro y ⟨z,hz,rfl⟩
    exact (hOD (subset_closure hz)).2
  have hl : 0 < p.2/2 := half_pos hp.2
  have hpin : p ∈ O ×ˢ Set.Ioo (p.2/2) (p.2+1) :=
    ⟨hpO (Set.mem_singleton _),half_lt_self hp.2,by linarith⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hO.prod isOpen_Ioo) p hpin
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  let K : Set (Parabolic.Point n) := Metric.closedBall p δ
  have hKc : IsCompact K := isCompact_closedBall p δ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have : IsFiniteMeasure (volume.comap ((↑) : K → Parabolic.Point n)) :=
    comap_subtype_isFiniteMeasure_of_measure_lt_top volume K hKc.measurableSet hKc.measure_lt_top
  have hreg : K = closure (interior K) := by
    dsimp only [K]
    rw [interior_closedBall p hδ.ne',closure_ball p hδ.ne']
  have hbuffer : K ⊆ O ×ˢ Set.Ioo (p.2/2) (p.2+1) := by
    intro q hq
    apply hball
    exact (mem_closedBall.mp hq).trans_lt (half_lt_self hε)
  have hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) := by
    intro q hq
    have hq' := hbuffer hq
    exact ⟨⟨(subset_closure.trans hOt) hq'.1,hOΩ ⟨q.1,hq'.1,rfl⟩⟩,hl.trans hq'.2.1⟩
  refine ⟨δ,hδ,ball_subset_closedBall.trans hKQ,?_⟩
  intro w
  obtain ⟨C,hC,hBound⟩ := dirichletClassicalHeat_compact_jet_bound g hK μ hμ Ω hΩ a
    hO hOc hOt hOΩ hl K hKc hreg hbuffer hKQ w
  exact ⟨C,hC,fun f q hq => hBound f q (ball_subset_closedBall hq)⟩

end Yau.Proofs.F03Aux
