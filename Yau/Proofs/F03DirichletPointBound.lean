import Yau.Proofs.F03DirichletCompactBound

/-! Actual bounded point evaluation, with its constant before every source. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Every positive interior evaluation has a genuine finite source bound,
constructed from an actual buffered compact ball and its proved closed graph. -/
theorem dirichletClassicalHeat_point_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      |dirichletClassicalHeat g hK μ hμ Ω hΩ f x t| ≤ C * ‖f‖ := by
  have hinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hIn : chartPt x x ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} :=
    ⟨mem_extChartAt_target x,by rwa [hinv]⟩
  obtain ⟨O,hO,hxO,hOD,hOc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (dirichletChartInterior_open Ω hΩ x) (Set.singleton_subset_iff.mpr hIn)
  have hOt : closure O ⊆ chartTarget x := fun z hz => (hOD hz).1
  have hOΩ : chartInv x '' O ⊆ Ω := by
    rintro y ⟨z,hz,rfl⟩
    exact (hOD (subset_closure hz)).2
  let p : Parabolic.Point n := (chartPt x x,t)
  have hl : 0 < t/2 := half_pos ht
  have hp : p ∈ O ×ˢ Set.Ioo (t/2) (t+1) :=
    ⟨hxO (Set.mem_singleton _),half_lt_self ht,by linarith⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hO.prod isOpen_Ioo) p hp
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
  have hbuffer : K ⊆ O ×ˢ Set.Ioo (t/2) (t+1) := by
    intro q hq
    apply hball
    exact (mem_closedBall.mp hq).trans_lt (half_lt_self hε)
  have hKQ : K ⊆ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) := by
    intro q hq
    have hq' := hbuffer hq
    exact ⟨⟨(subset_closure.trans hOt) hq'.1,hOΩ ⟨q.1,hq'.1,rfl⟩⟩,hl.trans hq'.2.1⟩
  obtain ⟨C,hC,hBound⟩ := dirichletClassicalHeat_compact_value_bound g hK μ hμ Ω hΩ x
    hO hOc hOt hOΩ hl K hKc hreg hbuffer hKQ
  refine ⟨C,hC,?_⟩
  intro f
  have hb := hBound f p (Metric.mem_closedBall_self hδ.le)
  simpa only [p,hinv] using hb

end Yau.Proofs.F03Aux
