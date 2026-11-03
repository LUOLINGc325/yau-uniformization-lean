import Yau.Proofs.F03DirichletLocalPositive
import Yau.Proofs.F03PositivityChaining
import Yau.Proofs.F03DirichletEvaluationNonzero

/-! Actual local chart comparison propagates positivity through the connected domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletClassicalHeat_local_forwardPositive (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ y ∂μ.restrict Ω, 0 ≤ f y)
    (x : M.Carrier) (hx : x ∈ Ω) :
    ∀ᶠ y in 𝓝[Ω] x,
      ForwardPositive (dirichletClassicalHeat g hK μ hμ Ω hΩ f) x y ∧
      ForwardPositive (dirichletClassicalHeat g hK μ hμ Ω hΩ f) y x := by
  let o := chartPt x x
  have hinv : chartInv x o=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have ho : o ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} :=
    ⟨mem_extChartAt_target x,by rwa [hinv]⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp (dirichletChartInterior_open Ω hΩ x) o ho
  let r := ρ/2
  have hr : 0 < r := half_pos hρ
  have hBall : Metric.closedBall o r ⊆ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} := by
    intro z hz
    apply hball
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hρ)
  have hHalfTarget : Metric.ball o (r/2) ⊆ chartTarget x := by
    intro z hz
    have hz' : z ∈ Metric.closedBall o r :=
      Metric.closedBall_subset_closedBall (by linarith only [hr]) (Metric.ball_subset_closedBall hz)
    exact (hBall hz').1
  let N := scalarChartRegion x (Metric.ball o (r/2))
  have hNopen : IsOpen N := scalarChartRegion_open x Metric.isOpen_ball hHalfTarget
  have hxN : x ∈ N := ⟨o,Metric.mem_ball_self (half_pos hr),hinv⟩
  have hNear : ∀ᶠ y in 𝓝[Ω] x, y ∈ N :=
    (show ∀ᶠ y in 𝓝 x, y ∈ N from hNopen.mem_nhds hxN).filter_mono nhdsWithin_le_nhds
  filter_upwards [hNear] with y hyN
  have hycoord : chartPt x y ∈ Metric.ball o (r/2) := scalarChartRegion_coords x hHalfTarget hyN
  have hysource := scalarChartRegion_source x hHalfTarget hyN
  have hyinv : chartInv x (chartPt x y)=y := (extChartAt (ComplexModel n) x).left_inv hysource
  have hcenter : o ∈ Metric.closedBall o (r/2) := Metric.mem_closedBall_self (half_pos hr).le
  have hyhalf : chartPt x y ∈ Metric.closedBall o (r/2) := Metric.ball_subset_closedBall hycoord
  constructor
  · intro s t hs hst hpos
    have hchartpos : 0 < dirichletClassicalChartHeat g hK μ hμ Ω hΩ x f (o,s) := by
      simpa only [dirichletClassicalChartHeat,hinv] using hpos
    have h := dirichletClassicalHeat_chart_forward_positive g hK μ hμ Ω hΩ x f hf
      o o (chartPt x y) hr hBall hcenter hyhalf hs hst hchartpos
    simpa only [dirichletClassicalChartHeat,hyinv] using h
  · intro s t hs hst hpos
    have hchartpos : 0 < dirichletClassicalChartHeat g hK μ hμ Ω hΩ x f (chartPt x y,s) := by
      simpa only [dirichletClassicalChartHeat,hyinv] using hpos
    have h := dirichletClassicalHeat_chart_forward_positive g hK μ hμ Ω hΩ x f hf
      o (chartPt x y) o hr hBall hyhalf hcenter hs hst hchartpos
    simpa only [dirichletClassicalChartHeat,hinv] using h

theorem dirichletClassicalHeat_strict_pos (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (hConn : IsPreconnected Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ y ∂μ.restrict Ω, 0 ≤ f y) (hfn : f ≠ 0)
    (x : M.Carrier) (hx : x ∈ Ω) {t : ℝ} (ht : 0 < t) :
    0 < dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  obtain ⟨y,hy,hpos⟩ := dirichletClassicalHeat_pos_somewhere g hK μ hμ Ω hΩ f hf hfn (half_pos ht)
  have hReach := forwardPositive_on_preconnected (dirichletClassicalHeat g hK μ hμ Ω hΩ f) hConn
    (dirichletClassicalHeat_local_forwardPositive g hK μ hμ Ω hΩ f hf) hy hx
  exact hReach (t/2) t (half_pos ht) (half_lt_self ht) hpos

theorem dirichletKernelCandidate_strict_pos (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (hConn : IsPreconnected Ω)
    (x y : M.Carrier) (hx : x ∈ Ω) (hy : y ∈ Ω) {t : ℝ} (ht : 0 < t) :
    0 < dirichletKernelCandidate g hK μ hμ Ω hΩ t x y := by
  rw [congrFun (dirichletKernelCandidate_row_classical g hK μ hμ Ω hΩ ht x hx) y]
  exact dirichletClassicalHeat_strict_pos g hK μ hμ Ω hΩ hConn
    (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))
    (dirichletHeatEvaluationVector_nonneg g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))
    (dirichletHeatEvaluationVector_ne_zero g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht)) y hy (half_pos ht)

end Yau.Proofs.F03Aux
