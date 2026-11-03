import Yau.Proofs.F03DirichletHeatCylinder
import Yau.Proofs.F03MovingBumpComparison
import Yau.Proofs.F03MovingTubeGeometry

/-! Actual point-to-point positivity inside one compact interior chart ball. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletClassicalHeat_chart_forward_positive (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
    (o z₀ z₁ : Space n) {r : ℝ} (hr : 0 < r)
    (hBall : Metric.closedBall o r ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω})
    (hz₀ : z₀ ∈ Metric.closedBall o (r/2)) (hz₁ : z₁ ∈ Metric.closedBall o (r/2))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hpos : 0 < dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f (z₀,s)) :
    0 < dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f (z₁,t) := by
  let F := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f
  let T := t-s
  have hT : 0 < T := sub_pos.mpr hst
  have hclock : s+T=t := by dsimp only [T];ring
  have hhalf : r/2 ≤ r := by linarith only [hr]
  have h₀Q := hBall (Metric.closedBall_subset_closedBall hhalf hz₀)
  have h₁Q := hBall (Metric.closedBall_subset_closedBall hhalf hz₁)
  have hFcont : ContinuousAt (fun z => F (z,s)) z₀ := by
    have hAt := (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f).contDiffAt
      (((dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi).mem_nhds
        (show (z₀,s) ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Ioi (0 : ℝ) from ⟨h₀Q,hs⟩))
    exact (hAt.comp z₀ (contDiffAt_id.prodMk contDiffAt_const)).continuousAt
  let m := F (z₀,s)/2
  have hm : 0 < m := half_pos hpos
  have hmU : m < F (z₀,s) := half_lt_self hpos
  have hnear : ∀ᶠ z in 𝓝 z₀, m < F (z,s) := hFcont.eventually (eventually_gt_nhds hmU)
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min (δ/2) (r/4)
  have hR : 0 < R := lt_min (half_pos hδ) (by positivity)
  have hRδ : R < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hRr : R ≤ r/2 := (min_le_right _ _).trans (by linarith only [hr])
  obtain ⟨ε,hε,hεm⟩ := exists_movingBump_amplitude hm R
  let c := straightMovingCenter z₀ z₁ T
  let V := ‖T⁻¹ • (z₁-z₀)‖
  have hc : ContDiff ℝ 2 c := (straightMovingCenter_smooth z₀ z₁ T).of_le (by simp)
  have hc₀ : c 0=z₀ := straightMovingCenter_zero z₀ z₁ T
  have hcT : c T=z₁ := straightMovingCenter_terminal z₀ z₁ hT.ne'
  have hV : ∀ τ ∈ Icc (0 : ℝ) T, ‖deriv c τ‖ ≤ V := by
    intro τ _
    rw [(straightMovingCenter_hasDerivAt z₀ z₁ T τ).deriv]
  have hTube : ∀ z ∈ frontier (Metric.ball o r), ∀ τ ∈ Icc (0 : ℝ) T, R ≤ ‖z-c τ‖ := by
    intro z hz τ hτ
    have hzout : z ∉ Metric.ball o r := by
      rw [Metric.isOpen_ball.frontier_eq] at hz
      exact hz.2
    exact straightMovingCenter_tube_margin z₀ z₁ o hT hz₀ hz₁ hRr hτ hzout
  let K := closure (Metric.ball o r)
  have hKclosed : K ⊆ Metric.closedBall o r := Metric.closure_ball_subset_closedBall
  have hKcompact : IsCompact K := (isCompact_closedBall o r).of_isClosed_subset isClosed_closure hKclosed
  have hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} := hKclosed.trans hBall
  obtain ⟨lam,upper,hEll,hCyl⟩ := dirichletClassicalHeat_shifted_cylinder g hK μ hμ Ω hΩ a
    K hKcompact hKQ hs hT
  let u := positiveTimeShift s F
  have hu : C2 (cylinder K 0 T) u := (hCyl f).1
  have hu0 : ∀ p ∈ cylinder K 0 T, 0 ≤ u p := by
    intro p hp
    exact dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ f hf
      (add_pos_of_pos_of_nonneg hs hp.2.1) (chartInv a p.1) (hKQ hp.1).2
  have hHeat : ∀ p ∈ Metric.ball o r ×ˢ Ioc (0 : ℝ) T,
      linearOp (cylinder K 0 T) (LeafProofs.L19Aux.scalarHeatChartCoeff g a) (fun _ _ => 0) u p=0 := by
    intro p hp
    exact (hCyl f).2 p ⟨subset_closure hp.1,hp.2.1.le,hp.2.2⟩
  have hInit : ∀ z ∈ K, ε*movingBallBump R c (z,0) ≤ u (z,0) := by
    intro z hz
    by_cases hzR : ‖z-z₀‖ ≤ R
    · have hzδ : z ∈ Metric.ball z₀ δ := by
        rw [Metric.mem_ball,dist_eq_norm]
        exact hzR.trans_lt hRδ
      have hzlow : m ≤ u (z,0) := by
        simpa only [u,positiveTimeShift,add_zero] using (hδnear hzδ).le
      exact ((mul_le_mul_of_nonneg_left (movingBallBump_le_radius_power hR.le c (z,0)) hε.le).trans hεm).trans hzlow
    · have hzero : movingBallBump R c (z,0)=0 := by
        apply movingBallBump_eq_zero hR.le
        rw [hc₀]
        exact (lt_of_not_ge hzR).le
      rw [hzero,mul_zero]
      exact hu0 (z,0) ⟨hz,le_rfl,hT.le⟩
  have hComp := movingBump_comparison Metric.isOpen_ball hKcompact hT hR hε.le hEll hc hV hTube
    hu hu0 hHeat hInit
  let C := movingCubicRate R lam (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper)
  have hz₁ball : z₁ ∈ Metric.ball o r := by
    rw [Metric.mem_ball,dist_eq_norm]
    simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hz₁).trans_lt (half_lt_self hr)
  have hpT : (z₁,T) ∈ cylinder K 0 T := ⟨subset_closure hz₁ball,hT.le,le_rfl⟩
  have hwpos : 0 < decayingMovingBump ε C 0 R c (z₁,T) := by
    apply decayingMovingBump_pos hε hR
    rw [hcT,sub_self,norm_zero]
    exact hR
  have hufinal := hwpos.trans_le (hComp (z₁,T) hpT)
  simpa only [u,positiveTimeShift,hclock] using hufinal

end Yau.Proofs.F03Aux
