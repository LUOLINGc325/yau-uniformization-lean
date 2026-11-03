import Yau.Proofs.D02LimitExtension
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! A metric normal limit is holomorphic in a genuine fixed target chart.
The same chart coordinates converge with their first complex derivatives. -/

open scoped Topology Manifold ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem holomorphic_curve_fixed_chart {n : ℕ} {M : ComplexManifold n}
    {U : Set ℂ} {f : ℂ → M.Carrier} (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f U)
    (p : M.Carrier) (hmap : MapsTo f U (extChartAt (ComplexModel n) p).source) :
    DifferentiableOn ℂ (fun z => chartPt p (f z)) U := by
  have hc := (contMDiffOn_extChartAt (I := ComplexModel n) (n := ∞) (x := p)).comp hf
    (by intro z hz; simpa only [Set.mem_preimage, extChartAt_source] using hmap hz)
  exact (hc.mdifferentiableOn (by simp)).differentiableOn

theorem holomorphic_limit_fixed_chart {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (hO : IsOpen O)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hfs : ∀ j, ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (fs j) O)
    (hc : ContinuousOn f O)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O)
    {x : ℂ} (hx : x ∈ O) :
    ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ O ∧
      MapsTo f (closedBall x R) (extChartAt (ComplexModel n) (f x)).source ∧
      (∀ᶠ j in atTop, MapsTo (fs j) (closedBall x R) (extChartAt (ComplexModel n) (f x)).source) ∧
      DifferentiableOn ℂ (fun z => chartPt (f x) (f z)) (ball x R) ∧
      TendstoLocallyUniformlyOn (fun j z => chartPt (f x) (fs j z))
        (fun z => chartPt (f x) (f z)) atTop (ball x R) ∧
      TendstoLocallyUniformlyOn (fun j => deriv (fun z => chartPt (f x) (fs j z)))
        (deriv (fun z => chartPt (f x) (f z))) atTop (ball x R) := by
  letI := L12Aux.inducedMetricSpace g
  letI : ProperSpace M.Carrier := L12Aux.inducedMetricSpace_proper g
  have hn : O ∩ f ⁻¹' (extChartAt (ComplexModel n) (f x)).source ∈ 𝓝 x :=
    inter_mem (hO.mem_nhds hx)
      ((hc.continuousAt (hO.mem_nhds hx)).preimage_mem_nhds (extChartAt_source_mem_nhds (f x)))
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  have hRO : closedBall x R ⊆ O := fun z hz => (hsub hz).1
  have hfchart : MapsTo f (closedBall x R) (extChartAt (ComplexModel n) (f x)).source :=
    fun z hz => (hsub hz).2
  have hconvR := (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).mp hconv
    (closedBall x R) hRO (isCompact_closedBall x R)
  obtain ⟨hfschart, hcoord⟩ := uniform_limit_compact_chart_coordinates
    (isCompact_closedBall x R) (hc.mono hRO) hconvR
    (isOpen_extChartAt_source (I := ComplexModel n) (f x)) hfchart
    (chartPt (f x)) (continuousOn_extChartAt (I := ComplexModel n) (f x))
  have hcoordLocal : TendstoLocallyUniformlyOn (fun j z => chartPt (f x) (fs j z))
      (fun z => chartPt (f x) (f z)) atTop (ball x R) :=
    hcoord.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hdiff : ∀ᶠ j in atTop,
      DifferentiableOn ℂ (fun z => chartPt (f x) (fs j z)) (ball x R) := by
    filter_upwards [hfschart] with j hj
    exact holomorphic_curve_fixed_chart ((hfs j).mono (ball_subset_closedBall.trans hRO))
      (f x) (fun z hz => hj (ball_subset_closedBall hz))
  exact ⟨R, hR, hRO, hfchart, hfschart,
    hcoordLocal.differentiableOn hdiff isOpen_ball, hcoordLocal,
    hcoordLocal.deriv hdiff isOpen_ball⟩

theorem holomorphic_limit_contMDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (hO : IsOpen O)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hfs : ∀ j, ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (fs j) O)
    (hc : ContinuousOn f O)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O) :
    ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O := by
  intro x hx
  obtain ⟨R, hR, _, _, _, hd, _, _⟩ := holomorphic_limit_fixed_chart g hO fs f hfs hc hconv hx
  have hcd : ContDiffAt ℂ ∞ (fun z => chartPt (f x) (f z)) x :=
    (hd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_target.mpr
  refine ⟨hc.continuousAt (hO.mem_nhds hx), ?_⟩
  exact hcd.contMDiffAt

end Yau.NodeProofs.D02Aux
