import Yau.Proofs.V02CostMixedDensity
import Yau.Proofs.V03OuterBoundary

/-! Joint smoothness of the original boundary expressions needs only the
actual holomorphic family, fixed clock, and the original two boundary walls. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof V02CostMixedProof

variable {n q : ℕ} {X : KahlerManifold n}

theorem actual_outer_norm_le_one {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖outerCandidate (logTrace d j F.f) a ζ‖ ≤ 1 := by
  have hh := outerCandidate_contDiffOn (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F) a
  apply norm_le_of_circle_bound hh ?_ ζ hζ
  intro θ
  rw [outerCandidate_logTrace_modulus hd hF a θ]
  exact (admissible_wallPower_bounds hd hF a θ).2

theorem family_boundaryDensity_contDiffOn_of_boundary {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hfamily : HolomorphicDiscFamily F fz r)
    (hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ, fz z (circlePoint θ) ∈ boundaryRegion d j) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => boundaryDensity d j {F with f := fz p.1} (circlePoint p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) := by
  have ht : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => discTime F p.2)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (discTime_contDiffOn hF.2.1).comp contDiffOn_snd (fun _ hp => hp.2)
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  intro p hp
  have hζ := circlePoint_mem_closedBall p.2
  have htime := admissible_discTime_mem hF hζ
  have hscalar := cotangentHolomorphicOn_scalarTime_contDiffWithinAt
    (b := fun y t => dualNorm (d.h t) y.1 y.2 + wallCost d j y t F.s)
    hfamily.2.2 (p := (p.1, circlePoint p.2)) ⟨hp.1, hζ⟩ (ht _ ⟨hp.1, hζ⟩)
    (boundaryFullChartCost_contDiffAt hd j (hboundary p.1 hp.1 p.2)
      ⟨htime.1, htime.2.trans hd.2.1⟩ F.s)
  exact hscalar.comp p (hc.contDiffWithinAt (s := Metric.ball (0 : ℂ) r ×ˢ Set.univ))
    (show Set.MapsTo (fun v : ℂ × ℝ => (v.1, circlePoint v.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) from
      fun v hv => ⟨hv.1, circlePoint_mem_closedBall v.2⟩)

theorem family_logTrace_contDiffOn_of_boundary {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hfamily : HolomorphicDiscFamily F fz r)
    (hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ, fz z (circlePoint θ) ∈ boundaryRegion d j) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => logTrace d j (fz p.1) p.2)
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) := by
  have hwall : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => wallProduct d j (fz p.1 p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    apply cotangentHolomorphicOn_scalar_contDiffOn hfamily.2.2
    intro x
    exact (deltaBase_chart_contDiffOn hd j x).mul (deltaFiber_chart_contDiffOn hd j x)
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  have htrace := hwall.comp hc.contDiffOn
    (show Set.MapsTo (fun p : ℂ × ℝ => (p.1, circlePoint p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) from
      fun p hp => ⟨hp.1, circlePoint_mem_closedBall p.2⟩)
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  exact htrace.log (fun p hp => (wallProduct_pos_le_one (setup_wallProfiles hd) hA hB
    (hboundary p.1 hp.1 p.2)).1.ne')

end Yau.Blueprint.V02WallTaylorProof
