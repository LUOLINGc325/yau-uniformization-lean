import Yau.Proofs.V03BoundaryChartRegularity
import Yau.Proofs.V03BoundaryCostSmooth
import Yau.Proofs.V03FamilyLogTrace

/-! Joint angular smoothness of the original full boundary density, with
its physical clock and reciprocal walls. No uniform wall margin is used. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02CostMixedProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem cotangentHolomorphicOn_scalarTime_contDiffWithinAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {S : Set P} {f : P → CotangentPoint X.manifold}
    (hf : CotangentHolomorphicOn f S) {p : P} (hp : p ∈ S)
    {t : P → ℝ} (ht : ContDiffWithinAt ℝ ∞ t S p)
    {b : CotangentPoint X.manifold → ℝ → ℝ}
    (hb : ContDiffAt ℝ ∞
      (fun v : CotangentCoord n × ℝ => b (cotangentChartInv (f p).1 v.1) v.2)
      (cotangentChart (f p).1 (f p), t p)) :
    ContDiffWithinAt ℝ ∞ (fun v => b (f v) (t v)) S p := by
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p hp
  have hpcoord := ((hcoord p ⟨hp, hpV⟩).restrict_scalars ℝ).prodMk
    (ht.mono Set.inter_subset_left)
  have hcomp := hb.comp_contDiffWithinAt p hpcoord
  apply (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp
  apply hcomp.congr_of_eventuallyEq_of_mem ?_ ⟨hp, hpV⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact congrArg (fun y => b y (t v))
    (cotangentChart_left_inv (f p).1 (hsource v hv)).symm

theorem boundaryFullChartCost_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {y : CotangentPoint X.manifold} (hy : y ∈ boundaryRegion d j)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 d.extendedT) (s : ℝ) :
    ContDiffAt ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      let v := cotangentChartInv y.1 p.1
      dualNorm (d.h p.2) v.1 v.2 + wallCost d j v p.2 s)
      (cotangentChart y.1 y, t) := by
  let x := y.1
  let z0 := cotangentChart x y
  have hself : y ∈ cotangentSource x := mem_extChartAt_source x
  have hz : z0 ∈ cotangentTarget x := cotangentChart_mapsTo x hself
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hnhds : cotangentTarget x ×ˢ Set.Icc 0 d.extendedT ∈ 𝓝 (z0, t) :=
    prod_mem_nhds (hopen.mem_nhds hz) (Icc_mem_nhds ht.1 ht.2)
  have hcost := (boundarySmoothChartCost_contDiffOn hd j x).contDiffAt hnhds
  have hb := ((deltaBase_chart_contDiffOn hd j x).contDiffAt
    (hopen.mem_nhds hz)).comp (z0, t) contDiffAt_fst
  have hf := ((deltaFiber_chart_contDiffOn hd j x).contDiffAt
    (hopen.mem_nhds hz)).comp (z0, t) contDiffAt_fst
  have hround : cotangentChartInv x z0 = y := cotangentChart_left_inv x hself
  have hpos := setup_index_bounds hd j
  have hb0 : deltaBase d j (cotangentChartInv x z0).1 ≠ 0 := by
    rw [hround]
    exact (deltaBase_pos (setup_wallProfiles hd) hpos.1 hy.1).ne'
  have hf0 : deltaFiber d j (cotangentChartInv x z0) ≠ 0 := by
    rw [hround]
    exact (deltaFiber_pos (setup_wallProfiles hd) hpos.2 hy.2).ne'
  have hw := (contDiffAt_const (c := 1 + s)).mul
    (((hb.inv hb0).sub (contDiffAt_const (c := (1 : ℝ)))).add
      ((hf.inv hf0).sub (contDiffAt_const (c := (1 : ℝ)))))
  convert hcost.add hw using 1
  funext p
  simp only [boundarySmoothChartCost, wallCost, wallBase, wallFiber,
    Pi.inv_apply, Function.comp_def, x]
  ring

theorem family_boundaryDensity_joint_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F)
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hfamily : HolomorphicDiscFamily F fz r)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) r, AdmissibleVariationDisc d j {F with f := fz z}) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => boundaryDensity d j {F with f := fz p.1} (circlePoint p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) := by
  have ht : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => discTime F p.2)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (discTime_contDiffOn hF.2.1).comp contDiffOn_snd (fun p hp => hp.2)
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  intro p hp
  have hζ := circlePoint_mem_closedBall p.2
  have htime := admissible_discTime_mem hF hζ
  have hboundary := (hadm p.1 hp.1).2.2.2.2.2.2.2.1 p.2
  have hscalar := cotangentHolomorphicOn_scalarTime_contDiffWithinAt
    (b := fun y t => dualNorm (d.h t) y.1 y.2 + wallCost d j y t F.s)
    hfamily.2.2 (p := (p.1, circlePoint p.2)) ⟨hp.1, hζ⟩
    (ht _ ⟨hp.1, hζ⟩)
    (boundaryFullChartCost_contDiffAt hd j hboundary
      ⟨htime.1, htime.2.trans hd.2.1⟩ F.s)
  have hmaps : Set.MapsTo (fun v : ℂ × ℝ => (v.1, circlePoint v.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    fun v hv => ⟨hv.1, circlePoint_mem_closedBall v.2⟩
  exact hscalar.comp p (hc.contDiffWithinAt (s := Metric.ball (0 : ℂ) r ×ˢ Set.univ)) hmaps

end Yau.Blueprint.V02CostMixedProof
