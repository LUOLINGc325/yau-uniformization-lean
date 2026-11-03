import Yau.Proofs.V03BoundaryChartRegularity
import Yau.Proofs.V04TimeCoefficientControl
import Yau.Proofs.V04ClockRegularity
import Yau.Proofs.V03FunctionalLower

/-! Actual physical-time jets on the complete one-sided slab. The
original circle integrand is smooth along each admissible disc. -/
open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivWithinAt_time_slice {S : Set E} {J : Set ℝ} {f : E × ℝ → F}
    {z : E} {t : ℝ} (hz : z ∈ S) (ht : t ∈ J)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) (z, t)) :
    HasDerivWithinAt (fun s => f (z, s))
      (fderivWithin ℝ f (S ×ˢ J) (z, t) (0, 1)) J t := by
  have hi : HasDerivWithinAt (fun s : ℝ => (z, s)) (0, 1) J t :=
    ((hasDerivAt_const t z).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  exact hf.hasFDerivWithinAt.comp_hasDerivWithinAt t hi (fun s hs => ⟨hz, hs⟩)

theorem time_slice_derivWithin {S : Set E} {J : Set ℝ} {f : E × ℝ → F}
    {z : E} {t : ℝ} (hz : z ∈ S) (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) (z, t)) :
    derivWithin (fun s => f (z, s)) J t = fderivWithin ℝ f (S ×ˢ J) (z, t) (0, 1) :=
  (hasDerivWithinAt_time_slice hz ht hf).derivWithin hJ

def clockSmoothCost (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  dualNorm (d.h t) y.1 y.2 + baseCost d j y.1 t

def clockTimeJet (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  derivWithin (clockSmoothCost d j y) (Icc 0 d.extendedT) t

def clockTimeJet₂ (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  derivWithin (clockTimeJet d j y) (Icc 0 d.extendedT) t

theorem coefficient_timeJet_chart_smooth {d : VariationData X q} (hd : VariationSetup d)
    {b : CotangentPoint X.manifold → ℝ → ℝ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      b (cotangentChartInv x p.1) p.2) (cotangentTarget x ×ˢ Icc 0 d.extendedT)) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      derivWithin (b (cotangentChartInv x p.1)) (Icc 0 d.extendedT) p.2)
      (cotangentTarget x ×ˢ Icc 0 d.extendedT) := by
  have hop : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hI : UniqueDiffOn ℝ (Icc 0 d.extendedT) := uniqueDiffOn_Icc (hd.1.trans hd.2.1)
  have hu := hop.uniqueDiffOn.prod hI
  have hs := ((hb x).fderivWithin hu (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := ((0, 1) : CotangentCoord n × ℝ)))
  apply hs.congr
  intro p hp
  exact time_slice_derivWithin hp.1 hp.2 (hI p.2 hp.2)
    ((hb x).differentiableOn (by simp) p hp)

theorem clockTimeJet_chart_smooth {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      clockTimeJet d j (cotangentChartInv x p.1) p.2)
      (cotangentTarget x ×ˢ Icc 0 d.extendedT) :=
  coefficient_timeJet_chart_smooth hd (boundarySmoothChartCost_contDiffOn hd j) x

theorem clockTimeJet₂_chart_smooth {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      clockTimeJet₂ d j (cotangentChartInv x p.1) p.2)
      (cotangentTarget x ×ˢ Icc 0 d.extendedT) :=
  coefficient_timeJet_chart_smooth hd (clockTimeJet_chart_smooth hd j) x

theorem coefficient_time_slice_smooth {d : VariationData X q}
    {b : CotangentPoint X.manifold → ℝ → ℝ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      b (cotangentChartInv x p.1) p.2) (cotangentTarget x ×ˢ Icc 0 d.extendedT))
    (y : CotangentPoint X.manifold) : ContDiffOn ℝ ∞ (b y) (Icc 0 d.extendedT) := by
  let x := y.1
  have hy : y ∈ cotangentSource x := mem_extChartAt_source x
  have hz := cotangentChart_mapsTo x hy
  have hc := (hb x).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun t ht => ⟨hz, ht⟩)
  change ContDiffOn ℝ ∞ (fun t => b (cotangentChartInv x (cotangentChart x y)) t) (Icc 0 d.extendedT) at hc
  simpa only [cotangentChart_left_inv x hy] using hc

theorem clockSmoothCost_hasDerivAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (y : CotangentPoint X.manifold) {t : ℝ} (ht : t ∈ Ioo 0 d.extendedT) :
    HasDerivAt (clockSmoothCost d j y) (clockTimeJet d j y t) t :=
  (((coefficient_time_slice_smooth (boundarySmoothChartCost_contDiffOn hd j) y).differentiableOn
    (by simp)) t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem clockTimeJet_hasDerivAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (y : CotangentPoint X.manifold) {t : ℝ} (ht : t ∈ Ioo 0 d.extendedT) :
    HasDerivAt (clockTimeJet d j y) (clockTimeJet₂ d j y t) t :=
  (((coefficient_time_slice_smooth (clockTimeJet_chart_smooth hd j) y).differentiableOn
    (by simp)) t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem cotangent_time_coefficient_bound {d : VariationData X q} (hd : VariationSetup d)
    {b : CotangentPoint X.manifold → ℝ → ℝ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      b (cotangentChartInv x p.1) p.2) (cotangentTarget x ×ˢ Icc 0 d.extendedT))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K, ∀ t ∈ Icc 0 d.T, |b y t| ≤ M := by
  letI : CompactSpace (d.G '' K) := isCompact_iff_compactSpace.mp
    (cotangentCompact_ambient_isCompact hd.2.2.2.2.1.1 hK)
  have hb' : ∀ x, ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      b (cotangentChartInv x p.1.1) p.1.2)
      ((cotangentTarget x ×ˢ Icc 0 d.extendedT) ×ˢ Set.univ) := fun x =>
    (hb x).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hc : Continuous (compactTimeCoefficient d (fun y t (_s : ℝ) => b y t) K) :=
    (compactTimeCoefficient_locallyLipschitz (F := ℝ) hd hb' hK).continuous
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (CompactImmersionTimes d.G K d.T))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun y hy t ht => ?_⟩
  let p : CompactImmersionTimes d.G K d.T :=
    ((⟨d.G y, ⟨y, hy, rfl⟩⟩, ⟨t, ht⟩), ⟨0, ⟨le_rfl, hd.1.le⟩⟩)
  have hh := hM p (Set.mem_univ p)
  change ‖b (compactImmersionPoint d.G ⟨d.G y, ⟨y, hy, rfl⟩⟩) t‖ ≤ M at hh
  rw [compactImmersionPoint_eq hd.2.2.2.2.1.2.1 y hy] at hh
  have hh' : |b y t| ≤ M := by simpa only [Real.norm_eq_abs] using hh
  exact hh'.trans (le_max_right 0 M)

theorem fixed_index_timeJet_bounds {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ boundaryCompact d j, ∀ t ∈ Icc 0 d.T,
      |clockTimeJet d j y t| ≤ M ∧ |clockTimeJet₂ d j y t| ≤ M := by
  have hK : CotangentCompact (boundaryCompact d j) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hi⟩
    exact (hi j).2.2.1
  obtain ⟨M, hM, hb⟩ := cotangent_time_coefficient_bound hd (clockTimeJet_chart_smooth hd j) hK
  obtain ⟨N, hN, hc⟩ := cotangent_time_coefficient_bound hd (clockTimeJet₂_chart_smooth hd j) hK
  refine ⟨M + N, add_nonneg hM hN, fun y hy t ht => ⟨?_, ?_⟩⟩
  · exact (hb y hy t ht).trans (le_add_of_nonneg_right hN)
  · exact (hc y hy t ht).trans (le_add_of_nonneg_left hM)

theorem normTime_chart_smooth {d : VariationData X q} (hd : VariationSetup d) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      dualNorm (d.h p.2) (cotangentChartInv x p.1).1 (cotangentChartInv x p.1).2)
      (cotangentTarget x ×ˢ Icc 0 d.extendedT) := by
  exact ((metricFamily_dualNormChart_contDiffOn hd.2.2.1.1.1.2.1 x).mono
    (fun p hp => ⟨hp.1, hp.2.1⟩)).congr
      (fun p hp => dualNorm_cotangentChartInv (d.h p.2) x hp.1)

theorem baseTime_chart_smooth {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => baseCost d j (cotangentChartInv x p.1).1 p.2)
      (cotangentTarget x ×ˢ Icc 0 d.extendedT) := by
  convert (boundarySmoothChartCost_contDiffOn hd j x).sub (normTime_chart_smooth hd x) using 1
  funext p
  unfold boundarySmoothChartCost
  ring

theorem clockTimeJet_eq_original {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (y : CotangentPoint X.manifold) {t : ℝ} (ht : t ∈ Ioo 0 d.extendedT) :
    clockTimeJet d j y t =
      derivWithin (fun t' => dualNorm (d.h t') y.1 y.2) (Ici 0) t +
      derivWithin (fun t' => baseCost d j y.1 t') (Ici 0) t := by
  have hN := ((coefficient_time_slice_smooth (b := fun y t => dualNorm (d.h t) y.1 y.2) (normTime_chart_smooth hd) y).contDiffAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  have hB := ((coefficient_time_slice_smooth (b := fun y t => baseCost d j y.1 t) (baseTime_chart_smooth hd j) y).contDiffAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  rw [clockTimeJet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  unfold clockSmoothCost
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1),
    derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)]
  simpa only [Pi.add_def] using deriv_add hN hB

theorem admissible_clockTimeJet_trace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ))) := by
  apply closedDisc_real_trace_contDiff (f := fun ζ => clockTimeJet d j (F.f ζ) (discTime F ζ))
  exact cotangentDisc_scalarTime_contDiffOn (b := clockTimeJet d j) (I := Icc 0 d.extendedT) hF.1 (discTime_contDiffOn hF.2.1)
    (fun ζ hζ => let ht := admissible_discTime_mem hF hζ
      ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩) (clockTimeJet_chart_smooth hd j)

theorem admissible_wallSum_trace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => wallBase d j (F.f (circlePoint θ)).1 + wallFiber d j (F.f (circlePoint θ))) := by
  have hW := admissible_wallTrace_contDiff hd hF
  have hB := closedDisc_real_trace_contDiff (admissible_baseCost_contDiffOn hd hF)
  convert (hW.sub hB).div_const (1 + F.s) using 1
  funext θ
  unfold wallCost
  have hs : (1 + F.s : ℝ) ≠ 0 := ne_of_gt (by linarith [hF.2.2.2.1])
  field_simp
  <;> ring

theorem clockBoundaryCost_integrand_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => let y := F.f (circlePoint θ)
      let t := discTime F (circlePoint θ)
      t / F.s * clockWeight d k j a F θ *
        (derivWithin (fun t' => dualNorm (d.h t') y.1 y.2) (Ici 0) t +
          derivWithin (fun t' => baseCost d j y.1 t') (Ici 0) t) +
        wallBase d j y.1 + wallFiber d j y) := by
  have hγ : ContDiff ℝ ∞ (clockWeight d k j a F) :=
    (clockWeightRaw_contDiff hd hk hF).div_const _
  have hh := (((admissible_discTime_trace_contDiff hF).div_const F.s).mul hγ).mul
    (admissible_clockTimeJet_trace_contDiff hd hF) |>.add (admissible_wallSum_trace_contDiff hd hF)
  convert hh using 1
  funext θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  rw [clockTimeJet_eq_original hd j _ ⟨ht.1, ht.2.trans hd.2.1⟩]
  ring

end Yau.Blueprint.V04Proof.ClockTaylorAux
