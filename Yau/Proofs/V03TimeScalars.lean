import Yau.Proofs.V03MetricTime
import Yau.Proofs.V03DiscScalars

/-! Actual scalar composition along a cotangent disc and its physical clock,
including time-dependent inverse metric and localization costs. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint
open Filter

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentDisc_scalarTime_contDiffOn {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {I : Set ℝ} {t : ℂ → ℝ}
    (ht : ContDiffOn ℝ ∞ t (Metric.closedBall 0 1))
    (hI : Set.MapsTo t (Metric.closedBall 0 1) I) {b : CotangentPoint M → ℝ → ℝ}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞
      (fun p : CotangentCoord n × ℝ => b (cotangentChartInv x p.1) p.2)
      (cotangentTarget x ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun ζ => b (f ζ) (t ζ)) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hp := (hcoord.restrict_scalars ℝ).prodMk (ht.mono Set.inter_subset_left)
  have hm := (hb (f ζ).1).comp hp
    (fun η hη => ⟨cotangentChart_mapsTo (f ζ).1 (hsource η hη), hI hη.1⟩)
  apply (contDiffWithinAt_inter (hV.mem_nhds hζV)).mp
  apply (hm ζ ⟨hζ, hζV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact congrArg (fun y => b y (t η)) (cotangentChart_left_inv (f ζ).1 (hsource η hη)).symm

theorem cotangentDisc_metricFamilyNorm_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {t : ℂ → ℝ} (ht : ContDiffOn ℝ ∞ t (Metric.closedBall 0 1))
    (hI : Set.MapsTo t (Metric.closedBall 0 1) I) :
    ContDiffOn ℝ ∞ (fun ζ => dualNorm (h (t ζ)) (f ζ).1 (f ζ).2) (Metric.closedBall 0 1) := by
  apply cotangentDisc_scalarTime_contDiffOn hf ht hI
    (b := fun y s => dualNorm (h s) y.1 y.2)
  intro x
  exact (metricFamily_dualNormChart_contDiffOn hh x).congr
    (fun p hp => dualNorm_cotangentChartInv (h p.2) x hp.1)

theorem cotangentDisc_smoothSpaceTime_contDiffOn {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {t : ℂ → ℝ} (ht : ContDiffOn ℝ ∞ t (Metric.closedBall 0 1))
    (hI : Set.MapsTo t (Metric.closedBall 0 1) I) :
    ContDiffOn ℝ ∞ (fun ζ => u (f ζ).1 (t ζ)) (Metric.closedBall 0 1) := by
  apply cotangentDisc_scalarTime_contDiffOn hf ht hI (b := fun y s => u y.1 s)
  intro x
  have hp : ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  exact (hu x).comp hp.contDiffOn (fun p hp => ⟨hp.1.1, hp.2⟩)

variable {q : ℕ} {X : KahlerManifold n}

theorem discTime_contDiffOn {F : VariationDisc X}
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) :
    ContDiffOn ℝ ∞ (discTime F) (Metric.closedBall 0 1) := by
  have hre := Complex.reCLM.contDiff.comp_contDiffOn (hw.restrict_scalars ℝ)
  exact contDiffOn_const.mul ((contDiffOn_const.mul hre).exp)

theorem admissible_metricNorm_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiffOn ℝ ∞ (fun ζ => dualNorm (d.h (discTime F ζ)) (F.f ζ).1 (F.f ζ).2)
      (Metric.closedBall 0 1) :=
  cotangentDisc_metricFamilyNorm_contDiffOn hd.2.2.1.1.1.2.1 hF.1
    (discTime_contDiffOn hF.2.1) (fun ζ hζ => (admissible_discTime_mem hF hζ).1.le)

theorem admissible_baseCost_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiffOn ℝ ∞ (fun ζ => baseCost d j (F.f ζ).1 (discTime F ζ)) (Metric.closedBall 0 1) := by
  have ht := discTime_contDiffOn hF.2.1
  have hI : Set.MapsTo (discTime F) (Metric.closedBall 0 1) (Set.Icc 0 d.extendedT) := by
    intro ζ hζ
    have hs := admissible_discTime_mem hF hζ
    exact ⟨hs.1.le, hs.2.le.trans hd.2.1.le⟩
  have hQ := cotangentDisc_smoothSpaceTime_contDiffOn hd.2.2.2.2.2.2.2.2.1.1 hF.1 ht hI
  have hρ := cotangentDisc_smoothSpaceTime_contDiffOn (hd.2.2.2.2.2.2.2.2.2.1 j).1 hF.1 ht hI
  exact (contDiffOn_const.mul hQ).add hρ

end Yau.Blueprint.V03Proof
