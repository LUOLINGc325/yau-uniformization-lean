import Yau.Proofs.V04WallErrorHorizontal
import Yau.Proofs.V04WallErrorClearedPolynomial
import Yau.Proofs.V03PartialWirtinger
import Yau.Proofs.V03WallHessian

/-! Smooth fixed-chart coefficients of the normalized fiber estimate,
with the physical time parameter kept in its original closed interval. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

def fiberNormModel (d : VariationData X q) (x : Pt X) (t : ℝ) (z : CotangentCoord n) : ℝ :=
  dualNorm (d.h t) (cotangentChartInv x z).1 (cotangentChartInv x z).2

def fiberBaseModel (d : VariationData X q) (j : ℕ) (x : Pt X) (t : ℝ)
    (z : CotangentCoord n) : ℝ := baseCost d j (cotangentChartInv x z).1 t

def normalizedFiberProfile (d : VariationData X q) (x : Pt X) (z : CotangentCoord n) : ℝ :=
  d.profileFiber (fiberNormModel d x 0 z)

def fiberBaseCleared (d : VariationData X q) (j : ℕ) (x : Pt X)
    (z : CotangentCoord n) : CotangentMatrix n :=
  clearedReciprocalMatrix (fun w => deltaBase d j (cotangentChartInv x w).1) 3 cotangentDir z

def fiberFiberCleared (d : VariationData X q) (x : Pt X)
    (z : CotangentCoord n) : CotangentMatrix n :=
  clearedReciprocalMatrix (normalizedFiberProfile d x) 3 cotangentDir z

theorem fiberNormModel_contDiffOn {d : VariationData X q} (hd : VariationSetup d) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => fiberNormModel d x p.2 p.1)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hh := (metricFamily_dualNormChart_contDiffOn hd.2.2.1.1.1.2.1 x).mono
    (show cotangentTarget x ×ˢ Set.Icc 0 d.extendedT ⊆ cotangentTarget x ×ˢ Set.Ici 0 from
      fun p hp => ⟨hp.1, hp.2.1⟩)
  exact hh.congr (fun p hp => dualNorm_cotangentChartInv (d.h p.2) x hp.1)

theorem fiberBaseModel_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => fiberBaseModel d j x p.2 p.1)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hscalar {b : Pt X → ℝ → ℝ} (hb : SmoothSpaceTime b (Set.Icc 0 d.extendedT)) :
      ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => b (cotangentChartInv x p.1).1 p.2)
        (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
    have hp : ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
    exact (hb x).comp hp.contDiffOn (fun p hp => ⟨hp.1.1, hp.2⟩)
  exact ((contDiffOn_const.mul (hscalar hd.2.2.2.2.2.2.2.2.1.1)).add
    (hscalar (hd.2.2.2.2.2.2.2.2.2.1 j).1))

theorem normalizedFiberProfile_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (x : Pt X) :
    ContDiffOn ℝ ∞ (normalizedFiberProfile d x) (cotangentTarget x) := by
  have hnorm : ContDiffOn ℝ ∞ (fiberNormModel d x 0) (cotangentTarget x) := by
    rw [show fiberNormModel d x 0 =
      (fun z => dualNorm X.metric.form (cotangentChartInv x z).1 (cotangentChartInv x z).2) from
        by unfold fiberNormModel; rw [hd.2.2.1.1.1.1]]
    exact (dualNormChart_contDiffOn X.metric x).congr
      (fun z hz => dualNorm_cotangentChartInv X.metric.form x hz)
  exact (setup_wallProfiles hd).2.1.comp_contDiffOn hnorm

theorem fiberNormHessian_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (x : Pt X) (a b : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      leviMatrix (fiberNormModel d x p.2) p.1 cotangentDir a b)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact leviMatrix_parameter_contDiffOn hopen
    (hopen.uniqueDiffOn.prod (uniqueDiffOn_Icc (hd.1.trans hd.2.1)))
    (fiberNormModel_contDiffOn hd x) cotangentDir a b

theorem fiberBaseHessian_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) (x : Pt X) (a b : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      leviMatrix (fiberBaseModel d j x p.2) p.1 cotangentDir a b)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact leviMatrix_parameter_contDiffOn hopen
    (hopen.uniqueDiffOn.prod (uniqueDiffOn_Icc (hd.1.trans hd.2.1)))
    (fiberBaseModel_contDiffOn hd j x) cotangentDir a b

theorem fiberBaseCleared_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) (x : Pt X) (a b : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun z => fiberBaseCleared d j x z a b) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedReciprocalMatrix_entry_contDiffOn hopen (deltaBase_chart_contDiffOn hd j x)
    3 cotangentDir a b

theorem fiberFiberCleared_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (x : Pt X) (a b : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun z => fiberFiberCleared d x z a b) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedReciprocalMatrix_entry_contDiffOn hopen (normalizedFiberProfile_contDiffOn hd x)
    3 cotangentDir a b

end Yau.Blueprint.V04Proof.WallErrorAux
