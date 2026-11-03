import Yau.Proofs.V03PartialWirtinger
import Yau.Proofs.V03WallTensor

/-! The actual nonsingular part of the boundary cost and its actual spatial
Levi entries are jointly smooth through both endpoints of the time slab. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def boundarySmoothChartCost (d : VariationData X q) (j : ℕ) (x : Pt X)
    (p : CotangentCoord n × ℝ) : ℝ :=
  dualNorm (d.h p.2) (cotangentChartInv x p.1).1 (cotangentChartInv x p.1).2 +
    baseCost d j (cotangentChartInv x p.1).1 p.2

theorem boundarySmoothChartCost_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (boundarySmoothChartCost d j x)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hnorm : ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      dualNorm (d.h p.2) (cotangentChartInv x p.1).1 (cotangentChartInv x p.1).2)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
    have hh := (metricFamily_dualNormChart_contDiffOn hd.2.2.1.1.1.2.1 x).mono
      (show cotangentTarget x ×ˢ Set.Icc 0 d.extendedT ⊆ cotangentTarget x ×ˢ Set.Ici 0 from
        fun p hp => ⟨hp.1, hp.2.1⟩)
    exact hh.congr (fun p hp => dualNorm_cotangentChartInv (d.h p.2) x hp.1)
  have hscalar {b : Pt X → ℝ → ℝ} (hb : SmoothSpaceTime b (Set.Icc 0 d.extendedT)) :
      ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => b (cotangentChartInv x p.1).1 p.2)
        (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
    have hp : ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
    exact (hb x).comp hp.contDiffOn (fun p hp => ⟨hp.1.1, hp.2⟩)
  exact hnorm.add ((contDiffOn_const.mul (hscalar hd.2.2.2.2.2.2.2.2.1.1)).add
    (hscalar (hd.2.2.2.2.2.2.2.2.2.1 j).1))

theorem boundarySmoothChartHessian_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) (x : Pt X) (a b : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      leviMatrix (fun z => boundarySmoothChartCost d j x (z, p.2)) p.1 cotangentDir a b)
      (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hSJ : UniqueDiffOn ℝ (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) :=
    hopen.uniqueDiffOn.prod (uniqueDiffOn_Icc (hd.1.trans hd.2.1))
  exact leviMatrix_parameter_contDiffOn hopen hSJ (boundarySmoothChartCost_contDiffOn hd j x)
    cotangentDir a b

end Yau.Blueprint.V03Proof
