import Yau.Proofs.V04TimeCoefficientControl
import Yau.Proofs.V04ClockRegularity
import Yau.Proofs.V03WallTensor

/-! The original raw clock is a globally smooth coefficient on each
cotangent chart, including the zero-wall locus and time zero. -/

open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def clockRawCoefficient (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (y : CotangentPoint X.manifold) (t : ℝ) : ℝ :=
  wallPower d j a y ^ 4 *
    Real.exp (-clockBaseCutoff d k j y.1 * (d.rho y.1 t + k.dampingPower * Real.log (j + 3))) *
    Real.exp (-clockFiberCutoff d k j y * (Real.log (k.fiberCoefficient j) +
      k.dampingPower * Real.log (j + 3) + k.dampingPower * Real.log (1 + d.B j)))

theorem clockRawCoefficient_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) (x : X.manifold.Carrier) :
    ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      clockRawCoefficient d k j a (cotangentChartInv x p.1.1) p.1.2)
      ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
  let S : Set ((CotangentCoord n × ℝ) × ℝ) :=
    ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ)
  have hp : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ => p.1.1) S := by
    fun_prop
  have hmap : Set.MapsTo (fun p : (CotangentCoord n × ℝ) × ℝ => p.1.1) S
      (cotangentTarget x) := fun p hp => hp.1.1
  have hw := (((deltaBase_chart_contDiffOn hd j x).mul
    (deltaFiber_chart_contDiffOn hd j x)).pow a).pow 4
  have hbase : ContDiffOn ℝ ∞ (fun z => clockBaseCutoff d k j (cotangentChartInv x z).1)
      (cotangentTarget x) := by
    exact ((hk.2.2.2.1 j).2.1 x).comp contDiff_fst.contDiffOn (fun z hz => hz.1)
  have hfiber := (hk.2.2.2.1 j).2.2.2.2.2.2 x
  have hrho : SmoothSpaceTime d.rho (Set.Ici 0) := hd.2.2.1.1.2.2.2.1
  have hrt : ContDiff ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ => (p.1.1.1, p.1.2)) := by
    fun_prop
  have hr : ContDiffOn ℝ ∞ (fun p : (CotangentCoord n × ℝ) × ℝ =>
      d.rho (cotangentChartInv x p.1.1).1 p.1.2) S :=
    (hrho x).comp hrt.contDiffOn (fun p hp => ⟨hp.1.1.1, hp.1.2.1⟩)
  exact ((hw.comp hp hmap).mul (((hbase.comp hp hmap).neg.mul
    (hr.add contDiffOn_const)).exp)).mul
      (((hfiber.comp hp hmap).neg.mul contDiffOn_const).exp)

theorem clockRawCoefficient_compact_lipschitz {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ boundaryCompact d j, ∀ y' ∈ boundaryCompact d j,
      ∀ t ∈ Set.Icc 0 d.T, ∀ t' ∈ Set.Icc 0 d.T,
      |clockRawCoefficient d k j a y t - clockRawCoefficient d k j a y' t'| ≤
        C * (‖d.G y - d.G y'‖ + |t - t'|) := by
  obtain ⟨C, hC, hbound⟩ := timeCoefficient_compact_lipschitz (b := fun y t (_ : ℝ) => clockRawCoefficient d k j a y t) hd
    (clockRawCoefficient_chart_contDiffOn hd hk j a)
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  refine ⟨C, hC, fun y hy y' hy' t ht t' ht' => ?_⟩
  simpa only [Real.norm_eq_abs, sub_self, abs_zero, add_zero] using
    hbound y hy y' hy' t ht t' ht' 0 ⟨le_rfl, hd.1.le⟩ 0 ⟨le_rfl, hd.1.le⟩

end Yau.Blueprint.V04Proof
