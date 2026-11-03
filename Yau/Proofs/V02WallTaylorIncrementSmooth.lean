import Yau.Proofs.V02WallTaylorNativeIncrements
import Yau.Proofs.V02WallTaylorKernelAt

/-! The literal wall increments are jointly smooth near compact buffered
data, even at a zero wall. This uses the cleared derivative-integral formula. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem native_wall_increments_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    {p : ℂ × ChartFactorAux n b} (hu : p.2.1 ∈ Metric.ball A δ)
    (hτ : ‖wallPower d j a (cotangentChartInv x p.2.1) • chartFactorDirection p‖ < R / 2)
    (hRb : |chartBaseFactor d j a Ψ x p| < 1 / 2)
    (hRf : |chartFiberFactor d j a Ψ x p| < 1 / 2) :
    ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b =>
      nativeInverseIncrement d j a Ψ (cotangentChartInv x w.2.1) (w.1, w.2.2)) p ∧
    ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b =>
      nativeLogIncrement d j a Ψ (cotangentChartInv x w.2.1) (w.1, w.2.2)) p := by
  let m : CotangentCoord n → ℝ := fun u => wallPower d j a (cotangentChartInv x u)
  have hm : ContDiffOn ℝ ∞ m (Metric.ball A (2 * δ)) :=
    (wallPower_chart_contDiffOn hd j a x).mono hvalid
  have huT := hvalid (Metric.ball_subset_ball (by linarith) hu)
  have hopenT : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hproj : ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b => w.2.1) p :=
    contDiffAt_fst.comp p contDiffAt_snd
  have hdb : ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b =>
      deltaBase d j (cotangentChartInv x w.2.1).1) p :=
    ((deltaBase_chart_contDiffOn hd j x).contDiffAt (hopenT.mem_nhds huT)).comp (f := fun w : ℂ × ChartFactorAux n b => w.2.1) p hproj
  have hdf : ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b =>
      deltaFiber d j (cotangentChartInv x w.2.1)) p :=
    ((deltaFiber_chart_contDiffOn hd j x).contDiffAt (hopenT.mem_nhds huT)).comp (f := fun w : ℂ × ChartFactorAux n b => w.2.1) p hproj
  have hmAt : ContDiffAt ℝ ∞ (fun w : ℂ × ChartFactorAux n b => m w.2.1) p :=
    ((wallPower_chart_contDiffOn hd j a x).contDiffAt (hopenT.mem_nhds huT)).comp (f := fun w : ℂ × ChartFactorAux n b => w.2.1) p hproj
  have hpDom : p ∈ chartFactorDomain Ψ m x A δ R :=
    mem_chartFactorDomain_of_time_bound hδ hR hsource (Metric.ball_subset_closedBall hu)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hτ.le)
  have hdom := (isOpen_chartFactorDomain hΨ hm).mem_nhds hpDom
  have hbase : ContDiffAt ℝ ∞ (chartBaseFactor d j a Ψ x) p :=
    (chartSprayFactor_contDiffOn hΨ (B := fun y => deltaBase d j y.1)
      (deltaBase_chart_contDiffOn hd j x) hm).contDiffAt hdom
  have hfiber : ContDiffAt ℝ ∞ (chartFiberFactor d j a Ψ x) p :=
    (chartSprayFactor_contDiffOn hΨ (B := deltaFiber d j)
      (deltaFiber_chart_contDiffOn hd j x) hm).contDiffAt hdom
  have hprof := setup_wallProfiles hd
  have hbu : deltaBase d j (cotangentChartInv x p.2.1).1 ∈ Set.Icc 0 1 :=
    ⟨(hprof.2.2.1 _).1, deltaBase_le_one hprof _ _⟩
  have hfu : deltaFiber d j (cotangentChartInv x p.2.1) ∈ Set.Icc 0 1 :=
    ⟨(hprof.2.2.2 _).1, deltaFiber_le_one hprof _ _⟩
  have hdenb : 1 + wallRatioMultiplier a (deltaBase d j (cotangentChartInv x p.2.1).1)
      (deltaFiber d j (cotangentChartInv x p.2.1)) * chartBaseFactor d j a Ψ x p ≠ 0 := by
    have := (wall_ratio_bounds (a := a) hbu hfu hRb.le).1
    linarith
  have hdenf : 1 + wallRatioMultiplier a (deltaFiber d j (cotangentChartInv x p.2.1))
      (deltaBase d j (cotangentChartInv x p.2.1).1) * chartFiberFactor d j a Ψ x p ≠ 0 := by
    have := (wall_ratio_bounds (a := a) hfu hbu hRf.le).1
    linarith
  have hinv := (clearedInverseIncrement_contDiffAt a hdb hdf hbase hdenb).add
    (clearedInverseIncrement_contDiffAt a hdf hdb hfiber hdenf)
  have hlog := (clearedLogIncrement_contDiffAt a hdb hdf hbase hdenb).add
    (clearedLogIncrement_contDiffAt a hdf hdb hfiber hdenf)
  have hnear : ∀ᶠ w : ℂ × ChartFactorAux n b in 𝓝 p,
      w.2.1 ∈ Metric.ball A δ ∧
      ‖m w.2.1 • chartFactorDirection w‖ < R / 2 ∧
      |chartBaseFactor d j a Ψ x w| < 1 / 2 ∧ |chartFiberFactor d j a Ψ x w| < 1 / 2 := by
    have huN := hproj.continuousAt.eventually (isOpen_ball.mem_nhds hu)
    have htN := (hmAt.continuousAt.smul chartFactorDirection_contDiff.continuous.continuousAt).norm.eventually
      (isOpen_Iio.mem_nhds hτ)
    have hbN := hbase.continuousAt.abs.eventually (isOpen_Iio.mem_nhds hRb)
    have hfN := hfiber.continuousAt.abs.eventually (isOpen_Iio.mem_nhds hRf)
    filter_upwards [huN, htN, hbN, hfN] with w hw ht hb hf
    exact ⟨hw, ht, hb, hf⟩
  refine ⟨hinv.congr_of_eventuallyEq ?_, hlog.congr_of_eventuallyEq ?_⟩ <;>
    filter_upwards [hnear] with w hw
  · exact (native_wall_increments_eq_chart hd j a ha hzero x hδ hR hvalid hΨ hsource
      (Metric.ball_subset_closedBall hw.1)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2.1.le) hw.2.2.1.le hw.2.2.2.le).1
  · exact (native_wall_increments_eq_chart hd j a ha hzero x hδ hR hvalid hΨ hsource
      (Metric.ball_subset_closedBall hw.1)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2.1.le) hw.2.2.1.le hw.2.2.2.le).2

end Yau.Blueprint.V02WallTaylorProof
