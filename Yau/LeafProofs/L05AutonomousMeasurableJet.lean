import Yau.LeafProofs.L05AutonomousMeasurableJetEquation
import Yau.LeafProofs.L05AutonomousTimeDerivative

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Original normalized inputs give one actual compact extension, its canonical
measurable Hessian and a common full-measure set satisfying the true equation. -/
theorem auto_original_measurable_jet_data
    (n : ℕ) (hn : 0 < n) (ell L : ℝ) (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ delta C : ℝ, 0 < delta ∧ delta < 1 ∧ 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
        ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) →
        (∀ p ∈ unitClosed n, |u p| ≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
      ∃ w : Point n →ᵇ ℝ,
        EqOn (w : Point n → ℝ) u (unitClosed n) ∧ UniformContinuous (w : Point n → ℝ) ∧
        HasCompactSupport (w : Point n → ℝ) ∧ ‖w‖ ≤ 1 ∧
        (∀ (eps : ℝ) (heps : 0 < eps), eps < 1/256 →
          ∀ p ∈ autoClosed (0 : Space n) (45/64) 0,
            ‖secondFDerivMatrix (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1‖ ≤ C) ∧
        (∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < 1/512 →
          ∀ p ∈ autoClosed (0 : Space n) (11/16) 0, |autoSecond w e h p| ≤ C) ∧
      ∃ V : Point n → ℝ,
        ContinuousOn V (autoClosed (0 : Space n) (15/16) 0) ∧
        (∀ p ∈ autoClosed (0 : Space n) (15/16) 0, |V p| ≤ C) ∧
        HolderBound delta (autoClosed (0 : Space n) (15/16) 0) V C ∧
        autoPucci ell L (autoOpen (0 : Space n) (15/16) 0) V ∧
        (∀ x ∈ Metric.closedBall (0 : Space n) (15/16),
          (∀ t ∈ Ioo (-(15/16 : ℝ)^2) 0,
            HasDerivAt (fun s => u (x,s)) (V (x,t)) t) ∧
          (∀ t ∈ Icc (-(15/16 : ℝ)^2) 0,
            HasDerivWithinAt (fun s => u (x,s)) (V (x,t)) (Icc (-(15/16 : ℝ)^2) 0) t) ∧
          (∀ a ∈ Icc (-(15/16 : ℝ)^2) 0, ∀ b ∈ Icc (-(15/16 : ℝ)^2) 0,
            u (x,b)-u (x,a)=∫ s in a..b, V (x,s))) ∧
        (∀ z ∈ backward (15/16), timeD (backward (15/16)) u z=V z) ∧
        Measurable (peanoMeasurableHessian (w : Point n → ℝ)) ∧
      ∃ S : Set (Point n), MeasurableSet S ∧ S ⊆ autoOpen (0 : Space n) (5/8) 0 ∧
        (∀ᵐ p ∂((volume : Measure (Point n)).restrict (autoOpen (0 : Space n) (5/8) 0)), p ∈ S) ∧
        (∀ p ∈ S,
          (fun y => w (y,p.2)-w p-spatialD w p (y-p.1)-
            (1/2 : ℝ)*autoBilinearMap n (peanoMeasurableHessian (w : Point n → ℝ) p)
              (y-p.1) (y-p.1)) =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) ∧
        (∀ p ∈ S, ‖peanoMeasurableHessian (w : Point n → ℝ) p‖ ≤ C) ∧
        (∀ p ∈ S, ∀ e : Space n, ‖e‖=1 →
          |autoBilinearMap n (peanoMeasurableHessian (w : Point n → ℝ) p) e e| ≤ C) ∧
        (∀ p ∈ S, ∀ e : Space n,
          Tendsto (fun h => autoSecond w e h p) (𝓝[>] 0)
            (𝓝 (autoBilinearMap n (peanoMeasurableHessian (w : Point n → ℝ) p) e e))) ∧
        (∀ p ∈ S, F (peanoMeasurableHessian (w : Point n → ℝ) p)=V p) := by
  obtain ⟨B,hB,hForHessian⟩ := auto_uniform_mollified_hessian n hn ell L hell hL
  obtain ⟨Bs,hBs,hForSecond⟩ := auto_uniform_second_differences n hn ell L hell hL
  obtain ⟨delta,Ct,hd,hd1,hCt,hForTime⟩ := auto_time_derivative n hn ell L hell hL
  obtain ⟨Cn,hCn,hForMeasurable⟩ := peano_measurable_hessian n
  let C := 1+B+Bs+Ct+Cn*Bs
  have hProduct : 0 ≤ Cn*Bs := mul_nonneg hCn.le hBs.le
  have hC : 0 < C := by dsimp only [C]; linarith only [hB,hBs,hCt,hProduct]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hBs,hCt,hProduct]
  have hBsC : Bs ≤ C := by dsimp only [C]; linarith only [hB,hCt,hProduct]
  have hCtC : Ct ≤ C := by dsimp only [C]; linarith only [hB,hBs,hProduct]
  have hCnC : Cn*Bs ≤ C := by dsimp only [C]; linarith only [hB,hBs,hCt]
  refine ⟨delta,C,hd,hd1,hC,?_⟩
  intro F hF hE hConc h0 u hu hb hsol
  obtain ⟨w,hwu,hw,hcw,hw1,hHessian⟩ := hForHessian F hF hE hConc h0 u hu hb hsol
  have hSecondU := hForSecond F hF hE hConc h0 u hu hb hsol
  have hSecondW := auto_measurableJet_second_transport hwu hSecondU
  obtain ⟨V,hVc,hVB,hVH,hVP,hVTime,hVTimeD⟩ := hForTime F hF hE h0 u hu hb hsol
  have hQSecond : autoOpen (0 : Space n) (5/8) 0 ⊆ autoClosed 0 (11/16) 0 :=
    auto_measurableJet_open_closed_subset (by norm_num) (by norm_num)
  have hQTime : autoOpen (0 : Space n) (5/8) 0 ⊆ autoClosed 0 (15/16) 0 :=
    auto_measurableJet_open_closed_subset (by norm_num) (by norm_num)
  have hQI : (Metric.ball (0 : Space n) (5/8) ×ˢ Ioo (-(5/8 : ℝ)^2) 0)=
      autoOpen 0 (5/8) 0 := by simp only [autoOpen,zero_sub]
  have hLocalSecond : ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < 1/512 →
      ∀ p ∈ autoOpen (0 : Space n) (5/8) 0, |autoSecond w e h p| ≤ Bs :=
    fun e he h hh hs p hp => hSecondW e he h hh hs p (hQSecond hp)
  obtain ⟨hMeasH,S,hSMeas,hSSub,hSAe,hSPeano,hSNorm,hSLimit⟩ :=
    hForMeasurable (Metric.ball (0 : Space n) (5/8)) Metric.isOpen_ball
      (Ioo (-(5/8 : ℝ)^2) 0) measurableSet_Ioo Bs (1/512) hBs.le (by norm_num)
      (w : Point n → ℝ) w.continuous (spatialD w) (auto_spatialD_measurable w.continuous)
      (fun t ht => auto_original_extension_ae_spatial_peano hn hell hL hF hE hConc h0
        hu hb hsol hwu ⟨ht.1.le,ht.2.le⟩)
      (fun e he h hh hs p hp => hLocalSecond e he h hh hs p (hQI ▸ hp))
  rw [hQI] at hSSub hSAe
  have hTimeQ : ∀ q ∈ autoOpen (0 : Space n) (5/8) 0,
      HasDerivAt (fun t => u (q.1,t)) (V q) q.2 := by
    intro q hq
    have hqLarge := hQTime hq
    have ht : q.2 ∈ Ioo (-(15/16 : ℝ)^2) 0 := ⟨by linarith only [hq.2.1],hq.2.2⟩
    exact (hVTime q.1 hqLarge.1).1 q.2 ht
  refine ⟨w,hwu,hw,hcw,hw1,?_,?_,V,hVc,?_,
    auto_measurableJet_holder_mono hVH hCtC,hVP,hVTime,hVTimeD,hMeasH,
    S,hSMeas,hSSub,hSAe,hSPeano,?_,?_,hSLimit,?_⟩
  · intro eps heps hs p hp
    exact (hHessian eps heps hs p hp).trans hBC
  · intro e he h hh hs p hp
    exact (hSecondW e he h hh hs p hp).trans hBsC
  · intro p hp
    exact (hVB p hp).trans hCtC
  · intro p hp
    exact (hSNorm p hp).trans hCnC
  · intro p hp e he
    have hGood := peano_countable_of_littleO (u := (w : Point n → ℝ))
      (G := spatialD w) (p := p) (hSPeano p hp)
    exact (peano_good_direction_bound w.continuous (by norm_num : (0 : ℝ) < 1/512)
      hLocalSecond (hSSub hp) hGood e he).trans hBsC
  · intro p hp
    exact auto_measurableJet_point_equation hwu hF hu (hVc.mono hQTime) hTimeQ hsol
      (hSSub hp) (hSPeano p hp)

end Yau.LeafProofs.L05AutonomousAux
