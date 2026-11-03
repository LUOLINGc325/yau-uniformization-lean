import Yau.LeafProofs.L05AutonomousGradientFTCBuffered
import Yau.LeafProofs.L05AutonomousSpatialHessianUniform
import Yau.LeafProofs.L05AutonomousGradientFromMollifier
import Yau.LeafProofs.L05AutonomousActualDerivatives
import Yau.LeafProofs.L05AutonomousHarnackOscillation

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Interval BoundedContinuousFunction Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux
local instance autoSchauderReconstruction_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSchauderReconstruction_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSchauderReconstruction_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoSchauderReconstruction_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Pure reconstruction of actual native Schauder regularity. The continuous
bilinear field is tied to the original source by its genuine a.e. finite
second-difference limits; the actual first and second FTCs are proved here
from canonical smoothing. No original second derivative is assumed. -/
theorem auto_schauder_from_actual_directional_limits (n : ℕ)
    (eta B0 MH MV : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (hB0 : 0 ≤ B0) (hMH : 0 ≤ MH) (hMV : 0 ≤ MV) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : Point n →ᵇ ℝ),
      UniformContinuous (w : Point n → ℝ) → ‖w‖ ≤ 1 →
      ∀ u : Point n → ℝ, EqOn (w : Point n → ℝ) u (unitClosed n) →
        ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
      (∀ (eps : ℝ) (heps : 0 < eps), eps < 1/256 →
        ∀ p∈autoClosed (0 : Space n) (45/64) 0,
          ‖secondFDerivMatrix (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1‖ ≤ B0) →
      (∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h≠0 → |h| < 1/512 →
        ∀ p∈autoClosed (0 : Space n) (11/16) 0, |autoSecond w e h p| ≤ B0) →
      ∀ HB : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ),
        StronglyMeasurable HB → ContinuousOn HB (autoClosed (0 : Space n) (9/16) 0) →
        (∀ p v z, HB p v z=HB p z v) →
        HolderBound eta (autoClosed (0 : Space n) (9/16) 0) HB MH →
        (∀ e : Space n, ‖e‖=1 →
          ∀ᵐ p ∂((volume : Measure (Point n)).restrict (autoOpen (0 : Space n) (9/16) 0)),
            Tendsto (fun h : ℝ => autoSecond w e h p) (𝓝[>] 0) (𝓝 (HB p e e))) →
      ∀ V : Point n → ℝ, ContinuousOn V (autoClosed (0 : Space n) (15/16) 0) →
        HolderBound eta (autoClosed (0 : Space n) (9/16) 0) V MV →
        (∀ x∈Metric.closedBall (0 : Space n) (15/16),
          ∀ a∈Icc (-(15/16 : ℝ)^2) 0, ∀ b∈Icc (-(15/16 : ℝ)^2) 0,
            u (x,b)-u (x,a)=∫ t in a..b, V (x,t)) →
        SchauderBound eta (backward (1/2)) u C := by
  obtain ⟨CG,hCG,hGradient⟩ := auto_gradient_from_spatial_mollifiers n
  obtain ⟨C,hC,hQ⟩ := auto_schauder_from_buffered_ftc (n := n)
    (r := 1/2) (R := 17/32) (eta := eta) (M0 := 1) (M1 := CG*(1+B0)) (M2 := MH) (Mt := MV)
    (by norm_num) (by norm_num) heta heta1 (by norm_num)
    (mul_nonneg hCG.le (by positivity)) hMH hMV
  refine ⟨C,hC,?_⟩
  intro w hw hw1 u hwu hu huBound hMoll hSecond HB hHB hHBC hSym hHBHolder hLimit V hVC hVHolder hTime
  obtain ⟨hGC,hGN,hGNative,hGLip,hGQuadratic,hScalarW,hGradLimit⟩ :=
    hGradient B0 hB0 w hw hw1 hMoll
  let eps : ℕ → ℝ := autoDyadicStep (1/512)
  have heps (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (by norm_num) j
  let steps : ℕ → ℝ := autoDyadicStep (1/1024)
  have hsteps (j : ℕ) : 0 < steps j := auto_dyadicStep_pos (by norm_num) j
  have hStepsSmall (j : ℕ) : |steps j| < 1/512 := by
    rw [abs_of_pos (hsteps j)]
    exact (auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/1024) j).trans_lt (by norm_num)
  have hOpenSub : autoOpen (0 : Space n) (9/16) 0 ⊆ autoClosed (0 : Space n) (11/16) 0 := by
    intro p hp
    exact (autoClosed_subset (r := (9/16 : ℝ)) (R := 11/16) 0
      (by norm_num) (by norm_num) 0)
      ⟨Metric.ball_subset_closedBall hp.1,⟨hp.2.1.le,hp.2.2.le⟩⟩
  have hStepLimit : ∀ e : Space n, ‖e‖=1 →
      ∀ᵐ p ∂((volume : Measure (Point n)).restrict (autoOpen (0 : Space n) (9/16) 0)),
        Tendsto (fun j => autoSecond w e (steps j) p) atTop (𝓝 (HB p e e)) := by
    intro e he
    filter_upwards [hLimit e he] with p hp
    exact hp.comp (tendsto_nhdsWithin_iff.mpr
      ⟨auto_dyadicStep_tendsto _,Eventually.of_forall hsteps⟩)
  have hHessLimit := auto_spatial_mollify_hessian_uniform
    (r := 17/32) (R := 9/16) (by norm_num) (by norm_num) w hw HB hHB hHBC hSym
    steps hsteps (auto_dyadicStep_tendsto _) hB0
    (fun e he j p hp => hSecond e he _ (hsteps j).ne' (hStepsSmall j) p (hOpenSub hp))
    hStepLimit hHBHolder.2.1 eps heps (auto_dyadicStep_tendsto _) (fun j => by
      have hj := auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/512) j
      change (17/32 : ℝ)+autoDyadicStep (1/512) j < 9/16
      linarith only [hj])
  have hSmallG : autoClosed (0 : Space n) (17/32) 0 ⊆ autoClosed (0 : Space n) (5/8) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hSmallH : autoClosed (0 : Space n) (17/32) 0 ⊆ autoClosed (0 : Space n) (9/16) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hSmallV : autoClosed (0 : Space n) (17/32) 0 ⊆ autoClosed (0 : Space n) (15/16) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hK : autoDerivativeClosed (n := n) (17/32)=autoClosed (0 : Space n) (17/32) 0 := by
    simp only [autoDerivativeClosed,autoClosed,zero_sub]
  have hSmallUnit : autoClosed (0 : Space n) (17/32) 0 ⊆ unitClosed n := by
    have hOne : autoClosed (0 : Space n) (1 : ℝ) 0=unitClosed n := by
      norm_num [autoClosed,unitClosed,Yau.Parabolic.cylinder]
    rw [← hOne]
    exact autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hGradSmall : TendstoUniformlyOn
      (fun j => spatialD (autoSpatialMollify (eps j) (heps j) w)) (spatialD w)
      atTop (autoClosed (0 : Space n) (17/32) 0) := hGradLimit.mono hSmallG
  have hGradientFTC := auto_gradient_ftc_from_uniform_spatial_jets w hw eps heps HB hGradSmall hHessLimit
  have hGCsmall : ContinuousOn (spatialD w) (autoDerivativeClosed (n := n) (17/32)) := by
    rw [hK]
    exact hGC.mono hSmallG
  have hHBCsmall : ContinuousOn HB (autoDerivativeClosed (n := n) (17/32)) := by
    rw [hK]
    exact hHBC.mono hSmallH
  have hVCsmall : ContinuousOn V (autoDerivativeClosed (n := n) (17/32)) := by
    rw [hK]
    exact hVC.mono hSmallV
  have huSmall : ContinuousOn u (autoDerivativeClosed (n := n) (17/32)) := by
    rw [hK]
    exact hu.mono hSmallUnit
  have hHBsmall : HolderBound eta (autoDerivativeClosed (n := n) (17/32)) HB MH := by
    rw [hK]
    exact ⟨hHBHolder.1,(fun p hp => hHBHolder.2.1 p (hSmallH hp)),
      fun p hp q hq => hHBHolder.2.2 p (hSmallH hp) q (hSmallH hq)⟩
  have hVsmall : HolderBound eta (autoDerivativeClosed (n := n) (17/32)) V MV := by
    rw [hK]
    exact ⟨hVHolder.1,(fun p hp => hVHolder.2.1 p (hSmallH hp)),
      fun p hp q hq => hVHolder.2.2 p (hSmallH hp) q (hSmallH hq)⟩
  apply hQ u (spatialD w) HB V huSmall hGCsmall hHBCsmall hVCsmall
  · intro t ht x hx h hpath
    have hxC := Metric.ball_subset_closedBall hx
    have hyC : x+h∈Metric.closedBall (0 : Space n) (17/32) := by
      apply Metric.ball_subset_closedBall
      simpa only [one_smul] using hpath 1 (by norm_num)
    have hpx : (x,t)∈autoClosed (0 : Space n) (17/32) 0 := ⟨hxC,by simpa only [zero_sub] using ht⟩
    have hpy : (x+h,t)∈autoClosed (0 : Space n) (17/32) 0 := ⟨hyC,by simpa only [zero_sub] using ht⟩
    rw [← hwu (hSmallUnit hpy),← hwu (hSmallUnit hpx)]
    simpa only [add_sub_cancel_left] using
      hScalarW t (by simpa only [zero_sub] using (hSmallG hpx).2)
        x (hSmallG hpx).1 (x+h) (hSmallG hpy).1
  · intro t ht x hx h hpath
    have hyC : x+h∈Metric.closedBall (0 : Space n) (17/32) := by
      apply Metric.ball_subset_closedBall
      simpa only [one_smul] using hpath 1 (by norm_num)
    simpa only [add_sub_cancel_left] using
      hGradientFTC t ht x (Metric.ball_subset_closedBall hx) (x+h) hyC
  · intro x hx a ha b hb
    have hxC := Metric.closedBall_subset_closedBall (show (17/32 : ℝ) ≤ 15/16 by norm_num)
      (Metric.ball_subset_closedBall hx)
    have haC : a∈Icc (-(15/16 : ℝ)^2) 0 := ⟨by linarith only [ha.1],ha.2⟩
    have hbC : b∈Icc (-(15/16 : ℝ)^2) 0 := ⟨by linarith only [hb.1],hb.2⟩
    exact hTime x hxC a haC b hbC
  · intro p hp
    exact huBound p (hSmallUnit (hK ▸ hp))
  · intro p hp
    exact hGN p (hSmallG (hK ▸ hp))
  · exact hHBsmall
  · exact hVsmall

end Yau.LeafProofs.L05AutonomousAux
