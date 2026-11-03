import Yau.LeafProofs.L05AutonomousSecondFTC
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Interval
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- Actual uniform convergence of the first and second Frechet derivatives of
genuine smooth functions passes their literal gradient FTC to the limit. -/
theorem auto_gradient_ftc_limit {n : ℕ} {R : ℝ}
    (f : ℕ → Space n → ℝ) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (G : Space n → (Space n →L[ℝ] ℝ))
    (B : Space n → (Space n →L[ℝ] Space n →L[ℝ] ℝ))
    (hGrad : TendstoUniformlyOn (fun j => fderiv ℝ (f j)) G atTop (Metric.closedBall 0 R))
    (hHess : TendstoUniformlyOn (fun j => fderiv ℝ (fderiv ℝ (f j))) B atTop (Metric.closedBall 0 R))
    {x y : Space n} (hx : x∈Metric.closedBall 0 R) (hy : y∈Metric.closedBall 0 R) :
    G y-G x=∫ s in (0 : ℝ)..1, B (x+s • (y-x)) (y-x) := by
  let h := y-x
  let path : ℝ → Space n := fun s => x+s • h
  have hPath : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  have hPathMem : ∀ s∈Set.uIcc (0 : ℝ) 1, path s∈Metric.closedBall 0 R := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hm := (convex_closedBall (0 : Space n) R) hx hy (sub_nonneg.mpr hs.2) hs.1
      (sub_add_cancel 1 s)
    convert hm using 1 <;> dsimp only [path,h] <;> module
  have hCont (j : ℕ) : Continuous (fun s => fderiv ℝ (fderiv ℝ (f j)) (path s) h) :=
    (((((hf j).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).continuous).comp hPath
  have hFTC (j : ℕ) : (∫ s in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ (f j)) (path s) h)=
      fderiv ℝ (f j) y-fderiv ℝ (f j) x := by
    have hg := (hf j).fderiv_right (m := ∞) (by simp)
    have hDeriv (s : ℝ) : HasDerivAt (fun r => fderiv ℝ (f j) (path r))
        (fderiv ℝ (fderiv ℝ (f j)) (path s) h) s := by
      have hline : ContDiff ℝ ∞ (fun r : ℝ => fderiv ℝ (f j) (x+r • h)) :=
        hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
      have hactual := (hg.differentiable (by simp) (x+s • h)).deriv_comp_add_smul
      simpa only [path,hactual] using (hline.differentiable (by simp) s).hasDerivAt
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDeriv s)
      ((hCont j).intervalIntegrable 0 1)
    have hxy : x+(y-x)=y := by abel
    simpa only [path,h,one_smul,zero_smul,add_zero,hxy] using hh
  let ev : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] (Space n →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) h
  have hEval := ev.uniformContinuous.comp_tendstoUniformlyOn hHess
  have hAlong := (hEval.comp path).mono hPathMem
  change TendstoUniformlyOn (fun j s => fderiv ℝ (fderiv ℝ (f j)) (path s) h)
    (fun s => B (path s) h) atTop (Set.uIcc (0 : ℝ) 1) at hAlong
  have hIntegral := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (Eventually.of_forall fun j => (hCont j).continuousOn) hAlong
  have hId : (fun j => ∫ s in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ (f j)) (path s) h)=
      (fun j => fderiv ℝ (f j) y-fderiv ℝ (f j) x) := funext hFTC
  rw [hId] at hIntegral
  have hGradient := (hGrad.tendsto_at hy).sub (hGrad.tendsto_at hx)
  have hEq := tendsto_nhds_unique hIntegral hGradient
  exact hEq.symm

end Yau.LeafProofs.L05AutonomousAux
