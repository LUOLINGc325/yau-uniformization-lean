import Yau.LeafProofs.L22Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Poisson

noncomputable section
open Filter Metric Complex InnerProductSpace
open scoped Topology

namespace Yau.NodeProofs.P02Aux
open Yau

theorem circleAverage_eq_real_circleAverage (F : ℂ → ℝ) :
    Yau.circleAverage (fun θ => F (Complex.exp (θ*Complex.I))) =
      Real.circleAverage F 0 1 := by
  simp only [Yau.circleAverage, Real.circleAverage_def, circleMap_zero,
    Complex.ofReal_one, one_mul, smul_eq_mul]

def poissonApproxComplex (F : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ξ => herglotzRieszKernel 0 ((r : ℂ)*z) ξ • (F ξ : ℂ)) 0 1

def poissonApprox (F : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  (poissonApproxComplex F r z).re

theorem poissonApprox_eq (F : ℂ → ℝ) (hF : CircleIntegrable F 0 1)
    (r : ℝ) (z : ℂ) (hz : (r : ℂ)*z ∉ sphere 0 (1 : ℝ)) :
    poissonApprox F r z = Real.circleAverage (fun ξ => poissonKernel 0 ((r : ℂ)*z) ξ * F ξ) 0 1 := by
  have H := re_circleAverage_herglotzRieszKernel_smul (R := 1) (w := (r : ℂ)*z)
    hF (by simpa only [abs_one] using hz)
  simpa only [poissonApprox,poissonApproxComplex, ← poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, Pi.smul_def, Pi.mul_def, smul_eq_mul] using H

theorem poissonKernel_unit_circle (r : ℝ) (z ξ : ℂ)
    (hz : ‖z‖ = 1) (hξ : ‖ξ‖ = 1) :
    poissonKernel 0 ((r : ℂ)*z) ξ = (1-r^2)/‖ξ-(r : ℂ)*z‖^2 := by
  simp only [poissonKernel_def,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    hz,hξ,mul_one,one_pow,sq_abs]

theorem poissonKernel_unit_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (z ξ : ℂ) (hz : ‖z‖ = 1) (hξ : ‖ξ‖ = 1) :
    0 ≤ poissonKernel 0 ((r : ℂ)*z) ξ := by
  rw [poissonKernel_unit_circle r z ξ hz hξ]
  exact div_nonneg (by nlinarith) (sq_nonneg _)

theorem poissonKernel_mass_one (w : ℂ) (hw : ‖w‖ < 1) :
    Real.circleAverage (poissonKernel 0 w) 0 1 = 1 := by
  have H := (harmonicOnNhd_const (1 : ℝ) :
    HarmonicOnNhd (fun _ : ℂ => (1 : ℝ)) (closedBall 0 1)).circleAverage_poissonKernel_smul
      (by simpa only [mem_ball,dist_zero_right] using hw : w ∈ ball 0 1)
  simpa only [Pi.smul_def,smul_eq_mul,Pi.mul_def,mul_one] using H

theorem poissonApprox_harmonic (F : ℂ → ℝ) (hF : ContinuousOn F (sphere 0 1))
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HarmonicOnNhd (poissonApprox F r) (closedBall 0 1) := by
  have hFC : CircleIntegrable (fun ξ => (F ξ : ℂ)) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_one,Function.comp_def] using Complex.continuous_ofReal.comp_continuousOn hF
  have HA := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hFC
  intro z hz
  have hnorm : ‖(r : ℂ)*z‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    nlinarith
  have hoff : (r : ℂ)*z ∈ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    simpa only [Set.mem_compl_iff,mem_sphere,dist_zero_right,abs_one] using ne_of_lt hnorm
  have Hcomp := (HA _ hoff).comp (analyticAt_const.mul analyticAt_id)
  exact Hcomp.harmonicAt_re

theorem poissonApprox_zero (F : ℂ → ℝ) (hF : CircleIntegrable F 0 1) (r : ℝ) :
    poissonApprox F r 0 = Real.circleAverage F 0 1 := by
  rw [poissonApprox_eq F hF r 0 (by simp)]
  apply Real.circleAverage_congr_sphere
  intro ξ hξ
  have hn : ‖ξ‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hξ
  simp [poissonKernel_def,hn]

end Yau.NodeProofs.P02Aux
