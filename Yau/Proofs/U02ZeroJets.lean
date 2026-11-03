import Yau.Geometry.Polynomial

/-! A finite zero jet gives the higher-order Schwarz estimate used for the
actual conjugacy error. The proof uses the mean-value inequality and the
native Banach-valued Schwarz lemma, without a supplied Taylor remainder. -/

open scoped Topology ContDiff
open Filter Asymptotics Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem zeroJet_value_zero {n d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ComplexVector n → F}
    (hjet : ∀ k ≤ d, iteratedFDeriv ℂ k f 0 = 0) : f 0 = 0 := by
  apply norm_eq_zero.mp
  have hh := congrArg norm (hjet 0 (Nat.zero_le d))
  simpa only [norm_iteratedFDeriv_zero, norm_zero] using hh

theorem zeroJet_isLittleO {n d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {f : ComplexVector n → F} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℂ ∞ f (ball 0 R))
    (hjet : ∀ k ≤ d, iteratedFDeriv ℂ k f 0 = 0) :
    f =o[𝓝 (0 : ComplexVector n)] (fun z => ‖z‖ ^ d) := by
  induction d generalizing F with
  | zero =>
    have hzero : f 0 = 0 := zeroJet_value_zero hjet
    have hc := hf.continuousOn.continuousAt (ball_mem_nhds _ hR)
    simpa only [pow_zero, isLittleO_one_iff, hzero] using hc.tendsto
  | succ d ih =>
    have hfd : ContDiffOn ℂ ∞ (fderiv ℂ f) (ball 0 R) :=
      (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.2
    have hjd : ∀ k ≤ d, iteratedFDeriv ℂ k (fderiv ℂ f) 0 = 0 := by
      intro k hk
      apply norm_eq_zero.mp
      rw [norm_iteratedFDeriv_fderiv, hjet (k + 1) (by omega), norm_zero]
    have hsmall := ih hfd hjd
    have hd : DifferentiableOn ℂ f (ball 0 R) :=
      (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.1
    have hder : ∀ z ∈ ball (0 : ComplexVector n) R,
        HasFDerivWithinAt f (fderiv ℂ f z) (ball 0 R) z := by
      intro z hz
      exact ((hd z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasFDerivAt.hasFDerivWithinAt
    have hsmall' : fderiv ℂ f =o[𝓝[ball 0 R] (0 : ComplexVector n)]
        (fun z => ‖z - 0‖ ^ d) := by
      simpa only [sub_zero] using hsmall.mono
        (nhdsWithin_le_nhds : 𝓝[ball 0 R] (0 : ComplexVector n) ≤ 𝓝 0)
    have hsucc := (convex_ball (0 : ComplexVector n) R).isLittleO_pow_succ
      (mem_ball_self hR) hder hsmall'
    simpa only [zeroJet_value_zero hjet, sub_zero,
      nhdsWithin_eq_nhds.2 (ball_mem_nhds (0 : ComplexVector n) hR)] using hsucc

theorem zeroJet_schwarz_bound {n d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {f : ComplexVector n → F} {R A : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℂ ∞ f (ball 0 R))
    (hjet : ∀ k ≤ d, iteratedFDeriv ℂ k f 0 = 0)
    (hbound : ∀ z ∈ ball (0 : ComplexVector n) R, ‖f z‖ ≤ A)
    {z : ComplexVector n} (hz : ‖z‖ < R) :
    ‖f z‖ ≤ A * (‖z‖ / R) ^ (d + 1) := by
  have hzero := zeroJet_value_zero hjet
  have hd : DifferentiableOn ℂ f (ball 0 R) :=
    (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hf |>.1
  have hm : Set.MapsTo f (ball 0 R) (closedBall (f 0) A) := by
    intro w hw
    simpa only [mem_closedBall, hzero, dist_zero_right] using hbound w hw
  have hsmall := zeroJet_isLittleO hR hf hjet
  have hh := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    hd hm (by simpa only [hzero, sub_zero] using hsmall)
    (by simpa using hz : z ∈ ball (0 : ComplexVector n) R)
  simpa only [hzero, dist_zero_right] using hh

end Yau.NodeProofs.U02Proof
