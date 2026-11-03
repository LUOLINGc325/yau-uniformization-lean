import Yau.Proofs.V02DiscDbarEnergy
import Yau.Proofs.V03OuterBoundary
import Yau.Proofs.V03Pluriharmonic

/-! The existing positive Fourier projection gives a genuine harmonic
extension of every real smooth boundary trace, with its constant mode retained. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

def realDiscTrace (u : ℂ → ℝ) (θ : ℝ) : ℝ := u (circlePoint θ)

theorem realDiscTrace_contDiff {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiff ℝ ∞ (realDiscTrace u) := by
  apply contDiffOn_univ.mp
  exact hu.comp V03Proof.circlePoint_contDiff.contDiffOn
    (fun θ _ => V03Proof.circlePoint_mem_closedBall θ)

theorem realDiscTrace_periodic (u : ℂ → ℝ) :
    Function.Periodic (realDiscTrace u) (2 * Real.pi) := by
  intro θ
  unfold realDiscTrace
  rw [V03Proof.circlePoint_periodic]

def realHarmonicExtension (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (V03Proof.outerExponent (realDiscTrace u) 1 z).re

theorem realHarmonicExtension_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (realHarmonicExtension u) (Metric.closedBall (0 : ℂ) 1) :=
  Complex.reCLM.contDiff.comp_contDiffOn
    ((V03Proof.outerExponent_contDiffOn (realDiscTrace_contDiff hu)
      (realDiscTrace_periodic u) 1).restrict_scalars ℝ)

theorem realHarmonicExtension_boundary {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    realHarmonicExtension u (circlePoint θ) = u (circlePoint θ) := by
  simpa only [realHarmonicExtension, Nat.cast_one, one_mul, realDiscTrace] using
    V03Proof.outerExponent_re_boundary (realDiscTrace_contDiff hu)
      (realDiscTrace_periodic u) 1 θ

theorem realHarmonicExtension_laplacian {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyRealLaplacian (realHarmonicExtension u) z = 0 := by
  have hF : ContDiffAt ℂ 2 (V03Proof.outerExponent (realDiscTrace u) 1) z :=
    ((V03Proof.outerExponent_contDiffOn (realDiscTrace_contDiff hu)
      (realDiscTrace_periodic u) 1).contDiffAt (discEnergy_closedBall_mem_nhds hz)).of_le (by simp)
  have hH : ContDiffAt ℝ 2 (realHarmonicExtension u) z :=
    (hF.restrict_scalars ℝ).continuousLinearMap_comp Complex.reCLM
  have hm := V03Proof.mixedWirt_re_holomorphic_zero hF (1 : ℂ)
  change (wirt (fun w => wirtBar (fun w' => (realHarmonicExtension u w' : ℂ)) w 1) z 1).re = 0 at hm
  rw [V03Proof.mixedWirt_real_diagonal hH] at hm
  simp only [smul_eq_mul, mul_one] at hm
  have hD := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold discEnergyRealLaplacian
  rw [discEnergyPartial_twice_eq _ _ _ hz, discEnergyPartial_twice_eq _ _ _ hz,
    fderiv_clm_apply hD (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hD (differentiableAt_const Complex.I)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add]
  linarith

end Yau.Blueprint.V02Proof
