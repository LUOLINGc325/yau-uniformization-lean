import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

open Filter Asymptotics Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L05Aux

/-- The actual local second Frechet Taylor expansion needs no quantitative C2 budget. -/
theorem perturb_actual_second_peano {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (fun x => f x - f 0 - fderiv ℝ f 0 x -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 x x) =o[𝓝 0] (fun x => ‖x‖ ^ 2) := by
  let l := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hB : ∀ v w, B v w = B w v := hf.isSymmSndFDerivAt (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ f) B 0 :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hEventually : ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hEventually
  let R : V → ℝ := fun y => f y - f 0 - l y - (1 / 2 : ℝ) * B y y
  let R' : V → V →L[ℝ] ℝ := fun y => fderiv ℝ f y - l - B y
  have hQ (y : V) : HasFDerivAt (fun z => (1 / 2 : ℝ) * B z z) (B y) y := by
    have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_mul (1 / 2 : ℝ)
    convert h using 1
    · funext z; rfl
    ext v
    change B y v = (1 / 2 : ℝ) * (B y v + B v y)
    rw [hB v y]
    ring
  have hR (y : V) (hy : y ∈ ball (0 : V) r) : HasFDerivAt R (R' y) y := by
    exact (((hBall hy).hasFDerivAt.sub_const (f 0)).sub l.hasFDerivAt).sub (hQ y)
  have hSmall : R' =o[𝓝 (0 : V)] (fun y => ‖y‖ ^ 1) := by
    simpa only [R', l, sub_zero, pow_one] using hD.isLittleO.norm_right
  have hWithin : 𝓝[ball (0 : V) r] 0 = 𝓝 (0 : V) :=
    nhdsWithin_eq_nhds.mpr (ball_mem_nhds _ hr)
  have hSmallWithin : R' =o[𝓝[ball (0 : V) r] 0] (fun y => ‖y - 0‖ ^ 1) := by
    simpa only [hWithin, sub_zero] using hSmall
  have hFinal := (convex_ball (0 : V) r).isLittleO_pow_succ (n := 1) (mem_ball_self hr)
    (fun y hy => (hR y hy).hasFDerivWithinAt) hSmallWithin
  have hR0 : R 0 = 0 := by simp [R]
  rw [hWithin, hR0] at hFinal
  simpa only [R, sub_zero] using hFinal

/-- A continuous quadratic form which is little-o of the squared norm vanishes. -/
theorem perturb_actual_quadratic_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (h : (fun x => B x x) =o[𝓝 (0 : V)] (fun x => ‖x‖ ^ 2)) :
    ∀ v, B v v = 0 := by
  intro v
  by_cases hv : v = 0
  · subst v; simp
  have hvN : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 (0 : V)) := by
    have hc : Continuous (fun t : ℝ => t • v) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := (h.comp_tendsto ht).tendsto_div_nhds_zero
  have heq : (fun t : ℝ => B (t • v) (t • v) / ‖t • v‖ ^ 2) =ᶠ[𝓝[≠] 0]
      (fun _ => B v v / ‖v‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    simp only [map_smul, smul_apply, smul_eq_mul, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [ht0, hvN]
  have hz : B v v / ‖v‖ ^ 2 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr' heq)
  exact (div_eq_zero_iff.mp hz).resolve_right hvN

end Yau.LeafProofs.L05Aux
