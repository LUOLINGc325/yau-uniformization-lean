import Yau.Proofs.C07CurveConcatPath

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07CurveConcatAux

open Yau Set Filter

variable {n : ℕ} {M : ComplexManifold n}

theorem realTangentDerivative_eq_deriv_chart {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) (t : ℝ) :
    realTangentDerivative γ t = deriv (fun s => chartPt (γ t) (γ s)) t := by
  have h := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := γ t)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  unfold realTangentDerivative
  rw [h]
  rfl

/-- Local affine reparameterization by slope two multiplies the actual
speed by two, outside the original finite corner set. -/
theorem curveSpeed_double_affine (k : HermitianField M) {x y u v : M.Carrier}
    (γ : PiecewiseC1Curve x y) (ζ : PiecewiseC1Curve u v) (b t : ℝ)
    (heq : ζ.toFun =ᶠ[𝓝 t] (fun s => γ (2 * s + b)))
    (hb : 2 * t + b ∉ γ.breakpoints) :
    curveSpeed k ζ t = 2 * curveSpeed k γ (2 * t + b) := by
  let H : ℝ → ComplexVector n := fun s => chartPt (γ (2 * t + b)) (γ s)
  have hpt : ζ t = γ (2 * t + b) := heq.self_of_nhds
  have hd : DifferentiableAt ℝ H (2 * t + b) :=
    (γ.piecewise_c1 _ hb).differentiableAt (by norm_num)
  have hAff : HasDerivAt (fun s : ℝ => 2 * s + b) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).add_const b
  have hcoord : (fun s => chartPt (ζ t) (ζ s)) =ᶠ[𝓝 t] (fun s => H (2 * s + b)) := by
    filter_upwards [heq] with s hs
    change chartPt (ζ t) (ζ s) = chartPt (γ (2 * t + b)) (γ (2 * s + b))
    rw [hpt, hs]
  have htwo : fderiv ℝ H (2 * t + b) 2 = (2 : ℝ) • deriv H (2 * t + b) := by
    simpa only [smul_eq_mul, mul_one, fderiv_apply_one_eq_deriv] using
      (fderiv ℝ H (2 * t + b)).map_smul (2 : ℝ) (1 : ℝ)
  have hComp : HasDerivAt (fun s => H (2 * s + b))
      ((2 : ℝ) • deriv H (2 * t + b)) t := by
    convert! hd.hasFDerivAt.comp_hasDerivAt t hAff using 1
    exact htwo.symm
  have hder : HasDerivAt (fun s => chartPt (ζ t) (ζ s))
      ((2 : ℝ) • deriv H (2 * t + b)) t := hComp.congr_of_eventuallyEq hcoord
  have hvec : realTangentDerivative ζ t = (2 : ℂ) • realTangentDerivative γ (2 * t + b) := by
    rw [realTangentDerivative_eq_deriv_chart, realTangentDerivative_eq_deriv_chart, hder.deriv]
    rfl
  let q := hermitianNormSq (k (γ (2 * t + b))) (realTangentDerivative γ (2 * t + b))
  have hscale : hermitianNormSq (k (γ (2 * t + b)))
      ((2 : ℂ) • realTangentDerivative γ (2 * t + b)) = 4 * q := by
    simp [q, hermitianNormSq, HermitianInnerProduct.map_smul_left,
      HermitianInnerProduct.map_smul_right, Complex.mul_re] <;> ring
  unfold curveSpeed
  rw [hvec, hpt, hscale]
  change Real.sqrt (2 * (4 * q)) = 2 * Real.sqrt (2 * q)
  calc
    _ = Real.sqrt (4 * (2 * q)) := congrArg Real.sqrt (by ring)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

theorem concat_speed_left (k : HermitianField M) {x y z : M.Carrier}
    (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t < 1 / 2) (hb : 2 * t ∉ γ.breakpoints) :
    curveSpeed k (concatPiecewise γ η) t = 2 * curveSpeed k γ (2 * t) := by
  have heq : (concatPiecewise γ η).toFun =ᶠ[𝓝 t] (fun s => γ (2 * s + 0)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    simpa only [concatPiecewise, add_zero] using concatPath_left γ η hs.le
  simpa only [add_zero] using curveSpeed_double_affine k γ (concatPiecewise γ η) 0 t heq (by simpa using hb)

theorem concat_speed_right (k : HermitianField M) {x y z : M.Carrier}
    (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : 1 / 2 < t) (hb : 2 * t - 1 ∉ η.breakpoints) :
    curveSpeed k (concatPiecewise γ η) t = 2 * curveSpeed k η (2 * t - 1) := by
  have heq : (concatPiecewise γ η).toFun =ᶠ[𝓝 t] (fun s => η (2 * s + (-1))) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simpa only [concatPiecewise, sub_eq_add_neg] using concatPath_right γ η hs.le
  simpa only [sub_eq_add_neg] using curveSpeed_double_affine k η (concatPiecewise γ η) (-1) t heq (by simpa only [sub_eq_add_neg] using hb)

end Yau.Proofs.C07CurveConcatAux
