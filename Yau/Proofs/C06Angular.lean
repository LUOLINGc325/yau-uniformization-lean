import Yau.LeafProofs.L22Circle
import Yau.LeafProofs.L22Locality
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped Topology ContDiff
open Filter Set MeasureTheory

noncomputable section

namespace Yau.Proofs.C06Aux

open Yau Yau.LeafProofs Yau.LeafProofs.L22Aux

variable {n : ℕ}

/-- Finite C² regularity suffices for differentiating the angular mean. -/
theorem angularMean_hasDerivAt {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ 2 f) (z v : ComplexVector n) (r : ℝ) :
    HasDerivAt (angularLineMean f z v)
      (circleAverage (fun θ => fderiv ℝ f
        (z + r • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v))) r := by
  have hq : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I) • v) := by fun_prop
  have hpath : Continuous (fun p : ℝ × ℝ =>
      z + p.1 • (Complex.exp (p.2 * Complex.I) • v)) := by fun_prop
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  apply (L08_hasDerivAt_intervalIntegral (hf.continuous.comp hpath)
    ((hdf.comp hpath).clm_apply (hq.comp continuous_snd))
    (fun s θ => ?_) 0 (2 * Real.pi) r).const_mul ((2 * Real.pi)⁻¹)
  convert (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const (Complex.exp (θ * Complex.I) • v)).const_add z) using 1 <;>
    simp only [Function.comp_def, id_eq, one_smul]

theorem angularMean_derivative_hasDerivAt {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ 2 f) (z v : ComplexVector n) (r : ℝ) :
    HasDerivAt
      (fun s => circleAverage (fun θ => fderiv ℝ f
        (z + s • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v)))
      (circleAverage (fun θ => fderiv ℝ (fderiv ℝ f)
        (z + r • (Complex.exp (θ * Complex.I) • v))
        (Complex.exp (θ * Complex.I) • v) (Complex.exp (θ * Complex.I) • v))) r := by
  have hq : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I) • v) := by fun_prop
  have hpath : Continuous (fun p : ℝ × ℝ =>
      z + p.1 • (Complex.exp (p.2 * Complex.I) • v)) := by fun_prop
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hqc : Continuous (fun p : ℝ × ℝ => Complex.exp (p.2 * Complex.I) • v) :=
    hq.comp continuous_snd
  apply (L08_hasDerivAt_intervalIntegral
    ((hdf.continuous.comp hpath).clm_apply hqc)
    (((hdf.continuous_fderiv (by norm_num)).comp hpath).clm_apply hqc |>.clm_apply hqc)
    (fun s θ => ?_) 0 (2 * Real.pi) r).const_mul ((2 * Real.pi)⁻¹)
  have hd := (hdf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const (Complex.exp (θ * Complex.I) • v)).const_add z)
  convert hd.clm_apply (hasDerivAt_const s (Complex.exp (θ * Complex.I) • v)) using 1 <;>
    simp only [Function.comp_def, id_eq, one_smul, ContinuousLinearMap.map_zero, add_zero]

theorem angularMean_second_deriv {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ 2 f) (z v : ComplexVector n) :
    deriv (deriv (angularLineMean f z v)) 0 =
      (fderiv ℝ (fderiv ℝ f) z v v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v)) / 2 := by
  have heq : deriv (angularLineMean f z v) =
      (fun r => circleAverage (fun θ => fderiv ℝ f
        (z + r • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v))) :=
    funext (fun r => (angularMean_hasDerivAt hf z v r).deriv)
  rw [heq, (angularMean_derivative_hasDerivAt hf z v 0).deriv]
  simp only [zero_smul, add_zero]
  exact circleAverage_bilinear _ _

/-- Local finite C² data can be multiplied by a genuine bump without changing its germ. -/
theorem exists_contDiff_two_extension {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) :
    ∃ g : ComplexVector n → ℝ, ContDiff ℝ 2 g ∧ g =ᶠ[𝓝 z] f := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by norm_num))
  let b : ContDiffBump z :=
    { rIn := R / 4
      rOut := R / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g : ComplexVector n → ℝ := fun x => b x * f x
  refine ⟨g, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Metric.closedBall z (R / 2)
    · have hx' : x ∈ Metric.ball z R :=
        Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
      exact b.contDiffAt.mul (hball hx')
    · have heq : g =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(Metric.isClosed_closedBall (x := z) (ε := R / 2)).isOpen_compl.mem_nhds hx] with y hy
        have hy' : R / 2 ≤ dist y z := (lt_of_not_ge (Metric.mem_closedBall.not.mp hy)).le
        simp only [g, b.zero_of_le_dist hy', zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp only [g, hx, one_mul, Pi.one_apply]

end Yau.Proofs.C06Aux
