import Yau.Proofs.D06CircleFourierRepresentative
import Yau.Proofs.D06DiscreteYoung
import Yau.Proofs.D06HardyTraceShift

/-! Multiplication by the continuous Fourier representative of a Sobolev
function has the actual convolution coefficients on the same L² space. -/

open scoped ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleProduct_mem (f g : CircleL2) :
    MemLp (fun t => f t * circleFourierRepresentative g t) 2 hardyCircleMeasure :=
  (Lp.memLp f).fun_mul (ContinuousMap.memLp (p := ⊤) (μ := hardyCircleMeasure) ℂ
    (circleFourierRepresentative g))

def circleProduct (f g : CircleL2) : CircleL2 :=
  (circleProduct_mem f g).toLp (fun t => f t * circleFourierRepresentative g t)

theorem circleProduct_ae (f g : CircleL2) (hg : CircleSobolev 1 g) :
    (circleProduct f g : HardyCircle → ℂ) =ᵐ[hardyCircleMeasure] fun t => f t * g t := by
  filter_upwards [(circleProduct_mem f g).coeFn_toLp, circleFourierRepresentative_ae hg] with t hp hg
  exact hp.trans (by rw [hg])

theorem circleFourierRepresentative_hasSum {g : CircleL2} (hg : CircleSobolev 1 g) (t : HardyCircle) :
    HasSum (fun j : ℤ => circleCoeff g j * fourier j t) (circleFourierRepresentative g t) := by
  have h := (circleFourierSeries_summable hg).hasSum.mapL
    (ContinuousMap.evalCLM (R := ℂ) t)
  exact h

theorem circleProduct_coeff (f g : CircleL2) (hg : CircleSobolev 1 g) (n : ℤ) :
    circleCoeff (circleProduct f g) n = ∑' j : ℤ, circleCoeff g j * circleCoeff f (n - j) := by
  let F : ℤ → HardyCircle → ℂ := fun j t =>
    circleCoeff g j * (fourier (j - n) t * f t)
  let B : ℤ → HardyCircle → ℝ := fun j t => ‖circleCoeff g j‖ * ‖f t‖
  have hf : Integrable (fun t => f t) hardyCircleMeasure :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
  have hF (j : ℤ) : Integrable (F j) hardyCircleMeasure := by
    exact (hf.fourier_smul (j - n)).const_mul (circleCoeff g j)
  have hbound (j : ℤ) : ∀ᵐ t ∂hardyCircleMeasure, ‖F j t‖ ≤ B j t := by
    filter_upwards with t
    simp only [F, B, norm_mul, fourier_apply, Circle.norm_coe, one_mul, le_refl]
  have hsum : ∀ᵐ t ∂hardyCircleMeasure, Summable (fun j => B j t) := by
    filter_upwards with t
    exact (circleSobolev_one_summable_coeff hg).mul_right ‖f t‖
  have hB : Integrable (fun t => ∑' j, B j t) hardyCircleMeasure := by
    simp only [B, tsum_mul_right]
    exact hf.norm.const_mul _
  have hpoint : ∀ᵐ t ∂hardyCircleMeasure,
      HasSum (fun j => F j t) (fourier (-n) t * (f t * circleFourierRepresentative g t)) := by
    filter_upwards with t
    have h := (circleFourierRepresentative_hasSum hg t).mul_left (fourier (-n) t * f t)
    convert h using 1
    · funext j
      change circleCoeff g j * (fourier (j - n) t * f t) =
        (fourier (-n) t * f t) * (circleCoeff g j * fourier j t)
      rw [show j - n = -n + j by ring, fourier_add]
      ring
    · ring
  have hi := hasSum_integral_of_dominated_convergence B (fun j => (hF j).aestronglyMeasurable)
    hbound hsum hB hpoint
  have hterm (j : ℤ) : (∫ t, F j t ∂hardyCircleMeasure) = circleCoeff g j * circleCoeff f (n - j) := by
    change (∫ t, circleCoeff g j * (fourier (j - n) t * f t) ∂hardyCircleMeasure) = _
    rw [integral_const_mul]
    simp only [circleCoeff_eq_fourierCoeff, fourierCoeff, smul_eq_mul, neg_sub]
  calc
    circleCoeff (circleProduct f g) n = fourierCoeff (fun t => f t * circleFourierRepresentative g t) n := by
      rw [circleCoeff_eq_fourierCoeff]
      exact congrFun (fourierCoeff_congr_ae (circleProduct_mem f g).coeFn_toLp) n
    _ = ∑' j : ℤ, ∫ t, F j t ∂hardyCircleMeasure := hi.tsum_eq.symm
    _ = _ := tsum_congr hterm

end Yau.NodeProofs.D06Aux
