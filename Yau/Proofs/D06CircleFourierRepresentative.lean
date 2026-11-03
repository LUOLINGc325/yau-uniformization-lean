import Yau.Proofs.D06SobolevSummability

/-! The absolutely summable Fourier series gives a continuous representative
of the same original L² function, with no replacement of its coefficients. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

def circleFourierRepresentative (f : CircleL2) : C(HardyCircle, ℂ) :=
  ∑' n : ℤ, circleCoeff f n • fourier n

theorem circleFourierSeries_summable {f : CircleL2} (hf : CircleSobolev 1 f) :
    Summable (fun n : ℤ => circleCoeff f n • (fourier n : C(HardyCircle, ℂ))) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using circleSobolev_one_summable_coeff hf

theorem circleFourierRepresentative_toLp {f : CircleL2} (hf : CircleSobolev 1 f) :
    ContinuousMap.toLp 2 hardyCircleMeasure ℂ (circleFourierRepresentative f) = f := by
  have hC := circleFourierSeries_summable hf
  have h := hC.hasSum.mapL (ContinuousMap.toLp 2 hardyCircleMeasure ℂ)
  have hF := hasSum_fourier_series_L2 f
  have heq : (fun n : ℤ => ContinuousMap.toLp 2 hardyCircleMeasure ℂ
      (circleCoeff f n • fourier n)) =
      fun n : ℤ => fourierCoeff f n • fourierLp 2 n := by
    funext n
    rw [map_smul, circleCoeff_eq_fourierCoeff]
  rw [heq] at h
  exact h.unique hF

theorem circleFourierRepresentative_ae {f : CircleL2} (hf : CircleSobolev 1 f) :
    (circleFourierRepresentative f : HardyCircle → ℂ) =ᵐ[hardyCircleMeasure] f := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) hardyCircleMeasure (circleFourierRepresentative f)
  rw [circleFourierRepresentative_toLp hf] at h
  exact h.symm

end Yau.NodeProofs.D06Aux
