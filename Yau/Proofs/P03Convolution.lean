import Yau.Proofs.P03Wirtinger

open scoped Topology ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

def smoothBy (k : ComplexVector n → ℝ) (f : ComplexVector n → ℂ) :
    ComplexVector n → ℂ := k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

def cmulConv (f k : ComplexVector n → ℂ) : ComplexVector n → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k

theorem smoothBy_eq_cmulConv (k : ComplexVector n → ℝ) (f : ComplexVector n → ℂ) :
    smoothBy k f = cmulConv f (fun y => (k y : ℂ)) := by
  ext x
  rw [smoothBy, convolution_eq_swap, cmulConv, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  simp [ContinuousLinearMap.lsmul_apply, Complex.real_smul, mul_comm]

theorem cmulConv_contDiff {f k : ComplexVector n → ℂ}
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (cmulConv f k) :=
  hkc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hk

theorem cmulConv_derivative_integrable {f k : ComplexVector n → ℂ}
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (x v : ComplexVector n) :
    Integrable (fun y => f y * fderiv ℝ k (x - y) v) volume := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hcont : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  have hi := ((hkc.fderiv ℝ).convolutionExists_right (L.precompR (ComplexVector n))
    hf.locallyIntegrable hcont x).integrable
  have hev := (ContinuousLinearMap.apply ℝ ℂ v).integrable_comp hi
  exact hev

theorem cmulConv_fderiv_apply {f k : ComplexVector n → ℂ}
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (x v : ComplexVector n) :
    fderiv ℝ (cmulConv f k) x v = ∫ y, f y * fderiv ℝ k (x - y) v := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hd := hkc.hasFDerivAt_convolution_right L hf.locallyIntegrable
    (hk.of_le (by norm_num)) x
  rw [show fderiv ℝ (cmulConv f k) x =
      (f ⋆[L.precompR (ComplexVector n), volume] fderiv ℝ k) x from hd.fderiv]
  rw [convolution_precompR_apply L hf.locallyIntegrable (hkc.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v]
  rfl

/-- Differentiate the actual convolution and keep all derivative integrands
integrable before using the weak CR test identity. -/
theorem wirtBar_cmulConv {f k : ComplexVector n → ℂ}
    (hf : Integrable f volume) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (x v : ComplexVector n) :
    wirtBar (cmulConv f k) x v = ∫ y, f y * wirtBar k (x - y) v := by
  have hi := cmulConv_derivative_integrable hf hk hkc x v
  have hiI := cmulConv_derivative_integrable hf hk hkc x (Complex.I • v)
  rw [wirtBar, cmulConv_fderiv_apply hf hk hkc x v,
    cmulConv_fderiv_apply hf hk hkc x (Complex.I • v)]
  calc
    (1 / 2 : ℂ) * ((∫ y, f y * fderiv ℝ k (x - y) v) +
        Complex.I * ∫ y, f y * fderiv ℝ k (x - y) (Complex.I • v)) =
        (1 / 2 : ℂ) * ∫ y, f y * fderiv ℝ k (x - y) v +
          Complex.I * (f y * fderiv ℝ k (x - y) (Complex.I • v)) := by
      rw [integral_add hi (hiI.const_mul Complex.I), integral_const_mul]
    _ = ∫ y, (1 / 2 : ℂ) * (f y * fderiv ℝ k (x - y) v +
          Complex.I * (f y * fderiv ℝ k (x - y) (Complex.I • v))) :=
      (integral_const_mul _ _).symm
    _ = ∫ y, f y * wirtBar k (x - y) v := by
      apply integral_congr_ae
      filter_upwards with y
      unfold wirtBar
      ring

end Yau.NodeProofs.P03Aux
