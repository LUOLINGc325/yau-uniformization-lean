import Yau.Proofs.D06HardyKernel

/-! Sharp continuous Hardy evaluation and the normalized kernel right inverse. -/

open scoped ComplexConjugate lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyKernel_norm (z : ℂ) (hz : ‖z‖ < 1) (v : EuclideanSpace ℂ (Fin r)) :
    ‖hardyKernel z hz v‖ = (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ * ‖v‖ := by
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [← Real.sqrt_sq (norm_nonneg (hardyKernel z hz v)), hardyKernel_norm_sq,
    Real.sqrt_mul (inv_nonneg.mpr hq.le), Real.sqrt_inv, Real.sqrt_sq (norm_nonneg v)]

theorem hardyEval_norm_le (a : HardySeq r) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖hardyEval a z‖ ≤ (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ * ‖a‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hardyKernel z hz (hardyEval a z)) a
  rw [hardyKernel_reproduces, ← inner_self_re_eq_norm, inner_self_eq_norm_sq,
    hardyKernel_norm] at h
  by_cases he : ‖hardyEval a z‖ = 0
  · rw [he]
    positivity
  · have hp : 0 < ‖hardyEval a z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    apply le_of_mul_le_mul_left (a := ‖hardyEval a z‖) _ hp
    nlinarith only [h]

def hardyEvalLM (z : ℂ) (hz : ‖z‖ < 1) : HardySeq r →ₗ[ℂ] EuclideanSpace ℂ (Fin r) where
  toFun a := hardyEval a z
  map_add' a b := by
    ext j
    exact hardyEvalEntry_add a b j z hz
  map_smul' c a := by
    ext j
    exact hardyEvalEntry_smul c a j z

def hardyEvalCLM (z : ℂ) (hz : ‖z‖ < 1) : HardySeq r →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (hardyEvalLM z hz).mkContinuous (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹
    (fun a => hardyEval_norm_le a z hz)

theorem hardyEval_shift (a : HardySeq r) (z : ℂ) (hz : ‖z‖ < 1) :
    hardyEval (hardyShift a) z = z • hardyEval a z := by
  ext j
  exact hardyEvalEntry_shift a j z hz

theorem hardyEval_const (v : EuclideanSpace ℂ (Fin r)) (z : ℂ) :
    hardyEval (hardyConst v) z = v := by
  ext j
  change hardyEvalEntry (hardyConst v) j z = v j
  rw [hardyEvalEntry_eq_tsum]
  simp only [hardyConst_apply, mul_ite, mul_zero, tsum_ite_eq, pow_zero, one_mul]

def hardyNormalizedKernel (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) : HardySeq r :=
  ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) • hardyKernel z hz v

theorem hardyEval_kernel (z : ℂ) (hz : ‖z‖ < 1) (v : EuclideanSpace ℂ (Fin r)) :
    hardyEval (hardyKernel z hz v) z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ • v := by
  ext j
  change hardyEvalEntry (hardyKernel z hz v) j z = _
  rw [hardyEvalEntry_eq_tsum]
  have hn : ‖z * conj z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z]
  have hzc : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.mul_conj z
  calc
    (∑' n : ℕ, z ^ n * hardyKernel z hz v (n, j)) =
        (∑' n : ℕ, (z * conj z) ^ n) * v j := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      rw [hardyKernel_apply, mul_pow]
      ring
    _ = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ * v j := by
      rw [tsum_geometric_of_norm_lt_one hn, hzc]
      push_cast
      rfl

theorem hardyEval_normalizedKernel (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) : hardyEval (hardyNormalizedKernel z hz v) z = v := by
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  change hardyEvalCLM z hz (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) • hardyKernel z hz v) = v
  rw [map_smul]
  change ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) • hardyEval (hardyKernel z hz v) z = v
  rw [hardyEval_kernel, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hq.ne'), one_smul]

theorem hardyNormalizedKernel_norm (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) :
    ‖hardyNormalizedKernel z hz v‖ = Real.sqrt (1 - ‖z‖ ^ 2) * ‖v‖ := by
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.mpr hq
  rw [hardyNormalizedKernel, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq, hardyKernel_norm]
  have hc : (1 - ‖z‖ ^ 2) * (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ =
      Real.sqrt (1 - ‖z‖ ^ 2) := by
    conv_lhs => lhs; rw [← Real.sq_sqrt hq.le]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
  rw [← mul_assoc, hc]

end Yau.NodeProofs.D06Aux
