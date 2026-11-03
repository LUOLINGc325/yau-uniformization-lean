import Yau.Proofs.D06HardyRotation

/-! The actual difference quotient of each nonnegative circle character
converges to its weak angular derivative multiplier i n. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem hardy_fourier_coe_exp (n : ℕ) (t : ℝ) :
    fourier (n : ℤ) (t : HardyCircle) = Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

def hardySmallAngle (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem hardySmallAngle_pos (n : ℕ) : 0 < hardySmallAngle n := by
  unfold hardySmallAngle
  positivity

theorem hardySmallAngle_tendsto : Tendsto hardySmallAngle atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall (fun n => (hardySmallAngle_pos n).ne')

def hardyFourierQuotient (n k : ℕ) : ℂ :=
  (hardySmallAngle k)⁻¹ • (fourier (n : ℤ) (hardySmallAngle k : HardyCircle) - 1)

theorem hardyFourierQuotient_tendsto (n : ℕ) :
    Tendsto (hardyFourierQuotient n) atTop (𝓝 ((n : ℂ) * Complex.I)) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (z * (n : ℂ) * Complex.I))
      ((n : ℂ) * Complex.I) 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).mul_const (n : ℂ)).mul_const Complex.I).cexp using 1 <;> simp
  have hr : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I))
      ((n : ℂ) * Complex.I) 0 := hd.comp_ofReal
  have hslope : Tendsto (fun t : ℝ => t⁻¹ •
      (Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) - 1)) (𝓝[≠] 0) (𝓝 ((n : ℂ) * Complex.I)) := by
    simpa only [zero_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using hr.tendsto_slope_zero
  have h := hslope.comp hardySmallAngle_tendsto
  apply h.congr'
  apply Eventually.of_forall
  intro k
  rw [hardyFourierQuotient, hardy_fourier_coe_exp]
  rfl

theorem hardyFourierQuotient_norm_sq_tendsto (n : ℕ) :
    Tendsto (fun k => ‖hardyFourierQuotient n k‖ ^ 2) atTop (𝓝 ((n : ℝ) ^ 2)) := by
  have h := (hardyFourierQuotient_tendsto n).norm.pow 2
  simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast] using h

end Yau.NodeProofs.D06Aux
