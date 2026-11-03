import Yau.Proofs.V03FourierKernel

/-! Exact normalized integral of the integer circular difference kernel.
The value assigned at the diagonal has measure zero. -/

open scoped Topology ComplexConjugate
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [hT : Fact (0 < T)]

def differenceKernel (k : ℤ) (x : AddCircle T) : ℝ :=
  ‖fourier k x - 1‖ ^ 2 / ‖fourier 1 x - 1‖ ^ 2

theorem haarAddCircle_singleton_zero (x : AddCircle T) : haarAddCircle {x} = 0 := by
  have hv : (volume : Measure (AddCircle T)) {x} = 0 := by
    rw [← Metric.closedBall_zero (x := x), AddCircle.volume_closedBall]
    simp
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr hT.out))

theorem fourier_one_eq_one_iff (x : AddCircle T) : fourier 1 x = 1 ↔ x = 0 := by
  rw [fourier_one]
  constructor
  · intro hx
    apply AddCircle.injective_toCircle hT.out.ne'
    apply Subtype.ext
    simpa only [AddCircle.toCircle_zero, Circle.coe_one] using hx
  · intro hx
    simp [hx]

theorem differenceKernel_nat_eq {x : AddCircle T} (hx : x ≠ 0) (m : ℕ) :
    differenceKernel (m : ℤ) x = ‖geometricFourier m x‖ ^ 2 := by
  have hne : fourier 1 x - 1 ≠ 0 := sub_ne_zero.mpr
    (fun heq => hx ((fourier_one_eq_one_iff x).mp heq))
  have heq : geometricFourier m x = (fourier (m : ℤ) x - 1) / (fourier 1 x - 1) :=
    (eq_div_iff hne).mpr (geometricFourier_mul m x)
  rw [heq, norm_div, div_pow]
  rfl

theorem differenceKernel_nat_integral (m : ℕ) :
    (∫ x : AddCircle T, differenceKernel (m : ℤ) x ∂haarAddCircle) = (m : ℝ) := by
  calc
    (∫ x : AddCircle T, differenceKernel (m : ℤ) x ∂haarAddCircle) =
        ∫ x : AddCircle T, ‖geometricFourier m x‖ ^ 2 ∂haarAddCircle := by
      apply integral_congr_ae
      have hx : ∀ᵐ x : AddCircle T ∂haarAddCircle, x ≠ 0 := by
        simp [ae_iff, haarAddCircle_singleton_zero]
      exact hx.mono fun x hx => differenceKernel_nat_eq hx m
    _ = (m : ℝ) := geometricFourier_integral_norm_sq m

theorem differenceKernel_neg (k : ℤ) (x : AddCircle T) :
    differenceKernel (-k) x = differenceKernel k x := by
  unfold differenceKernel
  rw [fourier_neg]
  have hh : conj (fourier k x) - 1 = conj (fourier k x - 1) := by simp
  rw [hh, Complex.norm_conj]

theorem differenceKernel_integral (k : ℤ) :
    (∫ x : AddCircle T, differenceKernel k x ∂haarAddCircle) = |(k : ℝ)| := by
  cases k with
  | ofNat m =>
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) by positivity)] using
        differenceKernel_nat_integral (T := T) m
  | negSucc m =>
      have hk : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hk]
      simp_rw [differenceKernel_neg]
      simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (show (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) by positivity)] using
        differenceKernel_nat_integral (T := T) (m + 1)

theorem differenceKernel_eq_natAbs {x : AddCircle T} (hx : x ≠ 0) (k : ℤ) :
    differenceKernel k x = ‖geometricFourier k.natAbs x‖ ^ 2 := by
  cases k with
  | ofNat m => exact differenceKernel_nat_eq hx m
  | negSucc m =>
      have hk : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hk, differenceKernel_neg]
      exact differenceKernel_nat_eq hx (m + 1)

theorem differenceKernel_integrable (k : ℤ) :
    Integrable (differenceKernel (T := T) k) haarAddCircle := by
  have hc : Continuous (fun x : AddCircle T => ‖geometricFourier k.natAbs x‖ ^ 2) :=
    (geometricFourier k.natAbs).continuous.norm.pow 2
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).congr
  have hx : ∀ᵐ x : AddCircle T ∂haarAddCircle, x ≠ 0 := by
    simp [ae_iff, haarAddCircle_singleton_zero]
  exact hx.mono fun x hx => (differenceKernel_eq_natAbs hx k).symm

end Yau.Blueprint.V03Proof
