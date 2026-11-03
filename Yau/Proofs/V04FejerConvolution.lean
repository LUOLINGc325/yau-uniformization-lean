import Yau.Proofs.V04FejerKernel

/-! The actual finite Fejer polynomial is convolution with the same
nonnegative normalized kernel. Its uniform bound follows from actual
integrable continuous products. -/

open MeasureTheory AddCircle
open scoped Topology ComplexConjugate
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourier_neg_point (k : ℤ) (y : AddCircle T) : fourier k (-y) = fourier (-k) y := by
  simp only [fourier_apply, smul_neg, neg_smul]

theorem fejerKernel_convolution {u : AddCircle T → ℂ} (hu : Continuous u)
    (P : ℕ) (x : AddCircle T) :
    (∫ y : AddCircle T, (fejerKernel P (x - y) : ℂ) * u y ∂haarAddCircle) = scalarFejer u P x := by
  calc
    _ = ∫ y : AddCircle T, ∑ k ∈ Finset.Icc (-(P : ℤ)) P,
        ((fejerMultiplier P k : ℂ) * fourier k x) * (fourier (-k) y * u y) ∂haarAddCircle := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      dsimp only
      rw [fejerKernel_eq_fourier_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [sub_eq_add_neg, fourier_point_add, fourier_neg_point]
      ring
    _ = ∑ k ∈ Finset.Icc (-(P : ℤ)) P,
        ((fejerMultiplier P k : ℂ) * fourier k x) * fourierCoeff u k := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul]
        rfl
      · intro k _
        exact (continuous_const.mul ((fourier (-k)).continuous.mul hu)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    _ = _ := by
      unfold scalarFejer
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem fejerKernel_sub_integral (P : ℕ) (x : AddCircle T) :
    (∫ y : AddCircle T, fejerKernel P (x - y) ∂haarAddCircle) = 1 := by
  rw [integral_sub_left_eq_self (fejerKernel P) haarAddCircle x, fejerKernel_integral]

theorem scalarFejer_norm_le {u : AddCircle T → ℂ} (hu : Continuous u)
    {M : ℝ} (hM : ∀ y, ‖u y‖ ≤ M) (P : ℕ) (x : AddCircle T) :
    ‖scalarFejer u P x‖ ≤ M := by
  have hkc : Continuous (fun y => fejerKernel P (x - y)) :=
    (fejerKernel_continuous P).comp (continuous_const.sub continuous_id)
  have hi : Integrable (fun y => (fejerKernel P (x - y) : ℂ) * u y) haarAddCircle :=
    ((Complex.continuous_ofReal.comp hkc).mul hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound : Integrable (fun y => fejerKernel P (x - y) * M) haarAddCircle :=
    (hkc.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← fejerKernel_convolution hu]
  calc
    _ ≤ ∫ y : AddCircle T, ‖(fejerKernel P (x - y) : ℂ) * u y‖ ∂haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : AddCircle T, fejerKernel P (x - y) * M ∂haarAddCircle := by
      apply integral_mono hi.norm hbound
      intro y
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg P _)]
      exact mul_le_mul_of_nonneg_left (hM y) (fejerKernel_nonneg P _)
    _ = M := by rw [integral_mul_const, fejerKernel_sub_integral, one_mul]

end Yau.Blueprint.V04Proof
