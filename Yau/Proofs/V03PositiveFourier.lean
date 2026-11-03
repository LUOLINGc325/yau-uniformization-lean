import Yau.Proofs.V03FourierFunctional
import Yau.Proofs.V03FourierKernel

/-! The positive Fourier projection is an actual uniformly convergent
continuous trace. Its coefficients are computed by the native Fourier functional. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def positiveFourierSum (b : ℕ → ℂ) : C(AddCircle T, ℂ) :=
  ∑' n : ℕ, b n • fourier (n : ℤ)

theorem positiveFourierSum_summable {b : ℕ → ℂ} (hb : Summable b) :
    Summable (fun n : ℕ => b n • (fourier (T := T) (n : ℤ))) := by
  apply Summable.of_norm_bounded hb.norm
  intro n
  simpa only [norm_smul, fourier_norm, mul_one] using (le_rfl : ‖b n‖ ≤ ‖b n‖)

theorem positiveFourierSum_coeff {b : ℕ → ℂ} (hb : Summable b) (k : ℤ) :
    fourierCoeff (positiveFourierSum (T := T) b) k =
      ∑' n : ℕ, b n * (Pi.single (n : ℤ) (1 : ℂ) : ℤ → ℂ) k := by
  have hs := positiveFourierSum_summable (T := T) hb
  calc
    fourierCoeff (positiveFourierSum (T := T) b) k =
        fourierCoeffFunctional k (∑' n : ℕ, b n • fourier (n : ℤ)) := rfl
    _ = ∑' n : ℕ, fourierCoeffFunctional k (b n • fourier (n : ℤ)) :=
      (fourierCoeffFunctional k).map_tsum hs
    _ = ∑' n : ℕ, b n * (Pi.single (n : ℤ) (1 : ℂ) : ℤ → ℂ) k := by
      apply tsum_congr
      intro n
      rw [map_smul, fourierCoeffFunctional_apply, fourierCoeff_fourier]
      rfl

theorem positiveFourierSum_coeff_nat {b : ℕ → ℂ} (hb : Summable b) (m : ℕ) :
    fourierCoeff (positiveFourierSum (T := T) b) (m : ℤ) = b m := by
  rw [positiveFourierSum_coeff hb]
  simp [Pi.single_apply, eq_comm]

theorem positiveFourierSum_coeff_negSucc {b : ℕ → ℂ} (hb : Summable b) (m : ℕ) :
    fourierCoeff (positiveFourierSum (T := T) b) (-((m + 1 : ℕ) : ℤ)) = 0 := by
  rw [positiveFourierSum_coeff hb]
  calc
    (∑' n : ℕ, b n * (Pi.single (n : ℤ) (1 : ℂ) : ℤ → ℂ) (-((m + 1 : ℕ) : ℤ))) =
        ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      simp only [Pi.single_apply]
      split_ifs with h
      · omega
      · simp
    _ = 0 := tsum_zero

theorem positiveFourierSum_apply {b : ℕ → ℂ} (hb : Summable b) (x : AddCircle T) :
    positiveFourierSum b x = ∑' n : ℕ, b n * (fourier 1 x) ^ n := by
  have hs := positiveFourierSum_summable (T := T) hb
  calc
    positiveFourierSum b x = (ContinuousMap.evalCLM ℂ x) (∑' n : ℕ, b n • fourier (n : ℤ)) := rfl
    _ = ∑' n : ℕ, (ContinuousMap.evalCLM ℂ x) (b n • fourier (n : ℤ)) :=
      (ContinuousMap.evalCLM ℂ x).map_tsum hs
    _ = ∑' n : ℕ, b n * (fourier 1 x) ^ n := by
      apply tsum_congr
      intro n
      simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul, fourier_nat_pow]

end Yau.Blueprint.V03Proof
