import Yau.Proofs.V04ScalarFejer
import Yau.Proofs.V03GagliardoCircle

/-! Parseval controls the full Fejer error, including attenuation of all
retained modes. Finiteness is required before taking real seminorm values. -/

open MeasureTheory AddCircle
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem scalarFejer_error_fourier_sq {u : AddCircle T → ℂ} (hu : Continuous u)
    (P : ℕ) (k : ℤ) :
    ‖fourierCoeff (fun x => scalarFejer u P x - u x) k‖ ^ 2 ≤
      ((P : ℝ) + 1)⁻¹ * (|(k : ℝ)| * ‖fourierCoeff u k‖ ^ 2) := by
  rw [scalarFejer_sub_fourierCoeff hu, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
  have hb : |fejerMultiplier P k - 1| ^ 2 ≤ |(k : ℝ)| / (P + 1) := by
    simpa only [abs_sub_comm] using fejerMultiplier_error_sq P k
  exact (mul_le_mul_of_nonneg_right hb (sq_nonneg _)).trans_eq (by ring)

theorem scalarFejer_error_ennreal {u : AddCircle T → ℂ} (hu : Continuous u) (P : ℕ) :
    ENNReal.ofReal (∫ x : AddCircle T, ‖scalarFejer u P x - u x‖ ^ 2 ∂haarAddCircle) ≤
      ENNReal.ofReal (((P : ℝ) + 1)⁻¹) * circleDirichlet u := by
  have hp := circle_parseval_continuous ((scalarFejer_continuous u P).sub hu)
  change HasSum (fun k : ℤ => ‖fourierCoeff (fun x => scalarFejer u P x - u x) k‖ ^ 2)
    (∫ x : AddCircle T, ‖scalarFejer u P x - u x‖ ^ 2 ∂haarAddCircle) at hp
  rw [← hp.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.summable]
  calc
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (((P : ℝ) + 1)⁻¹) *
        ENNReal.ofReal (|(k : ℝ)| * ‖fourierCoeff u k‖ ^ 2) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ((P : ℝ) + 1)⁻¹)]
      exact ENNReal.ofReal_le_ofReal (scalarFejer_error_fourier_sq hu P k)
    _ = _ := by rw [ENNReal.tsum_mul_left]; rfl

theorem scalarFejer_error_real {u : AddCircle T → ℂ} (hu : Continuous u)
    (hfinite : circleDirichlet u ≠ ⊤) (P : ℕ) :
    (∫ x : AddCircle T, ‖scalarFejer u P x - u x‖ ^ 2 ∂haarAddCircle) ≤
      (circleDirichlet u).toReal / (P + 1) := by
  have hR : ENNReal.ofReal (((P : ℝ) + 1)⁻¹) * circleDirichlet u ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  have hh := ENNReal.toReal_mono hR (scalarFejer_error_ennreal hu P)
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ ((P : ℝ) + 1)⁻¹)] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

end Yau.Blueprint.V04Proof
